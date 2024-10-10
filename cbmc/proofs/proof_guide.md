# CBMC Proof Guide and Cookbook for MLKEM-C

This doc acts as a guide to developing proofs of C code using CBMC. It concentrates
on the use of _contracts_ to achieve _unbounded_ and _modular_ proofs of type-safety
and correctness properties.

This document uses the abbreviated forms of the CBMC contracts defined by macros in the
cbmc.h h

## Installation and getting started

Installing CBMC can be a bit error prone. The main issue is to make sure that you have exactly the right version of CBMC, its supporting tools (cbmc-viewer and cbmc-starter-kit), and the underlying solvers all installed.

If your project has a "NIX" environment set up, then use that.

You'll often need the "latest" build of CBMC (to get the most recent bug-fixes) but those latest builds take a while to appear in package managers like APT or DPKG on Linux and Homebrew on macOS. In that case, you'll need to download the build that you need from [here](https://github.com/diffblue/cbmc/releases) BUT those packages do NOT include the supporting tools or solvers.

At the time of writing, you should make sure that you have:

CBMC 6.3.1 or higher [here](https://github.com/diffblue/cbmc/releases)

CBMC-Viewer 3.9 [here](https://github.com/model-checking/cbmc-viewer/releases)

cbmc-starter-kit 2.11[here](https://github.com/model-checking/cbmc-starter-kit)

Litani 1.29 - available via `brew install litani` on macOS, or standard package managers on Linux.

Z3 4.12.5 or better [here](https://github.com/Z3Prover/z3/releases)

Bitwuzla 0.5.0 [here](https://github.com/bitwuzla/bitwuzla/releases)

Kissat 3.1.1 [here](https://github.com/arminbiere/kissat/releases)

Cadical 2.0.0 [here](https://github.com/arminbiere/cadical/releases)

All of these tools must be on your PATH. Make sure they're all working (w.g. with `z3 --version` and so on) before you proceed.

## Running existing proofs

It's best to start by re-playing some existing proofs to see how they work. There are a few ways to do this. By "proof" in this context, we really mean "proof of a single C function, including proof of all the assertions, loop invariants, the post-condition and type-safety checks."

Typically, a project will have a on subdirectory per function, each of which contains a `Makefile` that configures the proof run for that function, and the "harness" function that CBMC needs.

Let's do a concrete example - the proof of the `poly_decompress` function from the PQCP AArch64-C-MLKEM repo [here](https://github.com/pq-code-package/mlkem-c-aarch64/tree/main/cbmc/proofs/poly_decompress)

If everything is set up, `cd` to that directory. You can run the proof to get output in HTML or plaintext.

### Single function proof, plaintext output

The Makefile contains a target called `result` that generates output of CBMC in plaintext only, and avoids the HTML reporting steps. The output appears in `logs/result.txt`, so

```
cd cbmc/proofs/poly_decompress
make result
less logs/result.txt
```

You should see a file that ends with something like:
```
** 0 of 225 failed (1 iterations)
VERIFICATION SUCCESSFUL
```

which is good news. If the run fails, then this file is the place to look to see what went wrong.

### Single function proof, HTML report

The default Makefile target generates HTML, so

```
cd cbmc/proofs/poly_decompress
make
```

generates report/html/index.html that can be opened in your Browser.

### Proving all functions

In CI, we want to prove all the functions. This is done from the "proofs" subdirectory, where there's a script called `run-cbmc-proofs.py`

To run that manually, it's just

```
cd cbmc/proofs
./run-cbmc-proofs.py --summarize -j8
```

where "8" is the number of processor cores that litani can use to run things in parallel. On a big EC2 instance, increase that to `-j32` or whatever.

That should get you something like this:

```
| Status  | Count |
|---------|-------|
| Success | 8     |

| Proof                          | Status  |
|--------------------------------|---------|
| poly_compress                  | Success |
| poly_decompress                | Success |
| scalar_compress_q_16           | Success |
| scalar_compress_q_32           | Success |
| scalar_decompress_q_16         | Success |
| scalar_decompress_q_32         | Success |
| scalar_signed_to_unsigned_q_16 | Success |

```
which looks good.

This what you should run to check that everything is OK before you push new code changes or an entirely new proof.

## Common Proof Patterns

### Assignments, initialization, and variables

1. Declare variables with as small a scope as possible. Declare and initialize a variable close to where it is needed.

2. Always make variables `const` if they are initialized and then read-only from then on.

3. Initialize arrays and structs at the point of declaration using an initializing expression. Don't use a sequence of element-by-element assignments.  For example.

DON'T WRITE:
```
  int a[3];
  a[0] = 1;
  a[1] = 2;
  a[2] = 3;
```

DO WRITE:
```
int a[3] = { 1, 2, 3 };
```

and so on.

### Loops (general advice)

1. A function should contain at most one outermost loop statement. If the function you're trying to prove has more than one outermost loop, then re-factor it into two or more functions.

2. The one outermost loop statement should be _final_ statement before the function returns. Don't have complicated code _after_ the loop body.

### For loops

The most common, and easiest, patten is a "for" loop that has a counter starting at 0, and counting up to some upper bound, like this:

```
for (int i = 0; i < C; i++) {
    S;
}
```
Notes:
1. It is good practice to declare the counter variable locally, within the scope of the loop.
2. The counter variable should be a constant within the loop body. In the example above, DO NOT modify `i` in the body of the loop.
3. "int" is the best type for the counter variable. "unsigned" integer types complicate matters with their modulo N semantics. Avoid "size_t" since its large range (possibly unsigned 64 bit) can slow proofs down.

CBMC requires basic assigns, loop-invariant, and decreases contracts _in exactly that order_. Note that the contracts appear _before_ the opening `{` of the loop body, so we also need to tell `clang-format` NOT to reformat these lines. The basic pattern is thus:

```
for (int i = 0; i < C; i++)
// clang-format off
ASSIGNS(i) // plus whatever else S does
INVARIANT(i >= 0)
INVARIANT(i <= C)
DECREASES(C - i)
// clang-format on
{
    S;
}
```

The `i <= C` in the invariant is NOT a typo. CBMC places the invariant just _after_ the loop counter has been incremented, but just _before_ the loop exit test, so it is possible for `i == C` at the invariant on the final iteration of the loop.

### Iterating over an array for a for loop

A common pattern - doing something to every element of an array. An example would be setting every element of a byte-array to 0x00 given a pointer to the first element and a length. Initially, we want to prove type safety of this function, so we won't even bother with a post-condition. The function specification might look like this:

```
void zero_array_ts (uint8_t *dst, int len)
REQUIRES(IS_FRESH(dst, len))
ASSIGNS(OBJECT_WHOLE(dst));
```

The body:

```
void zero_array_ts (uint8_t *dst, int len)
{
    for (int i = 0; i < len; i++)
    // clang-format off
    ASSIGNS(i, OBJECT_WHOLE(dst))
    INVARIANT(i >= 0 && i <= len)
    DECREASES(len - i)
    // clang-format on
    {
        dst[i] = 0;
    }
}
```
The only real "type safety proofs" here are that
1. dst is pointing at exactly "len" bytes - this is given by the IS_FRESH() part of the precondition.
2. The assignment to `dst[i]` does not have a buffer overflow. This requires a proof that `i >= 0 && i < len` which is trivially discharged given the loop invariant AND the fact that the loop _hasn't_ terminated (so we know `i < len` too).

### Correctness proof of zero_array

We can go further, and prove the correctness of that function by adding a post-condition, and extending the loop invariant. This introduces more important patterns.

The function specification is extended:

```
void zero_array_correct (uint8_t *dst, int len)
REQUIRES(IS_FRESH(dst, len))
ASSIGNS(OBJECT_WHOLE(dst))
ENSURES(FORALL { int k; (0 <= k && k < len) ==> dst[k] == 0 });
```

Note the required order of the contracts is always REQUIRES, ASSIGNS, ENSURES.

The body is the same, but with a stronger loop invariant. The invariant says that "after j loop iterations, we've zeroed the first j elements of the array", so:

```
void zero_array_correct (uint8_t *dst, int len)
{
    for (int i = 0; i < len; i++)
    // clang-format off
    ASSIGNS(i, OBJECT_WHOLE(dst))
    INVARIANT(i >= 0 && i <= len)
    INVARIANT(FORALL { int j; (0 <= j && j <= i - 1) ==> dst[j] == 0 } )
    DECREASES(len - i)
    // clang-format on
    {
        dst[i] = 0;
    }
}
```

Rules of thumb:
1. Don't overload your program variables with quantified variables inside your FORALL contracts. It get confusing if you do.
2. The type of the quanitified variable is _signed_ "int". This is important.
3. The path in the program from the loop-invariant, through the final loop exit test, to the implicit `return` statement is "nothing" or a "null statement". We need to prove that (on the final iteration), the loop invariant AND the loop exit condidtion imply the post-condition. Imagine having to do that if there's some really complex code _after_ the loop body.

This pattern also brings up another important trick - the use of "null ranges" in FORALL expressions. Consider the loop invariant above. We need to prove that it's true on the first entry to the loop (i.e. when i == 0).

Substituting i == 0 into there, we need to prove

```
FORALL { int j; (0 <= j && j <= -1) ==> dst[j] == 0 }
```

but how can j be both larger-than-or-equal-to 0 AND less-than-or-equal-to -1 at the same time? Answer: it can't! So.. the left hand side of the quantified predicate is False, so it reduces to:

```
FORALL { int j; false ==> dst[j] == 0 }
```

The `==>` is a logical implication, and we know that `False ==> ANYTHING` is True, so all is well.

This comes up a lot. You often end up reasoning about such "slices" of arrays, where one or more of the slices has "null range" at either the loop entry, or at the loop exit point, and therefore that particular quantifier "disappears". Several examples of this trick can be found on the MLKEM codebase.

This also explains why we prefer to use _signed_ integers for loop counters and quantified variables - to allow "0 - 1" to evaluate to -1.  If you use an unsigned type, then "0 - 1" evaluated to something like UINT_MAX, and all hell breaks loose.

## Invariant && loop-exit ==> post-condition

Another important sanity check. If there are no statements following the loop body, then the loop invariant AND the loop exit condition should imply the post-condition. For the example above, we need to prove:

```
// Loop invariant
(i >= 0 &&
 i <= len &&
 (FORALL { int j; (0 <= j && j <= i - 1) ==> dst[j] == 0 } )
&&
// Loop exit condition must be TRUE, so
i == len)

  ==>

// Post-condition
FORALL { int k; (0 <= k && k < len) ==> dst[k] == 0 }
```

The loop exit condition means that we can just replace `i` with `len` in the hypotheses, to get:

```
len >= 0 &&
len <= len &&
(FORALL { int j; (0 <= j && j <= len - 1) ==> dst[j] == 0 } )
  ==>
FORALL { int k; (0 <= k && k < len) ==> dst[k] == 0 }
```

`j <= len - 1` can be simplified to `j < len` so that simplifies to:

```
FORALL { int j; (0 <= j && j < len) ==> dst[j] == 0 }
  ==>
FORALL { int k; (0 <= k && k < len) ==> dst[k] == 0 }
```

which is True.
