/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/***************************************************
 * Basic replacements for __CPROVER_XXX contracts
 ***************************************************/

#include "common.h"

#ifndef CBMC

#define STATIC_INLINE_TESTABLE static INLINE
#define STATIC_NO_INLINE_TESTABLE static NO_INLINE
#define STATIC_TESTABLE static

#define __contract__(x)
#define __loop__(x)
#define cassert(x, y)

#else /* CBMC _is_ defined, therefore we're doing proof */

/* expose certain procedures to CBMC proofs that are static otherwise */
#define STATIC_TESTABLE
#define STATIC_INLINE_TESTABLE
#define STATIC_NO_INLINE_TESTABLE

#define __contract__(x) x
#define __loop__(x) x

/* https://diffblue.github.io/cbmc/contracts-assigns.html */
#define assigns(...) __CPROVER_assigns(__VA_ARGS__)

/* https://diffblue.github.io/cbmc/contracts-requires-ensures.html */
#define requires(...) __CPROVER_requires(__VA_ARGS__)
#define ensures(...) __CPROVER_ensures(__VA_ARGS__)
/* https://diffblue.github.io/cbmc/contracts-loops.html */
#define invariant(...) __CPROVER_loop_invariant(__VA_ARGS__)
#define decreases(...) __CPROVER_decreases(__VA_ARGS__)
/* cassert to avoid confusion with in-built assert */
#define cassert(...) __CPROVER_assert(__VA_ARGS__)
#define assume(...) __CPROVER_assume(__VA_ARGS__)

/***************************************************
 * Macros for "expression" forms that may appear
 * _inside_ top-level contracts.
 ***************************************************/

/*
 * function return value - useful inside ensures
 * https://diffblue.github.io/cbmc/contracts-functions.html
 */
#define return_value (__CPROVER_return_value)

/*
 * assigns l-value targets
 * https://diffblue.github.io/cbmc/contracts-assigns.html
 */
#define object_whole(...) __CPROVER_object_whole(__VA_ARGS__)
#define memory_slice(...) __CPROVER_object_upto(__VA_ARGS__)
#define same_object(...) __CPROVER_same_object(__VA_ARGS__)

/*
 * Pointer-related predicates
 * https://diffblue.github.io/cbmc/contracts-memory-predicates.html
 */
#define memory_no_alias(...) __CPROVER_is_fresh(__VA_ARGS__)
#define readable(...) __CPROVER_r_ok(__VA_ARGS__)
#define writeable(...) __CPROVER_w_ok(__VA_ARGS__)

/*
 * History variables
 * https://diffblue.github.io/cbmc/contracts-history-variables.html
 */
#define old(...) __CPROVER_old(__VA_ARGS__)
#define loop_entry(...) __CPROVER_loop_entry(__VA_ARGS__)

/*
 * Quantifiers
 * Note that the range on qvar is _inclusive_ between qvar_lb .. qvar_ub
 * https://diffblue.github.io/cbmc/contracts-quantifiers.html
 */

/*
 * Prevent clang-format from corrupting CBMC's special ==> operator
 */
/* clang-format off */
#define forall(type, qvar, qvar_lb, qvar_ub, predicate)           \
  __CPROVER_forall                                                \
  {                                                               \
    type qvar;                                                    \
    ((qvar_lb) <= (qvar) && (qvar) <= (qvar_ub)) ==> (predicate)  \
  }

#define EXISTS(type, qvar, qvar_lb, qvar_ub, predicate)         \
  __CPROVER_exists                                              \
  {                                                             \
    type qvar;                                                  \
    ((qvar_lb) <= (qvar) && (qvar) <= (qvar_ub)) && (predicate) \
  }
/* clang-format on */

/***************************************************
 * Convenience macros for common contract patterns
 ***************************************************/

/*
 * Boolean-value predidate that asserts that "all values of array_var are in
 * range value_lb .. value_ub (inclusive)"
 * Example:
 *  array_bound(a->coeffs, 0, MLKEM_N-1, -(MLKEM_Q - 1), MLKEM_Q - 1)
 * expands to
 *  __CPROVER_forall { int k; (0 <= k && k <= MLKEM_N-1) ==> ( (-(MLKEM_Q -
 *  1) <= a->coeffs[k]) && (a->coeffs[k] <= (MLKEM_Q - 1))) }
 */

/*
 * Prevent clang-format from corrupting CBMC's special ==> operator
 */
/* clang-format off */
#define CBMC_CONCAT_(left, right) left##right
#define CBMC_CONCAT(left, right) CBMC_CONCAT_(left, right)

#define array_bound_core(indextype, qvar, qvar_lb, qvar_ub, array_var, \
                         value_lb, value_ub)                           \
  __CPROVER_forall                                                     \
  {                                                                    \
    indextype qvar;                                                    \
    ((qvar_lb) <= (qvar) && (qvar) <= (qvar_ub)) ==>                   \
        (((value_lb) <= (array_var[(qvar)])) &&                        \
        ((array_var[(qvar)]) <= (value_ub)))                           \
  }

#define array_bound(array_var, qvar_lb, qvar_ub, value_lb, value_ub) \
  array_bound_core(int, CBMC_CONCAT(_cbmc_idx, __LINE__), (qvar_lb), \
                   (qvar_ub), (array_var), (value_lb), (value_ub))


/* Wrapper around array_bound operating on absolute values */
#define array_abs_bound(arr, lb, ub, k) \
  array_bound((arr), (lb), (ub), (-(k)), (k))
/* clang-format on */

#endif
