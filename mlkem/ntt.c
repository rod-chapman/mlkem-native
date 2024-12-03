/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "ntt.h"
#include <stdint.h>
#include "params.h"
#include "reduce.h"

#include "arith_native.h"
#include "debug/debug.h"

#if !defined(MLKEM_USE_NATIVE_NTT)

#define NTT_BOUND1 (MLKEM_Q - 1)
#define NTT_BOUND4 (4 * MLKEM_Q - 1)
#define NTT_BOUND6 (6 * MLKEM_Q - 1)
#define NTT_BOUND7 (7 * MLKEM_Q - 1)
#define NTT_BOUND8 (8 * MLKEM_Q - 1)

typedef int16_t pc[MLKEM_N];

/* nb stucture this as 1 32-bit integer and 2 16-bit integers            */
/* so the whole thing can be accessed with a single 64-bit aligned read. */
typedef struct
{
  int32_t parent_zeta;
  int16_t left_child_zeta;
  int16_t right_child_zeta;
} zeta_subtree_entry;

const zeta_subtree_entry layer45_zetas[8] = {
    {-171, 573, -1325},  {622, 264, 383},    {1577, -829, 1458},
    {182, -1602, -130},  {962, -681, 1017},  {-1202, 732, 608},
    {-1474, -1542, 411}, {1468, -205, -1571}};

const int16_t layer6_zetas[32] = {
    1223, 652,   -552,  1015, -1293, 1491, -282, -1544, 516, -8,    -320,
    -666, -1618, -1162, 126,  1469,  -853, -90,  -271,  830, 107,   -1421,
    -247, -951,  -398,  961,  -1508, -725, 448,  -1065, 677, -1275,
};

const int16_t layer7_zetas[64] = {
    /* Layer 7 - index 64 .. 127 */
    -1103, 430,  555,   843,   -1251, 871,   1550,  105,   422,   587,  177,
    -235,  -291, -460,  1574,  1653,  -246,  778,   1159,  -147,  -777, 1483,
    -602,  1119, -1590, 644,   -872,  349,   418,   329,   -156,  -75,  817,
    1097,  603,  610,   1322,  -1285, -1465, 384,   -1215, -136,  1218, -1335,
    -874,  220,  -1187, -1659, -1185, -1530, -1278, 794,   -1510, -854, -870,
    478,   -108, -308,  996,   991,   958,   -1460, 1522,  1628};


STATIC_INLINE_TESTABLE void ntt_layer123(pc r)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  requires(array_abs_bound(r, 0, MLKEM_N - 1, NTT_BOUND1))
  assigns(memory_slice(r, sizeof(pc)))
  ensures(array_abs_bound(r, 0, MLKEM_N - 1, NTT_BOUND4)))
{
  const int32_t z1 = -758;
  const int32_t z2 = -359;
  const int32_t z3 = -1517;
  const int32_t z4 = 1493;
  const int32_t z5 = 1422;
  const int32_t z6 = 287;
  const int32_t z7 = 202;

  int j;
  for (j = 0; j < 32; j++)
  __loop__(
    /* A single iteration of this loop updates 8 coefficients 3 times each,
     * meaning their bound jumps from NTT_BOUND1 to NTT_BOUND4. Other (as yet
     * untouched) coefficients remain bounded by NTT_BOUND1. When this loop
     * terminates with j == 32, ALL the coefficients have been updated
     * exactly 3 times, so ALL are bounded by NTT_BOUND4, which establishes
     * the post-condition */
    invariant(0 <= j && j <= 32)
    invariant(array_abs_bound(r,       0,   j - 1, NTT_BOUND4))
    invariant(array_abs_bound(r,       j,      31, NTT_BOUND1))
    invariant(array_abs_bound(r,      32,  j + 31, NTT_BOUND4))
    invariant(array_abs_bound(r,  j + 32,      63, NTT_BOUND1))
    invariant(array_abs_bound(r,      64,  j + 63, NTT_BOUND4))
    invariant(array_abs_bound(r,  j + 64,      95, NTT_BOUND1))
    invariant(array_abs_bound(r,      96,  j + 95, NTT_BOUND4))
    invariant(array_abs_bound(r,  j + 96,     127, NTT_BOUND1))
    invariant(array_abs_bound(r,     128, j + 127, NTT_BOUND4))
    invariant(array_abs_bound(r, j + 128,     159, NTT_BOUND1))
    invariant(array_abs_bound(r,     160, j + 159, NTT_BOUND4))
    invariant(array_abs_bound(r, j + 160,     191, NTT_BOUND1))
    invariant(array_abs_bound(r,     192, j + 191, NTT_BOUND4))
    invariant(array_abs_bound(r, j + 192,     223, NTT_BOUND1))
    invariant(array_abs_bound(r,     224, j + 223, NTT_BOUND4))
    invariant(array_abs_bound(r, j + 224,     255, NTT_BOUND1)))
  {
    const int ci1 = j + 0;
    const int ci2 = j + 32;
    const int ci3 = j + 64;
    const int ci4 = j + 96;
    const int ci5 = j + 128;
    const int ci6 = j + 160;
    const int ci7 = j + 192;
    const int ci8 = j + 224;
    int16_t t1, t2;

    /* Layer 1 */
    t1 = fqmul(r[ci5], z1);
    t2 = r[ci1];
    r[ci5] = t2 - t1;
    r[ci1] = t2 + t1;

    t1 = fqmul(r[ci7], z1);
    t2 = r[ci3];
    r[ci7] = t2 - t1;
    r[ci3] = t2 + t1;

    t1 = fqmul(r[ci6], z1);
    t2 = r[ci2];
    r[ci6] = t2 - t1;
    r[ci2] = t2 + t1;

    t1 = fqmul(r[ci8], z1);
    t2 = r[ci4];
    r[ci8] = t2 - t1;
    r[ci4] = t2 + t1;

    /* Layer 2 */
    t1 = fqmul(r[ci3], z2);
    t2 = r[ci1];
    r[ci3] = t2 - t1;
    r[ci1] = t2 + t1;

    t1 = fqmul(r[ci7], z3);
    t2 = r[ci5];
    r[ci7] = t2 - t1;
    r[ci5] = t2 + t1;

    t1 = fqmul(r[ci4], z2);
    t2 = r[ci2];
    r[ci4] = t2 - t1;
    r[ci2] = t2 + t1;

    t1 = fqmul(r[ci8], z3);
    t2 = r[ci6];
    r[ci8] = t2 - t1;
    r[ci6] = t2 + t1;

    /* Layer 3 */
    t1 = fqmul(r[ci2], z4);
    t2 = r[ci1];
    r[ci2] = t2 - t1;
    r[ci1] = t2 + t1;

    t1 = fqmul(r[ci4], z5);
    t2 = r[ci3];
    r[ci4] = t2 - t1;
    r[ci3] = t2 + t1;

    t1 = fqmul(r[ci6], z6);
    t2 = r[ci5];
    r[ci6] = t2 - t1;
    r[ci5] = t2 + t1;

    t1 = fqmul(r[ci8], z7);
    t2 = r[ci7];
    r[ci8] = t2 - t1;
    r[ci7] = t2 + t1;
  }
}

STATIC_INLINE_TESTABLE void ntt_layer45_slice(pc r, int zeta_subtree_index,
                                              int start)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  requires(zeta_subtree_index >= 0)
  requires(zeta_subtree_index <= 7)
  requires(start >= 0)
  requires(start <= 224)
  requires(array_abs_bound(r,          0,    start -  1, NTT_BOUND6))
  requires(array_abs_bound(r,      start, (MLKEM_N - 1), NTT_BOUND4))
  assigns(memory_slice(r, sizeof(pc)))
  ensures (array_abs_bound(r,          0,    start + 31, NTT_BOUND6))
  ensures (array_abs_bound(r, start + 32, (MLKEM_N - 1), NTT_BOUND4)))
{
  const zeta_subtree_entry zeds = layer45_zetas[zeta_subtree_index];
  const int32_t z1 = zeds.parent_zeta;
  const int32_t z2 = (int32_t)zeds.left_child_zeta;
  const int32_t z3 = (int32_t)zeds.right_child_zeta;


  int j;
  for (j = 0; j < 8; j++)
  __loop__(
    invariant(j >= 0 && j <= 8)
    invariant(array_abs_bound(r,              0,     start -  1, NTT_BOUND6))
    invariant(array_abs_bound(r,      start + 0,  start + j - 1, NTT_BOUND6))
    invariant(array_abs_bound(r,      start + j,      start + 7, NTT_BOUND4))
    invariant(array_abs_bound(r,      start + 8,  start + j + 7, NTT_BOUND6))
    invariant(array_abs_bound(r,  start + j + 8,     start + 15, NTT_BOUND4))
    invariant(array_abs_bound(r,     start + 16, start + j + 15, NTT_BOUND6))
    invariant(array_abs_bound(r, start + j + 16,     start + 23, NTT_BOUND4))
    invariant(array_abs_bound(r,     start + 24, start + j + 23, NTT_BOUND6))
    invariant(array_abs_bound(r, start + j + 24,  (MLKEM_N - 1), NTT_BOUND4)))
  {
    const int ci1 = j + start;
    const int ci2 = ci1 + 8;
    const int ci3 = ci1 + 16;
    const int ci4 = ci1 + 24;
    int16_t t1, t2;

    /* Layer 4 */
    t1 = fqmul(r[ci3], z1);
    t2 = r[ci1];
    r[ci3] = t2 - t1;
    r[ci1] = t2 + t1;

    t1 = fqmul(r[ci4], z1);
    t2 = r[ci2];
    r[ci4] = t2 - t1;
    r[ci2] = t2 + t1;

    /* Layer 5 */
    t1 = fqmul(r[ci2], z2);
    t2 = r[ci1];
    r[ci2] = t2 - t1;
    r[ci1] = t2 + t1;

    t1 = fqmul(r[ci4], z3);
    t2 = r[ci3];
    r[ci4] = t2 - t1;
    r[ci3] = t2 + t1;
  }
}


STATIC_INLINE_TESTABLE void ntt_layer45(pc r)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  requires(array_abs_bound(r, 0, MLKEM_N - 1, NTT_BOUND4))
  assigns(memory_slice(r, sizeof(pc)))
  ensures(array_abs_bound(r, 0, MLKEM_N - 1, NTT_BOUND6)))
{
  ntt_layer45_slice(r, 0, 0);
  ntt_layer45_slice(r, 1, 32);
  ntt_layer45_slice(r, 2, 64);
  ntt_layer45_slice(r, 3, 96);
  ntt_layer45_slice(r, 4, 128);
  ntt_layer45_slice(r, 5, 160);
  ntt_layer45_slice(r, 6, 192);
  ntt_layer45_slice(r, 7, 224);
}



STATIC_INLINE_TESTABLE void ntt_layer6_slice(pc r, const int zeta_index,
                                             const int start)
{
  const int16_t zeta = layer6_zetas[zeta_index];

  int j;
  for (j = 0; j < 4; j++)
  {
    const int ci1 = j + start;
    const int ci2 = ci1 + 4;
    const int16_t t = fqmul(zeta, r[ci2]);
    const int16_t t2 = r[ci1];
    r[ci2] = t2 - t;
    r[ci1] = t2 + t;
  }
}

STATIC_INLINE_TESTABLE void ntt_layer6(pc r)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  requires(array_abs_bound(r, 0, MLKEM_N - 1, NTT_BOUND6))
  assigns(memory_slice(r, sizeof(pc)))
  ensures(array_abs_bound(r, 0, MLKEM_N - 1, NTT_BOUND7)))
{
  int j;
  for (j = 0; j < 32; j++)
  {
    ntt_layer6_slice(r, j, j * 8);
  }
}

STATIC_INLINE_TESTABLE void ntt_layer7_slice(pc r, int zeta_index, int start)
{
  const int32_t zeta = (int32_t)layer7_zetas[zeta_index];
  /* Coefficient indexes 0 through 3 */
  const unsigned int ci0 = start;
  const unsigned int ci1 = ci0 + 1;
  const unsigned int ci2 = ci0 + 2;
  const unsigned int ci3 = ci0 + 3;

  /* Read and write coefficients in natural order of
   * increasing memory location
   */
  const int16_t c0 = r[ci0];
  const int16_t c1 = r[ci1];
  const int16_t c2 = r[ci2];
  const int16_t c3 = r[ci3];

  const int16_t zc2 = fqmul(zeta, c2);
  const int16_t zc3 = fqmul(zeta, c3);

  r[ci0] = c0 + zc2;
  r[ci1] = c1 + zc3;
  r[ci2] = c0 - zc2;
  r[ci3] = c1 - zc3;
}

STATIC_INLINE_TESTABLE void ntt_layer7(pc r)
__contract__(
  requires(memory_no_alias(r, sizeof(pc)))
  requires(array_abs_bound(r, 0, MLKEM_N - 1, NTT_BOUND7))
  assigns(memory_slice(r, sizeof(pc)))
  ensures(array_abs_bound(r, 0, MLKEM_N - 1, NTT_BOUND8)))
{
  int j;
  for (j = 0; j < 64; j++)
  {
    ntt_layer7_slice(r, j, j * 4);
  }
}


void poly_ntt(poly *p)
{
  int16_t *r;
  POLY_BOUND_MSG(p, MLKEM_Q, "ref ntt input");
  r = p->coeffs;

  ntt_layer123(r);
  ntt_layer45(r);
  ntt_layer6(r);
  ntt_layer7(r);

  /* Check the stronger bound */
  POLY_BOUND_MSG(p, NTT_BOUND, "ref ntt output");
}



#else  /* MLKEM_USE_NATIVE_NTT */

/* Check that bound for native NTT implies contractual bound */
STATIC_ASSERT(NTT_BOUND_NATIVE <= NTT_BOUND, invntt_bound)

void poly_ntt(poly *p)
{
  POLY_BOUND_MSG(p, MLKEM_Q, "native ntt input");
  ntt_native(p);
  POLY_BOUND_MSG(p, NTT_BOUND_NATIVE, "native ntt output");
}
#endif /* MLKEM_USE_NATIVE_NTT */



#if !defined(MLKEM_USE_NATIVE_INTT)

/* Check that bound for reference invNTT implies contractual bound */
#define INVNTT_BOUND_REF (3 * MLKEM_Q / 4)
STATIC_ASSERT(INVNTT_BOUND_REF <= INVNTT_BOUND, invntt_bound)

/* Compute one layer of inverse NTT */
STATIC_TESTABLE
void invntt_layer(int16_t *r, int len, int layer)
__contract__(
  requires(memory_no_alias(r, sizeof(int16_t) * MLKEM_N))
  requires(2 <= len && len <= 128 && 1 <= layer && layer <= 7)
  requires(len == (1 << (8 - layer)))
  requires(array_abs_bound(r, 0, MLKEM_N - 1, MLKEM_Q))
  assigns(memory_slice(r, sizeof(int16_t) * MLKEM_N))
  ensures(array_abs_bound(r, 0, MLKEM_N - 1, MLKEM_Q)))
{
  int start, k;
  /* `layer` is a ghost variable used only in the specification */
  ((void)layer);
  k = MLKEM_N / len - 1;
  for (start = 0; start < MLKEM_N; start += 2 * len)
  __loop__(
    invariant(array_abs_bound(r, 0, MLKEM_N - 1, MLKEM_Q))
    invariant(0 <= start && start <= MLKEM_N && 0 <= k && k <= 127)
    /* Normalised form of k == MLKEM_N / len - 1 - start / (2 * len) */
    invariant(2 * len * k + start == 2 * MLKEM_N - 2 * len))
  {
    int j;
    int16_t zeta = zetas[k--];
    for (j = start; j < start + len; j++)
    __loop__(
      invariant(start <= j && j <= start + len)
      invariant(0 <= start && start <= MLKEM_N && 0 <= k && k <= 127)
      invariant(array_abs_bound(r, 0, MLKEM_N - 1, MLKEM_Q)))
    {
      int16_t t = r[j];
      r[j] = barrett_reduce(t + r[j + len]);
      r[j + len] = r[j + len] - t;
      r[j + len] = fqmul(r[j + len], zeta);
    }
  }
}

void poly_invntt_tomont(poly *p)
{
  /*
   * Scale input polynomial to account for Montgomery factor
   * and NTT twist. This also brings coefficients down to
   * absolute value < MLKEM_Q.
   */
  int j, len, layer;
  const int16_t f = 1441;
  int16_t *r = p->coeffs;

  for (j = 0; j < MLKEM_N; j++)
  __loop__(
    invariant(0 <= j && j <= MLKEM_N)
    invariant(array_abs_bound(r, 0, j - 1, MLKEM_Q)))
  {
    r[j] = fqmul(r[j], f);
  }

  /* Run the invNTT layers */
  for (len = 2, layer = 7; len <= 128; len <<= 1, layer--)
  __loop__(
    invariant(2 <= len && len <= 256 && 0 <= layer && layer <= 7 && len == (1 << (8 - layer)))
    invariant(array_abs_bound(r, 0, MLKEM_N - 1, MLKEM_Q)))
  {
    invntt_layer(p->coeffs, len, layer);
  }

  POLY_BOUND_MSG(p, INVNTT_BOUND_REF, "ref intt output");
}
#else  /* MLKEM_USE_NATIVE_INTT */

/* Check that bound for native invNTT implies contractual bound */
STATIC_ASSERT(INVNTT_BOUND_NATIVE <= INVNTT_BOUND, invntt_bound)

void poly_invntt_tomont(poly *p)
{
  intt_native(p);
  POLY_BOUND_MSG(p, INVNTT_BOUND_NATIVE, "native intt output");
}
#endif /* MLKEM_USE_NATIVE_INTT */

void basemul_cached(int16_t r[2], const int16_t a[2], const int16_t b[2],
                    int16_t b_cached)
{
  int32_t t0, t1;

  BOUND(a, 2, 4096, "basemul input bound");

  t0 = (int32_t)a[1] * b_cached;
  t0 += (int32_t)a[0] * b[0];
  t1 = (int32_t)a[0] * b[1];
  t1 += (int32_t)a[1] * b[0];

  /* |ti| < 2 * q * 2^15 */
  r[0] = montgomery_reduce(t0);
  r[1] = montgomery_reduce(t1);

  BOUND(r, 2, 2 * MLKEM_Q, "basemul output bound");
}
