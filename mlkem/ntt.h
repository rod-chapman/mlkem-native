/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef NTT_H
#define NTT_H

#include <stdint.h>
#include "cbmc.h"
#include "common.h"
#include "poly.h"
#include "reduce.h"

/* This declaration must match the one that appears in             */
/* zetas.i, which is autogenerated by script/autogenerate_files.py */
/* This declaration makes the mlkem_layer7_zetas table available   */
/* to other units. In particular, it is needed by                  */
/* poly_mulcache_computer() in poly.c                              */
#define mlkem_layer7_zetas MLKEM_NAMESPACE(mlkem_layer7_zetas)
extern const int16_t mlkem_layer7_zetas[64];

#define poly_ntt MLKEM_NAMESPACE(poly_ntt)
/*************************************************
 * Name:        poly_ntt
 *
 * Description: Computes negacyclic number-theoretic transform (NTT) of
 *              a polynomial in place.
 *
 *              The input is assumed to be in normal order and
 *              coefficient-wise bound by MLKEM_Q in absolute value.
 *
 *              The output polynomial is in bitreversed order, and
 *              coefficient-wise bound by NTT_BOUND in absolute value.
 *
 *              (NOTE: Sometimes the input to the NTT is actually smaller,
 *               which gives better bounds.)
 *
 * Arguments:   - poly *p: pointer to in/output polynomial
 **************************************************/
void poly_ntt(poly *r)
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  requires(array_abs_bound(r->coeffs, 0, MLKEM_N - 1, MLKEM_Q - 1))
  assigns(memory_slice(r, sizeof(poly)))
  ensures(array_abs_bound(r->coeffs, 0, MLKEM_N - 1, NTT_BOUND - 1))
);

#define poly_invntt_tomont MLKEM_NAMESPACE(poly_invntt_tomont)
/*************************************************
 * Name:        poly_invntt_tomont
 *
 * Description: Computes inverse of negacyclic number-theoretic transform (NTT)
 *              of a polynomial in place;
 *              inputs assumed to be in bitreversed order, output in normal
 *              order
 *
 *              The input is assumed to be in bitreversed order, and can
 *              have arbitrary coefficients in int16_t.
 *
 *              The output polynomial is in normal order, and
 *              coefficient-wise bound by INVNTT_BOUND in absolute value.
 *
 * Arguments:   - uint16_t *a: pointer to in/output polynomial
 **************************************************/
void poly_invntt_tomont(poly *r)
__contract__(
  requires(memory_no_alias(r, sizeof(poly)))
  assigns(memory_slice(r, sizeof(poly)))
  ensures(array_abs_bound(r->coeffs, 0, MLKEM_N - 1, INVNTT_BOUND - 1))
);

#endif
