// SPDX-License-Identifier: Apache-2.0
#ifndef PARAMS_H
#define PARAMS_H

#include "common.h"
#include "cpucap.h"

#ifndef MLKEM_K
#define MLKEM_K 3 /* Change this for different security strengths */
#endif

/* Don't change parameters below this line */
#if (MLKEM_K == 2)
#define MLKEM_NAMESPACE(s) PQCP_MLKEM_NATIVE_MLKEM512_##s
#define _MLKEM_NAMESPACE(s) _PQCP_MLKEM_NATIVE_MLKEM512_##s
#elif (MLKEM_K == 3)
#define MLKEM_NAMESPACE(s) PQCP_MLKEM_NATIVE_MLKEM768_##s
#define _MLKEM_NAMESPACE(s) _PQCP_MLKEM_NATIVE_MLKEM768_##s
#elif (MLKEM_K == 4)
#define MLKEM_NAMESPACE(s) PQCP_MLKEM_NATIVE_MLKEM1024_##s
#define _MLKEM_NAMESPACE(s) _PQCP_MLKEM_NATIVE_MLKEM1024_##s
#else
#error "MLKEM_K must be in {2,3,4}"
#endif

#define MLKEM_N 256
#define MLKEM_Q 3329

#define MLKEM_SYMBYTES 32 /* size in bytes of hashes, and seeds */
#define MLKEM_SSBYTES 32  /* size in bytes of shared key */

#define MLKEM_POLYBYTES 384
#define MLKEM_POLYVECBYTES (MLKEM_K * MLKEM_POLYBYTES)

#if MLKEM_K == 2
#define MLKEM_ETA1 3
#define MLKEM_POLYCOMPRESSEDBYTES_DV 128
#define MLKEM_POLYCOMPRESSEDBYTES_DU 320
#define MLKEM_POLYVECCOMPRESSEDBYTES_DU (MLKEM_K * MLKEM_POLYCOMPRESSEDBYTES_DU)
#elif MLKEM_K == 3
#define MLKEM_ETA1 2
#define MLKEM_POLYCOMPRESSEDBYTES_DV 128
#define MLKEM_POLYCOMPRESSEDBYTES_DU 320
#define MLKEM_POLYVECCOMPRESSEDBYTES_DU (MLKEM_K * MLKEM_POLYCOMPRESSEDBYTES_DU)
#elif MLKEM_K == 4
#define MLKEM_ETA1 2
#define MLKEM_POLYCOMPRESSEDBYTES_DV 160
#define MLKEM_POLYCOMPRESSEDBYTES_DU 352
#define MLKEM_POLYVECCOMPRESSEDBYTES_DU (MLKEM_K * MLKEM_POLYCOMPRESSEDBYTES_DU)
#endif

#define MLKEM_ETA2 2

#define MLKEM_INDCPA_MSGBYTES (MLKEM_SYMBYTES)
#define MLKEM_INDCPA_PUBLICKEYBYTES (MLKEM_POLYVECBYTES + MLKEM_SYMBYTES)
#define MLKEM_INDCPA_SECRETKEYBYTES (MLKEM_POLYVECBYTES)
#define MLKEM_INDCPA_BYTES \
  (MLKEM_POLYVECCOMPRESSEDBYTES_DU + MLKEM_POLYCOMPRESSEDBYTES_DV)

#define MLKEM_PUBLICKEYBYTES (MLKEM_INDCPA_PUBLICKEYBYTES)
/* 32 bytes of additional space to save H(pk) */
#define MLKEM_SECRETKEYBYTES                                   \
  (MLKEM_INDCPA_SECRETKEYBYTES + MLKEM_INDCPA_PUBLICKEYBYTES + \
   2 * MLKEM_SYMBYTES)
#define MLKEM_CIPHERTEXTBYTES (MLKEM_INDCPA_BYTES)

#endif
