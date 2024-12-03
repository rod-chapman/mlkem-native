// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0 AND Apache-2.0

#include "verify.h"

void harness(void)
{
  uint8_t a, b, c, cond;

  c = ct_sel_uint8(a, b, cond);
}