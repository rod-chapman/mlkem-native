#!/usr/bin/env python3
# Copyright (c) 2024 The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0

import subprocess
import argparse
import os

# This file re-generated auto-generated source files in mlkem-native.
#
# It currently covers:
# - zeta values for the reference NTT and invNTT

def bitreverse(i,n):
    r = 0
    for _ in range(n):
        r = 2*r + (i & 1)
        i >>= 1
    return r

def gen_header():
    yield "// Copyright (c) 2024 The mlkem-native project authors"
    yield "// SPDX-License-Identifier: Apache-2.0"
    yield ""
    yield "// WARNING: This file is auto-generated from scripts/autogenerate_files.py"
    yield "//          Do not modify it directly."
    yield ""


def gen_zetas():
    """Generate source and header file for zeta values used in
    the reference NTT and invNTT"""

    # The zeta values are the powers of the chosen root of unity (17),
    # converted to Montgomery form.

    modulus = 3329
    root_of_unity = 17
    montgomery_factor = pow(2, 16, modulus)

    def signed_reduce(a):
        """Return signed canonical representative of a mod b"""
        c = a % modulus
        if c >= modulus / 2:
            c -= modulus
        return c

    zeta = []
    for i in range(128):
        zeta.append(signed_reduce(pow(root_of_unity, i, modulus) * montgomery_factor))

    # The source code stores the zeta table in bit reversed form
    zeta_bitrev = [ zeta[bitreverse(i,7)] for i in range(128) ]

    yield "// Table of zeta values used in the reference NTT and inverse NTT."
    yield "// See autogenerate_files.py for details."
    yield "const int16_t zetas[128] = {"
    for i in range(0,128):
        yield str(zeta_bitrev[i]) + ","
    yield "};"

def gen_zeta_file():
    yield from gen_header()
    yield "#include \"ntt.h\""
    yield ""
    yield from gen_zetas()
    yield ""

def _main():
    parser = argparse.ArgumentParser(
        formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument("--dry-run", default=False, action='store_true')

    args = parser.parse_args()

    base = "mlkem"
    zeta_source = f"{base}/zetas.c"

    file_content = '\n'.join(gen_zeta_file())
    p = subprocess.run(["clang-format"], capture_output=True, input=file_content, text=True)
    if p.returncode != 0:
        print(f"Failed to auto-format autogenerated code (clang-format return code {p.returncode}")
        exit(1)
    file_content = p.stdout

    if args.dry_run is False:
        with open(zeta_source, "w+") as f:
            f.write('\n'.join(gen_zeta_file()))
    else:
        if os.path.exists(zeta_source) is False:
            print(f"Autogenerated file {zeta_source} does not exist")
            exit(1)
        with open(zeta_source, "r") as f:
            current_content = f.read()
        if current_content != file_content:
            print(f"Autogenerated file {zeta_source} needs updating. Have you called scripts/autogenerated.py?")
            exit(1)

    # Auto-format using clang-format, so we don't need to
    # bother about manual formatting above
    subprocess.run(["clang-format", "-i", zeta_source])

if __name__ == "__main__":
    _main()