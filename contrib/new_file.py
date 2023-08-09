#!/usr/bin/env python

from typing import List
from pathlib import PurePath
import os
import sys
import re


def mk_header(snake_path: List[str], description: str) -> str:
    if len(description) == 0:
        description = "TODO"
    while len(snake_path) > 0 and snake_path[0] == "src":
        del snake_path[0]
    guard = "__".join(p.upper() for p in snake_path)
    start = f"""\
/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * {description}
 */

#include "cvc5_private.h"

#ifndef CVC5__{guard}_H
#define CVC5__{guard}_H

// external includes

// std includes

// internal includes

namespace cvc5::internal {{
"""
    end = ""
    for p in snake_path[:-1]:
        start += f"namespace {p} {{\n"
        end += f"}}  // namespace {p}\n"

    end += f"""\
}}  // namespace cvc5::internal

#endif /* CVC5__{guard}_H */
"""
    return f"{start}\n\n{end}"


def mk_cpp(snake_path: List[str], description: str) -> str:
    if len(description) == 0:
        description = "TODO"
    while len(snake_path) > 0 and snake_path[0] == "src":
        del snake_path[0]
    header_path = "/".join(snake_path)
    guard = "__".join(p.upper() for p in snake_path)
    start = f"""\
/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * {description}
 */

#include "{header_path}.h"

// external includes

// std includes

// internal includes

namespace cvc5::internal {{
"""
    end = ""
    for p in snake_path[:-1]:
        start += f"namespace {p} {{\n"
        end += f"}}  // namespace {p}\n"

    end += f"""\
}}  // namespace cvc5::internal
"""
    return f"{start}\n\n{end}"


def path_prefixes(path):
    parts = PurePath(path).parts
    return [str(PurePath(*parts[:i])) for i in range(len(parts))]


def path_suffixes(path):
    parts = PurePath(path).parts
    return [str(PurePath(*parts[-i - 1 :])) for i in range(len(parts))]


def add_to_cmake(header_path, cpp_path):
    print(path_prefixes(cpp_path))
    print(path_suffixes(cpp_path))
    for header_path, cpp_path, cmake_dir in zip(
        path_suffixes(header_path),
        path_suffixes(cpp_path),
        reversed(path_prefixes(header_path)),
    ):
        cmake_path = f"{cmake_dir}/CMakeLists.txt"
        if not os.path.exists(cmake_path):
            continue
        print(f"trying to add {cpp_path} to {cmake_path}")
        lines = open(cmake_path).readlines()
        output = ""
        while len(lines) > 0 and "libcvc5_add_sources" not in lines[0]:
            output += lines[0]
            del lines[0]
        if len(lines) == 0:
            print(f"could not find line 'libcvc5_add_sources(' in {cmake_path}")
            continue
        output += lines[0]
        del lines[0]
        while len(lines) > 0 and (lines[0].strip() < cpp_path or lines[0].strip() == "("):
            output += lines[0]
            del lines[0]
        if len(lines) == 0:
            print(f"could not find place for {cpp_path} in {cmake_path}")
            continue
        output += f"  {cpp_path}\n"
        output += f"  {header_path}\n"
        for line in lines:
            output += line
        with open(cmake_path, "w") as f:
            f.write(output)
            print(f"added {cpp_path} to {cmake_path}")
        return
    print(f"could not find place for {cpp_path} anywhere")


def main():
    if "src" not in os.listdir(os.curdir):
        print("Run this script from cvc5's repository root")
        sys.exit(1)
    path = input("file path (no extension, ex: 'src/util/algs'): ")
    dir_ = os.path.dirname(path)
    if not os.path.isdir(dir_):
        print(f"Directory {dir_} does not exist")
        sys.exit(1)
    if os.path.exists(path):
        print(f"File {path} exists already")
        sys.exit(1)
    filename = os.path.basename(path)
    if not re.match("[a-z_]+", filename):
        print("Filename {filename} should be lowercase with underscores")
        sys.exit(1)
        if re.match("__", filename):
            print("Filename {filename} cannot have a double underscore")
            sys.exit(1)
    snake_case_path = path.split("/")
    for p in snake_case_path:
        if not re.match("[a-z_]+", p):
            print("Path component {p} should be lowercase with underscores")
            sys.exit(1)
            if re.match("__", p):
                print("Path coponent {p} cannot have a double underscore")
                sys.exit(1)
    header_path = f"{path}.h"
    cpp_path = f"{path}.cpp"
    description = input("short description (optional): ")
    header = mk_header(snake_case_path, description)
    cpp = mk_cpp(snake_case_path, description)
    add_to_cmake(header_path, cpp_path)
    open(cpp_path, "w").write(cpp)
    open(header_path, "w").write(header)


main()
