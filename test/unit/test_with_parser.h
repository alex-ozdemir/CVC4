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
 * Common header for tests that have access to an SMT-LIB parser.
 */

#ifndef CVC5__TEST__UNIT__TEST_API_H
#define CVC5__TEST__UNIT__TEST_API_H

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

#include "gtest/gtest.h"

#include "expr/node.h"
#include "test.h"

namespace cvc5::internal {
namespace test {

/**
 * For writing tests that accesss and SMT-LIB parser.
 *
 * The parser is set to logic ALL.
 */
class TestWithParser : public TestInternal
{
 protected:

  void SetUp() override
  {
    d_solver.reset(new cvc5::Solver());
    d_symman.reset(new parser::SymbolManager(d_solver.get()));
    d_ip.reset(new parser::InputParser(d_solver.get(), d_symman.get()));
  }
  std::unique_ptr<cvc5::Solver> d_solver;
  std::unique_ptr<parser::SymbolManager> d_symman;
  std::unique_ptr<cvc5::parser::InputParser> d_ip;

 public:

  /**
   * Run this SMT-LIB command.
   */
  void doCommand(const std::string& s)
  {
    d_ip->setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6, "temp");
    //d_ip->setLogic("ALL");
    d_ip->appendIncrementalStringInput(s);
    auto command = d_ip->nextCommand();
    command.invoke(d_solver.get(), d_symman.get(), std::cout);
  }

  /**
   * Parse a node from SMT-LIB.
   */
  Node parseNode(const std::string& s)
  {
    d_ip->setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6, "temp");
    //d_ip->setLogic("ALL");
    d_ip->appendIncrementalStringInput(s);
    return *d_ip->nextTerm().d_node;
  }

};

}  // namespace test
}  // namespace cvc5::internal
#endif

