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
 * Mapping finite-field constraints to integer constraints.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__TO_INT_H
#define CVC5__THEORY__FF__TO_INT_H

#include "context/cdhashmap.h"
#include "theory/ff/parse.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

class ToInt : protected EnvObj
{
  using CDNodeMap = context::CDHashMap<Node, Node>;

 public:
  /**
   * Constructor.
   */
  ToInt(Env& env);
  ~ToInt();

  /**
   * Replace field elements in n with integers.
   * @param n is a field term or formula to be translated.
   * @param lemmas additional lemmas that are needed for the translation
   * to be sound. These are range constraints on introduced variables.
   * @param skolems a map in which the following information will be stored
   * during the run of toInt: for each FF variable n, skolems[n] is its new
   * definition: ((_ nat2bv k) nn), where k is the bit-width of n, and nn is the
   * integer variable that corresponds to n.
   * For each UF f from BV to BV, skolems[f] is lambda x : BV[k] . ((_ nat2bv i)
   * ff((bv2nat x))), where k is the bit-width of the domain of f, i is the
   * bit-width of its range, and ff is a Int->Int function that corresponds to
   * f. For functions with other signatures this is similar
   * @return integer node that corresponds to n
   */
  Node toInt(Node n,
                std::vector<Node>& lemmas,
                std::map<Node, Node>& skolems);

 private:

  /**
   * Performs the actual translation to integers for nodes
   * that have children.
   */
  Node translateWithChildren(Node original,
                             const std::vector<Node>& translated_children,
                             std::vector<Node>& lemmas);

  /**
   * Performs the actual translation to integers for nodes
   * that don't have children (variables, constants, uninterpreted function
   * symbols).
   */
  Node translateNoChildren(Node original,
                           std::vector<Node>& lemmas,
                           std::map<Node, Node>& skolems);

  /**
   * Reconstructs a node whose main operator cannot be
   * translated to integers.
   * Reconstruction is done by casting to integers/finite-field elements
   * as needed.
   * For example, if node is (select A x) where A
   * is a field array, we do not change A to be
   * an integer array, even though x was translated
   * to integers.
   * In this case we cast x to (ff2nat x) during
   * the reconstruction.
   *
   * @param originalNode the node that we are reconstructing
   * @param resultType the desired type for the reconstruction
   * @param translated_children the children of originalNode
   *        after their translation to integers.
   * @return A node with originalNode's operator that has type resultType.
   */
  Node reconstructNode(Node originalNode,
                       TypeNode resultType,
                       const std::vector<Node>& translated_children);

  /**
   * A useful utility function.
   * if n is an integer and tn is finite-field,
   * applies the IntToFiniteField operator on n.
   * if n is a finite-field and tn is integer,
   * applies FINITEFIELD_TO_NAT operator.
   * Otherwise, keeps n intact.
   */
  Node castToType(Node n, TypeNode tn);

  /** Translation cache */
  CDNodeMap d_cache;

  /** Node manager that is used throughout the pass */
  NodeManager* d_nm;
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__TO_INT_H */
