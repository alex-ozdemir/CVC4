/*********************                                                        */
/*! \file proof_node_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Proof node manager utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__PROOF_NODE_MANAGER_H
#define CVC4__EXPR__PROOF_NODE_MANAGER_H

#include <vector>

#include "expr/proof_checker.h"
#include "expr/proof_node.h"

namespace CVC4 {

/**
 * A manager for proof node objects. This is a trusted interface for creating
 * and updating ProofNode objects.
 *
 * In more detail, we say a ProofNode is "well-formed (with respect to checker
 * X)" if its d_proven field is non-null, and corresponds to the formula that
 * the ProofNode proves according to X. The ProofNodeManager class constructs
 * and update nodes that are well-formed with respect to its underlying checker.
 *
 * If no checker is provided, then the ProofNodeManager assigns the d_proven
 * field of ProofNode based on the provided "expected" argument in mkNode below,
 * which must be provided in this case.
 *
 * The ProofNodeManager is used as a trusted way of updating ProofNode objects
 * via updateNode below. In particular, this method leaves the d_proven field
 * unchanged and updates (if possible) the remaining content of a given proof
 * node.
 *
 * Notice that ProofNode objects are mutable, and hence this class does not
 * cache the results of mkNode. A version of this class that caches
 * immutable version of ProofNode objects could be built as an extension
 * or layer on top of this class.
 */
class ProofNodeManager
{
 public:
  ProofNodeManager(ProofChecker* pc = nullptr);
  ~ProofNodeManager() {}
  /**
   * This constructs a ProofNode with the given arguments. The expected
   * argument, when provided, indicates the formula that the returned node
   * is expected to prove. If we find that it does not, based on the underlying
   * checker, this method returns nullptr.
   *
   * @param id The id of the proof node.
   * @param children The children of the proof node.
   * @param args The arguments of the proof node.
   * @param expected (Optional) the expected conclusion of the proof node.
   * @return the proof node, or nullptr if the given arguments do not
   * consistute a proof of the expected conclusion according to the underlying
   * checker, if both are provided. It also returns nullptr if neither the
   * checker nor the expected field is provided, since in this case the
   * conclusion is unknown.
   */
  std::shared_ptr<ProofNode> mkNode(
      PfRule id,
      const std::vector<std::shared_ptr<ProofNode>>& children,
      const std::vector<Node>& args,
      Node expected = Node::null());
  /** Construct proof node, single child version */
  std::shared_ptr<ProofNode> mkNode(PfRule id,
                                    std::shared_ptr<ProofNode> child1,
                                    const std::vector<Node>& args,
                                    Node expected = Node::null());
  /**
   * Make the proof node corresponding to the assumption of fact.
   *
   * @param fact The fact to assume.
   * @return The assume proof of fact.
   */
  std::shared_ptr<ProofNode> mkAssume(Node fact);
  /**
   * Make scope having body pf and arguments (assumptions-to-close) assump.
   * If ensureClosed is true, then this method throws an assertion failure if
   * the returned proof is not closed. This is the case if a free assumption
   * of pf is missing from the vector assumps.
   *
   * For conveinence, the proof pf may be modified to ensure that the overall
   * result is closed. For instance, given input:
   *   pf = TRANS( ASSUME( x=y ), ASSUME( y=z ) )
   *   assumps = { y=x, y=z }
   * This method will modify pf to be:
   *   pf = TRANS( SYMM( ASSUME( y=x ) ), ASSUME( y=z ) )
   * so that y=x matches the free assumption. The returned proof is:
   *   SCOPE(TRANS( SYMM( ASSUME( y=x ) ), ASSUME( y=z ) ) :args { y=x, y=z })
   *
   * Additionally, if both ensureClosed and doMinimize are true, assumps is
   * updated to contain exactly the free asumptions of pf. The minimized
   * vector is passed as arguments to the SCOPE.
   *
   * @param pf The body of the proof,
   * @param assumps The assumptions-to-close of the scope,
   * @param ensureClosed Whether to ensure that the proof is closed,
   * @param doMinimize Whether to minimize assumptions.
   * @param expected the node that the scope should prove.
   * @return The scoped proof.
   */
  std::shared_ptr<ProofNode> mkScope(std::shared_ptr<ProofNode> pf,
                                     std::vector<Node>& assumps,
                                     bool ensureClosed = true,
                                     bool doMinimize = false,
                                     Node expected = Node::null());

  /**
   * This method updates pn to be a proof of the form <id>( children, args ),
   * while maintaining its d_proven field. This method returns false if this
   * proof manager is using a checker, and we compute that the above proof
   * is not a proof of the fact that pn previously proved.
   *
   * @param pn The proof node to update.
   * @param id The updated id of the proof node.
   * @param children The updated children of the proof node.
   * @param args The updated arguments of the proof node.
   * @return true if the update was successful.
   *
   * Notice that updateNode always returns true if there is no underlying
   * checker.
   */
  bool updateNode(ProofNode* pn,
                  PfRule id,
                  const std::vector<std::shared_ptr<ProofNode>>& children,
                  const std::vector<Node>& args);
  /** Get the underlying proof checker */
  ProofChecker* getChecker() const;

 private:
  /** The (optional) proof checker */
  ProofChecker* d_checker;
  /** Check internal
   *
   * This returns the result of proof checking a ProofNode with the provided
   * arguments with an expected conclusion, which may not null if there is
   * no expected conclusion.
   *
   * This throws an assertion error if we fail to check such a proof node, or
   * if expected is provided (non-null) and is different what is proven by the
   * other arguments.
   */
  Node checkInternal(PfRule id,
                     const std::vector<std::shared_ptr<ProofNode>>& children,
                     const std::vector<Node>& args,
                     Node expected);
};

}  // namespace CVC4

#endif /* CVC4__EXPR__PROOF_NODE_H */
