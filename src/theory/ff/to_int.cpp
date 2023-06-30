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

#include "theory/ff/to_int.h"

#include "expr/node_traversal.h"
#include "expr/skolem_manager.h"
#include "util/finite_field_value.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

ToInt::ToInt(Env& env)
    : EnvObj(env), d_cache(userContext()), d_nm(NodeManager::currentNM()){};

ToInt::~ToInt(){};

/**
 * Translate n to Integers via post-order traversal.
 */
Node ToInt::toInt(Node n,
                  std::vector<Node>& lemmas,
                  std::map<Node, Node>& skolems)
{
  // make sure the node is re-written
  n = rewrite(n);

  for (TNode current :
       NodeDfsIterable(n, VisitOrder::POSTORDER, [this](TNode nn) {
         return d_cache.count(nn);
       }))
  {
    Node translation;
    if (current.getNumChildren() == 0)
    {
      translation = translateNoChildren(current, lemmas, skolems);
    }
    else
    {
      std::vector<Node> translatedChildren;
      for (TNode c : current)
      {
        translatedChildren.push_back(d_cache[c]);
      }
      translation = translateWithChildren(current, translatedChildren, lemmas);
    }
  }
  return d_cache[n].get();
}

Node ToInt::translateWithChildren(Node original,
                                  const std::vector<Node>& translatedChildren,
                                  std::vector<Node>& lemmas)
{
  // Store the translated node
  Node translation;

  // Translate according to the kind of the original node.
  switch (original.getKind())
  {
    case kind::FINITE_FIELD_ADD:
    {
      translation = d_nm->mkNode(kind::ADD, translatedChildren);
      break;
    }
    case kind::FINITE_FIELD_NEG:
    {
      translation = d_nm->mkNode(kind::NEG, translatedChildren);
      break;
    }
    case kind::FINITE_FIELD_MULT:
    {
      translation = d_nm->mkNode(kind::MULT, translatedChildren);
      break;
    }
    case kind::EQUAL:
    {
      if (original[0].getType().isFiniteField())
      {
        // Field equalities are existential
        Node q = d_nm->mkBoundVar("q", d_nm->integerType());
        Node diff = d_nm->mkNode(kind::SUB, translatedChildren);
        Node p = d_nm->mkConstInt(original[0].getType().getFfSize());
        Node prod = d_nm->mkNode(kind::MULT, q, p);
        Node vars = d_nm->mkNode(kind::BOUND_VAR_LIST, q);
        translation = d_nm->mkNode(kind::EXISTS, vars, diff.eqNode(prod));
      }
      else
      {
        // Other equalities are untouched.
        translation = original;
      }
      break;
    }
    default:
    {
      translation = original;
    }
  }
  return translation;
}

Node ToInt::translateNoChildren(Node original,
                                std::vector<Node>& lemmas,
                                std::map<Node, Node>& skolems)
{
  Trace("ff::to-int") << "translating leaf: " << original
                      << "; of type: " << original.getType() << std::endl;
  // The result of the translation
  Node translation;

  // The translation is done differently for variables (bound or free)  and
  // constants (values)
  if (original.isVar())
  {
    if (original.getType().isFiniteField())
    {
      // For bit-vector variables, we create fresh integer variables.
      if (original.getKind() == kind::BOUND_VARIABLE)
      {
        Unimplemented();
      }
      else
      {
        Node intCast = d_nm->mkNode(kind::FINITEFIELD_TO_NAT, original);
        // we introduce a fresh variable, add range constraints, and save the
        // connection between original and the new variable via intCast
        translation = d_nm->getSkolemManager()->mkPurifySkolem(intCast);
        Node zero = d_nm->mkConstInt(0);
        Node p = d_nm->mkConstInt(original.getType().getFfSize());
        Node lower = d_nm->mkNode(kind::LEQ, zero, translation);
        Node upper = d_nm->mkNode(kind::LT, translation, p);
        Node range = d_nm->mkNode(kind::AND, lower, upper);
        range = rewrite(range);
        lemmas.push_back(translation);
        // add bvCast to skolems if it is not already there.
        Assert(!skolems.count(original));
        skolems[original] = intCast;
      }
    }
    else if (original.getType().isFunction())
    {
      Unimplemented();
    }
    else
    {
      // leave other variables intact
      translation = original;
    }
  }
  else
  {
    // original is a constant (value)
    if (original.getKind() == kind::CONST_FINITE_FIELD)
    {
      // field element constants are transformed into their integer value.
      translation =
          d_nm->mkConstInt(original.getConst<FiniteFieldValue>().getValue());
    }
    else
    {
      // Other constants or operators stay the same.
      translation = original;
    }
  }
  return translation;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
