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
#include "theory/ff/parse.h"
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

  // if it's a bit-constraint, do a range.
  std::optional<Node> bitConstrainedVar = parse::bitConstraint(n);
  if (bitConstrainedVar.has_value())
  {
    Node var = toInt(bitConstrainedVar.value(), lemmas, skolems);
    Node zero = d_nm->mkConstInt(0);
    Node one = d_nm->mkConstInt(1);
    Node lower = d_nm->mkNode(kind::LEQ, zero, var);
    Node upper = d_nm->mkNode(kind::LEQ, var, one);
    Node range = d_nm->mkNode(kind::AND, lower, upper);
    Trace("ff::to-int") << "node: " << n << std::endl
                        << "; translated to a bit constraint: " << range
                        << std::endl;
    return rewrite(range);
  }

  for (TNode current :
       NodeDfsIterable(n, VisitOrder::POSTORDER, [this](TNode nn) {
         return d_cache.count(nn);
       }))
  {
    Node translation;
    Assert(!d_cache.count(current));
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
        Assert(!translatedChildren.back().isNull());
      }
      translation = translateWithChildren(current, translatedChildren, lemmas);
    }
    d_cache[current] = translation;
  }
  return d_cache[n].get();
}

Node ToInt::translateWithChildren(Node original,
                                  const std::vector<Node>& translatedChildren,
                                  std::vector<Node>& lemmas)
{
  Trace("ff::to-int") << "translating non-leaf: " << original
                      << "; of type: " << original.getType() << std::endl;
  if (TraceIsOn("ff::to-int"))
  {
    Trace("ff::to-int") << "translated children:" << std::endl;
    for (const auto& c : translatedChildren)
    {
      Trace("ff::to-int") << "  " << c << std::endl;
    }
  }
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
        translation = d_nm->mkNode(kind::EQUAL, translatedChildren);
      }
      break;
    }
    case kind::ITE:
    {
      translation = d_nm->mkNode(kind::ITE, translatedChildren);
      break;
    }
    default:
    {
      // In the default case, we have reached an operator that we do not
      // translate directly to integers. The children whose types have
      // changed from ff to int should be adjusted back to ff and then
      // this term is reconstructed.
      TypeNode resultingType;
      if (original.getType().isFiniteField())
      {
        resultingType = d_nm->integerType();
      }
      else
      {
        resultingType = original.getType();
      }
      translation =
          reconstructNode(original, resultingType, translatedChildren);
    }
  }
  Trace("ff::to-int") << " result " << translation << std::endl;
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
    TypeNode ty = original.getType();
    if (ty.isFiniteField())
    {
      // For bit-vector variables, we create fresh integer variables.
      if (original.getKind() == kind::BOUND_VARIABLE)
      {
        Unimplemented();
      }
      else
      {
        Node intCast = castToType(original, d_nm->integerType());
        // we introduce a fresh variable; defined in terms of the old
        translation = d_nm->getSkolemManager()->mkPurifySkolem(intCast);
        // add range constraints
        Node zero = d_nm->mkConstInt(0);
        Node p = d_nm->mkConstInt(original.getType().getFfSize());
        Node lower = d_nm->mkNode(kind::LEQ, zero, translation);
        Node upper = d_nm->mkNode(kind::LT, translation, p);
        Node range = d_nm->mkNode(kind::AND, lower, upper);
        range = rewrite(range);
        lemmas.push_back(range);
        // express the old variable in terms of the new one
        Assert(!skolems.count(original));
        Node backCast = castToType(translation, ty);
        skolems[original] = backCast;
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
  Trace("ff::to-int") << " result " << translation << std::endl;
  return translation;
}

Node ToInt::reconstructNode(Node originalNode,
                            TypeNode resultType,
                            const std::vector<Node>& translated_children)
{
  // first, we adjust the children of the node as needed.
  // re-construct the term with the adjusted children.
  kind::Kind_t oldKind = originalNode.getKind();
  NodeBuilder builder(oldKind);
  if (originalNode.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    builder << originalNode.getOperator();
  }
  for (uint32_t i = 0; i < originalNode.getNumChildren(); i++)
  {
    Node originalChild = originalNode[i];
    Node translatedChild = translated_children[i];
    Node adjustedChild = castToType(translatedChild, originalChild.getType());
    builder << adjustedChild;
  }
  Node reconstruction = builder.constructNode();
  // cast to tn in case the reconstruction is a field elem.
  reconstruction = castToType(reconstruction, resultType);
  return reconstruction;
}

Node ToInt::castToType(Node n, TypeNode tn)
{
  // If there is no reason to cast, return the
  // original node.
  if (n.getType() == tn)
  {
    return n;
  }
  // We only case int to ff or vice verse.
  Assert((n.getType().isFiniteField() && tn.isInteger())
         || (n.getType().isInteger() && tn.isFiniteField()));
  Trace("ff::to-int") << "castToType from " << n.getType() << " to " << tn
                      << std::endl;

  // casting integers to finite-fieldk
  if (n.getType().isInteger())
  {
    Assert(tn.isFiniteField());
    Node intToFfOp =
        d_nm->mkConst<IntToFiniteField>(IntToFiniteField(tn.getFfSize()));
    return d_nm->mkNode(intToFfOp, n);
  }
  // casting finite-field to ingers
  Assert(n.getType().isFiniteField());
  Assert(tn.isInteger());
  return d_nm->mkNode(kind::FINITEFIELD_TO_NAT, n);
}


}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
