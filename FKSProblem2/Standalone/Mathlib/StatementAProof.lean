/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import FKSProblem2.Standalone.Mathlib.StatementA

import FKSProblem2.Standalone.Mathlib.Support.GraphDimensionBridge

import GraphDimension.Extremal.SevenVertices

/-!
# Proof of the dimension-three question

Every graph on seven vertices, or its complement, has a unit-distance representation in `ℝ³`.
This is the shared library's seven-vertex disjunction, with the representation predicate
rewritten through the bridge on each side of the disjunction.
-/

public section

namespace FKSProblem2.StatementA

theorem questionAt3.proof : questionAt3 := by
  change ∀ G : SimpleGraph (Fin 7),
    HasUnitDistanceRepresentation 3 G ∨ HasUnitDistanceRepresentation 3 Gᶜ
  intro G
  rcases G.unitDistEmbeddable_three_or_compl_fin_seven with h | h
  · exact Or.inl ((hasUnitDistanceRepresentation_iff_unitDistEmbeddable G 3).mpr h)
  · exact Or.inr ((hasUnitDistanceRepresentation_iff_unitDistEmbeddable Gᶜ 3).mpr h)

end FKSProblem2.StatementA
