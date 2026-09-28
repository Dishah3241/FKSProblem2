/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import FKSProblem2.Standalone.Mathlib.StatementA

public import GraphDimension.Basic

/-!
# Bridge to the shared unit-distance library

Statement A's representation predicate and the shared library's embedding predicate say the same
thing: an injective placement of the vertices in Euclidean space under which every edge has
length one, with non-edges unconstrained. The equivalence is definitional, so either side's
placement results transfer to the other verbatim.
-/

public section

/-- Statement A's representation predicate and `SimpleGraph.UnitDistEmbeddable` agree: both
quantify an injective placement in `EuclideanSpace ℝ (Fin d)` sending every edge to distance
`1`, leaving non-edges unconstrained. -/
theorem FKSProblem2.hasUnitDistanceRepresentation_iff_unitDistEmbeddable
    {V : Type*} (G : SimpleGraph V) (d : ℕ) :
    FKSProblem2.StatementA.HasUnitDistanceRepresentation d G ↔ G.UnitDistEmbeddable d :=
  Iff.rfl
