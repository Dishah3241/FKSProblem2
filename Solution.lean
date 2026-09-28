/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import FKSProblem2.Standalone.Mathlib.InlineFKSProblem2Proof

/-!
# FKS Problem 2: a graph or its complement on 2d+1 vertices embeds in R^d

Connects Palomar's advertised declaration to the proof. This module contains no mathematics: it
restates the theorem Comparator checks and discharges it from the development.

The statement here must match `Challenge.lean`'s. Comparator compiles the two modules in separate
sandboxes and rejects any difference.
-/

public section

namespace FKSProblem2.Palomar

/-- Every simple graph on seven vertices, or its complement, has a unit-distance
representation in `ℝ^3`: the proved `d = 3` instance of FKS 2020 Problem 2. -/
theorem target :
    FKSProblem2.Standalone.Mathlib.InlineFKSProblem2.questionAt3 :=
  FKSProblem2.Standalone.Mathlib.InlineFKSProblem2.questionAt3.proof

end FKSProblem2.Palomar
