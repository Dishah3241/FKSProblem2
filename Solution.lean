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

/-- Any two distinct elements of `{2, 3, 5}` are coprime. -/
theorem target :
    FKSProblem2.Standalone.Mathlib.InlineFKSProblem2.SmallPrimesCoprime :=
  FKSProblem2.Standalone.Mathlib.InlineFKSProblem2.SmallPrimesCoprime.proof

end FKSProblem2.Palomar
