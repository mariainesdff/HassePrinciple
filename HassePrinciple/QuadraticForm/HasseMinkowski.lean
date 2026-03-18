/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.QuadraticForm.HighRank
public import HassePrinciple.QuadraticForm.RankFour
public import HassePrinciple.QuadraticForm.RankThree

@[expose] public section

namespace QuadraticForm

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (Q : QuadraticForm ℚ V)

/-- The Hasse-Minkowski theorem over `ℚ`. -/
lemma HasseMinkowski [Module.Finite ℚ V] : Q.Isotropic ↔ Q.EverywhereLocallyIsotropic := by
  refine ⟨fun h ↦ h.everywhereLocallyIsotropic, fun h ↦ ?_⟩
  by_cases dQ : Q.Nondegenerate
  · match hr : Module.finrank ℚ V with
    | 0       => sorry
    | 1       => sorry
    | 2       => sorry
    | 3       => sorry
    | 4       => sorry
    | (n + 5) => sorry
  · sorry


end QuadraticForm
