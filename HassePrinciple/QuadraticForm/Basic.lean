/-
Copyright (c) 2026b Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import Mathlib.NumberTheory.Padics.PadicNumbers

@[expose] public section

namespace QuadraticForm

/-- A quadratic form is isotropic if it vanishes on some nonzero vector. -/
abbrev Isotropic {R V : Type*} [CommSemiring R] [AddCommGroup V] [Module R V]
    (Q : QuadraticForm R V) := ¬ Q.Anisotropic

-- Let `V` be a `ℚ`-vector space.
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

-- Let `Q` be a quadratic form on `V`.
variable (Q : QuadraticForm ℚ V)

/-- A quadratic form over `ℚ` is everywhere locally isotropic if it has nontrivial
`p`-adic points for all `p`, and real points. -/
def EverywhereLocallyIsotropic :=
  (∀ (p : ℕ) [Fact (p.Prime)], (Q.baseChange ℚ_[p]).Isotropic) ∧
  (Q.baseChange ℝ).Isotropic

variable {Q}

-- The easy implication of the Hasse-Minkowski theorem.
theorem Isotropic.everywhereLocallyIsotropic (h : Q.Isotropic) :
    Q.EverywhereLocallyIsotropic := by
  sorry

lemma _root_.QuadraticMap.nondegenerate_of_anisotropic {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Invertible (2 : R)] {Q : QuadraticForm R M} (hQ : Q.Anisotropic) :
    Q.Nondegenerate :=
  sorry

lemma _root_.QuadraticMap.degenerate_baseChange {R A M : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M] [Algebra R A] [Module R M] [Invertible (2 : R)] [Invertible (2 : A)]
    {Q : QuadraticForm R M} (hQ : ¬ Q.Nondegenerate) :
    ¬ (Q.baseChange A).Nondegenerate := by
  sorry

open QuadraticMap

theorem HasseMinkowski_of_degenerate (Q : QuadraticForm ℚ V)
    (hQ : ¬ Q.Nondegenerate) :
    Q.Isotropic ↔ Q.EverywhereLocallyIsotropic := by
  have degenQ := Q.nondegenerate_of_anisotropic.mt hQ
  have degenR := ((Q.baseChange ℝ).nondegenerate_of_anisotropic).mt
    (degenerate_baseChange (A := ℝ) hQ)
  simp only [Isotropic, degenQ, not_false_eq_true,
    EverywhereLocallyIsotropic, degenR, and_true, true_iff]
  intro p hp
  exact ((Q.baseChange ℚ_[p]).nondegenerate_of_anisotropic).mt
    (degenerate_baseChange (A := ℚ_[p]) hQ)

-- The cases of rank 0 and 1 are easy:

-- The rank zero case will follow trivially from this lemma:
lemma anisotropic_of_rank_zero {R V : Type*} [CommRing R] [IsDomain R] [StrongRankCondition R]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.IsTorsionFree R V]
    (hr : Module.finrank R V = 0) (Q : QuadraticForm R V) : Q.Anisotropic := by
  rw [Module.finrank_zero_iff] at hr
  exact fun x _ ↦ Subsingleton.eq_zero x

-- The rank one case will follow from:
lemma anisotropic_of_rank_one {R V : Type*} [CommRing R] [IsDomain R] [StrongRankCondition R]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.IsTorsionFree R V]
    (hr : Module.finrank R V = 1) {Q : QuadraticForm R V} (hQ : Q ≠ 0) : Q.Anisotropic := by
  sorry

namespace EverywhereLocallyIsotropic

lemma isotropic_of_rank_two (hr : Module.finrank ℚ V = 2) (hQ : Q.EverywhereLocallyIsotropic) :
    Q.Isotropic := sorry

lemma isotropic_of_rank_three (hr : Module.finrank ℚ V = 3) (hQ : Q.EverywhereLocallyIsotropic) :
    Q.Isotropic := sorry

lemma isotropic_of_rank_four (hr : Module.finrank ℚ V = 4) (hQ : Q.EverywhereLocallyIsotropic) :
    Q.Isotropic := sorry

lemma isotropic_of_five_le_rank (hr : Module.finrank ℚ V = 4) (hQ : Q.EverywhereLocallyIsotropic) :
    Q.Isotropic := sorry

end EverywhereLocallyIsotropic

end QuadraticForm
