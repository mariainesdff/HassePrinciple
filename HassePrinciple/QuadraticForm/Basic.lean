/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
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

lemma nondegenerate_of_anisotropic {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Invertible (2 : R)] {Q : QuadraticForm R M} (hQ : Q.Anisotropic) :
    Q.Nondegenerate :=
  sorry

lemma degenerate_baseChange {R A M : Type*} [CommRing R] [CommRing A] [AddCommGroup M]
    [Algebra R A] [Module R M] [Invertible (2 : R)] [Invertible (2 : A)] {Q : QuadraticForm R M}
    (hQ : ¬ Q.Nondegenerate) :
    ¬ (Q.baseChange A).Nondegenerate := by
  sorry

open QuadraticMap

/- Will follow from `QuadraticMap.nondegenerate_of_anisotropic` and
  `QuadraticMap.degenerate_baseChange`. -/
theorem HasseMinkowski_of_degenerate (Q : QuadraticForm ℚ V) (hQ : ¬ Q.Nondegenerate) :
    Q.Isotropic ↔ Q.EverywhereLocallyIsotropic := by
  have dQ := Q.nondegenerate_of_anisotropic.mt hQ
  have dR := ((Q.baseChange ℝ).nondegenerate_of_anisotropic).mt (degenerate_baseChange (A := ℝ) hQ)
  simp only [Isotropic, dQ, not_false_eq_true, EverywhereLocallyIsotropic, dR, and_true, true_iff]
  intro p hp
  exact ((Q.baseChange ℚ_[p]).nondegenerate_of_anisotropic).mt (degenerate_baseChange hQ)

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

theorem equivalent_weightedSumSquares' {K V : Type*} [Field K] [Invertible 2] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] [NeZero (Module.finrank K V)] (Q : QuadraticForm K V) :
  ∃ (w : Fin (Module.finrank K V) → K), w (0 : Fin (Module.finrank K V)) = 1 ∧
    QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares K w) := sorry

theorem equivalent_weightedSumSquares_units_of_nondegenerate {K V : Type*} [Field K] [Invertible 2]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [NeZero (Module.finrank K V)]
  (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
  ∃ (w : Fin (Module.finrank K V) → Kˣ), w (0 : Fin (Module.finrank K V)) = 1 ∧
    QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares K w) := sorry

namespace EverywhereLocallyIsotropic

lemma isotropic_of_rank_zero (hr : Module.finrank ℚ V = 0) (hQ : Q.Nondegenerate)
    (hQ' : Q.EverywhereLocallyIsotropic) :
    Q.Isotropic := sorry

lemma isotropic_of_rank_one (hr : Module.finrank ℚ V = 1) (hQ : Q.Nondegenerate)
    (hQ' : Q.EverywhereLocallyIsotropic) :
    Q.Isotropic := sorry

lemma isotropic_of_rank_two (hr : Module.finrank ℚ V = 2) (hQ : Q.Nondegenerate)
    (hQ' : Q.EverywhereLocallyIsotropic) :
    Q.Isotropic := sorry

end EverywhereLocallyIsotropic

end QuadraticForm
