/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.QuadraticForm.Basic
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers

/-! # Quadratic forms over ℚ -/

@[expose] public section

open Module QuadraticMap

namespace QuadraticForm

-- Let `V` be a `ℚ`-vector space.
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

-- Let `Q` be a quadratic form on `V`.
variable (Q : QuadraticForm ℚ V)

/-- A quadratic form over `ℚ` is everywhere locally isotropic if it has nontrivial
`p`-adic points for all `p`, and real points. -/
def EverywhereLocallyIsotropic :=
  (∀ (p : ℕ) [Fact (p.Prime)], (Q.baseChange ℚ_[p]).Isotropic) ∧ (Q.baseChange ℝ).Isotropic

variable {Q}

-- The easy implication of the Hasse-Minkowski theorem.
theorem _root_.QuadraticMap.Isotropic.everywhereLocallyIsotropic (h : Q.Isotropic) :
    Q.EverywhereLocallyIsotropic := by
  obtain ⟨x, ⟨hx, hxne0⟩⟩ := represents_zero_iff_isotropic.mpr h
  refine ⟨fun _ _ => ?_, ?_⟩ <;>
  exact represents_zero_iff_isotropic.mp ⟨1 ⊗ₜ x, ⟨by simp [hx], by simp [hxne0]⟩⟩

/- Will follow from `QuadraticMap.nondegenerate_of_anisotropic` and
  `QuadraticMap.degenerate_baseChange`. -/
theorem HasseMinkowski_of_degenerate (Q : QuadraticForm ℚ V) (hQ : ¬ Q.Nondegenerate) :
    Q.Isotropic ↔ Q.EverywhereLocallyIsotropic := by
  have dQ := Q.nondegenerate_of_anisotropic.mt hQ
  have dR := ((Q.baseChange ℝ).nondegenerate_of_anisotropic).mt (degenerate_baseChange (A := ℝ) hQ)
  simp only [Isotropic, dQ, not_false_eq_true, EverywhereLocallyIsotropic, dR, and_true, true_iff]
  intro p hp
  exact ((Q.baseChange ℚ_[p]).nondegenerate_of_anisotropic).mt (degenerate_baseChange hQ)

namespace EverywhereLocallyIsotropic

lemma isotropic_of_rank_zero [Module.Finite ℚ V] (hr : finrank ℚ V = 0)
    (hQ' : Q.EverywhereLocallyIsotropic) : Q.Isotropic := by
  have h' := hQ'.2
  contrapose! h'
  exact anisotropic_of_rank_zero (by simp [hr])

lemma isotropic_of_rank_one (hr : finrank ℚ V = 1) (hQ : Q.EverywhereLocallyIsotropic) :
    Q.Isotropic := by
  simpa [isotropic_iff_zero_of_rank_one hr, baseChange_ext_iff, Q.ext_iff] using
    (isotropic_iff_zero_of_rank_one (by simp [hr])).mp hQ.2

/-
Auxiliary lemma deducing from a representation of 0 that the coefficient ratio is a square.
This is used twice, in ℝ and in ℚ_[p], so we make it a lemma in a general setting.
-/
private lemma coeff_ratio_isSquare_of_represents_zero {K : Type*} [Field K] [CharZero K]
    {w : Fin 2 → ℚ} {x : Fin 2 → K} (hw0 : w 0 ≠ 0) (hx1 : x 1 ≠ 0)
    (h : ↑(w 0) * x 0 ^ 2 + ↑(w 1) * x 1 ^ 2 = 0) : ↑(- (w 0)⁻¹ * (w 1)) = ((x 1)⁻¹ * x 0) ^ 2 := by
  rw [Rat.cast_mul, Rat.cast_neg, Rat.cast_inv]
  field_simp [hw0, hx1]
  exact neg_eq_of_add_eq_zero_left h

/-
Auxiliary lemma that the representative of 0 of a nondegenerate quadratic form is nonzero
in both components.
This is used twice, in ℝ and in ℚ_[p], so we make it a lemma in a general setting.
-/
private lemma comp_ne_zero_of_nondegenerate {K : Type*} [Field K] [CharZero K] {w : Fin 2 → ℚˣ}
    {x : Fin 2 → K} (hx : x ≠ 0) (h : w 0 * x 0 ^ 2 + w 1 * x 1 ^ 2 = 0) : x 0 ≠ 0 ∧ x 1 ≠ 0 := by
  by_contra! h'
  apply hx
  by_cases h0 : x 0 = 0
  · aesop (add norm funext_iff)
  · aesop

lemma isotropic_of_rank_two [FiniteDimensional ℚ V] (hr : finrank ℚ V = 2) (hQ : Q.Nondegenerate)
    (hQ' : Q.EverywhereLocallyIsotropic) : Q.Isotropic := by
  obtain ⟨hQ'f, hQ'R⟩ := hQ'
  -- Change assumption and goal from isotropic to representing 0
  simp only [← represents_zero_iff_isotropic] at *
  -- Q is equivalent to Q(w)
  obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate 2 hr
    (nondegenerate_associated_iff.mpr hQ).1
  -- Q_v is equivalent to Q(w)_v
  have heqR : (Q.baseChange ℝ).Equivalent (weightedSumSquares ℝ (fun i ↦ (w i : ℚ))) :=
      (hw.baseChange ℝ).trans (baseChange_weightedSumSquares ℚ ℝ fun i ↦ (w i : ℚ))
  have heqf (p : ℕ) [Fact (Nat.Prime p)] :
      (Q.baseChange ℚ_[p]).Equivalent (weightedSumSquares ℚ_[p] (fun i ↦ (w i : ℚ))) :=
    (hw.baseChange ℚ_[p]).trans (baseChange_weightedSumSquares ℚ ℚ_[p] fun i ↦ (w i : ℚ))
  -- Change goal to Q(w) represents 0
  rw [hw.represents_iff]
  -- Change assumption to Q(w) represents 0 everywhere
  rw [heqR.represents_iff] at hQ'R
  have hQ'fw (p : ℕ) [Fact (Nat.Prime p)] :
      (weightedSumSquares ℚ_[p] (fun i ↦ (w i : ℚ))).represents 0 :=
    ((heqf p).represents_iff 0).mp (hQ'f p)
  -- Simplify weightedSumSquares expressions
  simp only [represents, weightedSumSquares_apply, Fin.sum_univ_two, ← pow_two, Rat.smul_def]
    at hQ'R hQ'fw ⊢
  -- Represents 0 over ℝ implies that - (w 0)⁻¹ * w 1 is positive
  have hR' : 0 ≤ - ((w 0 : ℚ)⁻¹) * w 1 := by
    obtain ⟨x, hx, hx0⟩ := hQ'R
    rw [← Rat.cast_nonneg (K := ℝ), ← Real.isSquare_iff, isSquare_iff_exists_sq]
    exact ⟨(x 1)⁻¹ * x 0, coeff_ratio_isSquare_of_represents_zero (w := fun i ↦ (w i : ℚ)) (by simp)
      (comp_ne_zero_of_nondegenerate hx0 hx).2 hx⟩
  -- Represents 0 over ℚ_[p] implies that the `p`-adic valuation of - (w 0)⁻¹ * w 1 is even
  have hf (p : ℕ) (hp : p.Prime) : Even (padicValRat p (- (w 0 : ℚ)⁻¹ * w 1)) := by
    have : Fact (p.Prime) := ⟨hp⟩
    obtain ⟨x, hx⟩ := hQ'fw p
    rw [← Padic.valuation_ratCast, coeff_ratio_isSquare_of_represents_zero (w := fun i ↦ (w i : ℚ))
      (by simp) (comp_ne_zero_of_nondegenerate hx.2 hx.1).2 hx.1]
    simp
  -- A nonnegative rational number with even `p`-adic valuation for all `p` is a square
  obtain ⟨x, hx⟩ : ∃ (x : ℚ), - (w 0 : ℚ)⁻¹ * w 1 = x * x :=
    Rat.isSquare_iff_even_factorization.mpr ⟨hR', hf⟩
  exact ⟨![x, 1], by simp [pow_two, ← hx, Units.smul_def], by simp⟩

end EverywhereLocallyIsotropic

end QuadraticForm
