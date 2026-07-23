/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.ForMathlib.LinearAlgebra.TensorProduct.Prod
public import HassePrinciple.QuadraticForm.HasseMinkowskiInvariant
public import HassePrinciple.QuadraticForm.RankThree
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # The Hasse-Minkowski theorem for rank 4 quadratic forms -/

@[expose] public section

namespace QuadraticForm.EverywhereLocallyIsotropic

open Module QuadraticForm _root_.QuadraticMap TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {Q : QuadraticForm ℚ V}

/-- The obvious linear equivalence between `(Fin 4 → ℚ)` and
  `(Fin 2 → ℚ) × (Fin 2 → ℚ)`, where `finrank ℚ V = 4`. -/
private noncomputable def finFourLinearEquivProd :
    (Fin 4 → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ) × (Fin 2 → ℚ) where
  toFun x  := ⟨![x 0, x 1], ![x 2, x 3]⟩
  map_add' x y  := by simp
  map_smul' r x := by simp
  invFun x a := ![x.1 0, x.1 1, x.2 0, x.2 1] a
  left_inv x := by ext a; fin_cases a <;> simp
  right_inv x := by ext a <;> fin_cases a <;> simp

private theorem weightedSumSquares_equiv_prod (w : Fin 4 → ℚˣ) :
    (weightedSumSquares ℚ w).Equivalent
      ((weightedSumSquares ℚ ![w 0, w 1]).prod (-weightedSumSquares ℚ ![-w 2, -w 3])) :=
  ⟨finFourLinearEquivProd, by
    intro f
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, finFourLinearEquivProd,
      AddHom.toFun_eq_coe, AddHom.coe_mk, QuadraticMap.prod_apply, weightedSumSquares_apply,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      QuadraticMap.neg_apply, Units.neg_smul, neg_add_rev, neg_neg, Fin.sum_univ_four]
    ring⟩

open hilbertSym

private theorem isotropic_prod_neg {k : Type*} [Field k] [CharZero k] [HasBilinHilbertSym k]
    [Algebra ℚ k] {w : Fin 2 → ℚˣ} {x : ℚˣ}
    (hx : hilbertSym (x : k) (-(w ⟨0, by omega⟩) * (w ⟨1, by omega⟩)) =
      hilbertSym (w ⟨0, by omega⟩ : k) (w ⟨1, by omega⟩)) :
    Isotropic  ((prod (weightedSumSquares ℚ w) (weightedSumSquares ℚ ![-x])).baseChange k) := by
  have : (QuadraticForm.baseChange k
      (prod (weightedSumSquares ℚ ![w ⟨0, by omega⟩, w ⟨1, by omega⟩])
      (weightedSumSquares ℚ ![-x]))).Equivalent
    (prod (QuadraticForm.baseChange k
      (weightedSumSquares ℚ ![w ⟨0, by omega⟩, w ⟨1, by omega⟩]))
      (weightedSumSquares k
        ![-(Units.map (algebraMap ℚ k).toMonoidHom x)])) := by
    apply (baseChange_prod _ _).trans ((Equivalent.refl _).prod ?_)
    convert (baseChange_weightedSumSquares ℚ k ![-(x : ℚˣ)])
    · ext; simp [Units.smul_def]
    · ext; simp [Units.smul_def]
  apply this.symm.isotropic
  simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, neg_mul] at hx
  simp only [← represents_iff_sub_isotropic
      (nondegenerate_baseChange (nondegenerate_weightedSumSquares _)),
    represents_iff_of_rank_two (nondegenerate_baseChange
      (nondegenerate_weightedSumSquares _)) ((Pi.basisFun ℚ (Fin 2)).baseChange k),
    RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, eq_ratCast,
    Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one,
    hasseMinkoskiInv.of_baseChange_weightedSumSquares k, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [← hx, baseChange_discr, weightedSumSquares_discr]
  simp [Units.smul_def]

/-- Rank 4 case of Hasse-Minkowski. -/
lemma isotropic_of_rank_four (hr : finrank ℚ V = 4) (hQ : Q.Nondegenerate)
    (hQ' : Q.EverywhereLocallyIsotropic) : Q.Isotropic := by
  have : FiniteDimensional ℚ V := finite_of_finrank_pos (Nat.lt_of_sub_eq_sub_one hr)
  -- `Q` is equivalent to `a X₁^2 + b X₂ ^ 2 + c X₃ ^3 + d X₄^2`, for some `a b c d : ℚˣ`.
  obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate 4 (by simp [hr])
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  -- `Q1 := a X₁^2 + b X₂ ^ 2`, `Q2 := - c X₃ ^3 - d X₄^2`.
  let Q1 : QuadraticForm ℚ (Fin 2 → ℚ) := weightedSumSquares ℚ ![w 0, w 1]
  let Q2 : QuadraticForm ℚ (Fin 2 → ℚ) := weightedSumSquares ℚ ![-w 2, -w 3]
  have heq : Q.Equivalent (Q1.prod (-Q2)) := hw.trans (weightedSumSquares_equiv_prod w)
  -- Since `Q` is equivalent to `Q1.prod (-Q2)`, it suffices to prove that the latter is isotropic.
  apply (hw.trans (weightedSumSquares_equiv_prod w)).symm.isotropic
  -- Equivalently, there exists `x : ℚ` represented by both `Q1` and `Q2`.
  rw [prod_isotropic_iff (nondegenerate_weightedSumSquares _) (nondegenerate_weightedSumSquares _)]
  -- For all `p`, there exists `xₚ : ℚ_[p]` represented by both `Q1` and `Q2`.
  have hp (p : ℕ) [Fact (Nat.Prime p)] : ∃ xₚ : ℚ_[p]ˣ, (Q1.baseChange ℚ_[p]).represents xₚ.1 ∧
      (Q2.baseChange ℚ_[p]).represents xₚ.1 := by
    rw [← prod_isotropic_iff (nondegenerate_baseChange (nondegenerate_weightedSumSquares _))
      (nondegenerate_baseChange (nondegenerate_weightedSumSquares _))]
    exact (baseChange_prod_neg _ _).isotropic ((heq.baseChange _).isotropic (hQ'.1 p))
  -- There exists `xr : ℝ` represented by both `Q1` and `Q2`.
  obtain ⟨xr, hxr⟩ :
      ∃ x : ℝˣ, (Q1.baseChange ℝ).represents x.1 ∧ (Q2.baseChange ℝ).represents x.1 := by
    rw [← prod_isotropic_iff (nondegenerate_baseChange (nondegenerate_weightedSumSquares _))
      (nondegenerate_baseChange (nondegenerate_weightedSumSquares _))]
    exact (baseChange_prod_neg _ _).isotropic ((heq.baseChange ℝ).isotropic hQ'.2)
  -- For all prime `p`, we have `(xₚ, - ab)ₚ = (a, b)ₚ` and `(xₚ, - cd)ₚ = (-c, -d)ₚ`
  have hp' (p : ℕ) [Fact (Nat.Prime p)] :
      hilbertSym (hp p).choose.1 (-w 0 * w 1) = hilbertSym (w 0 : ℚ_[p]) (w 1) ∧
        hilbertSym (hp p).choose.1 (-(w 2) * w 3) = hilbertSym (-w 2 : ℚ_[p]) (-w 3) := by
    have h1 : (Q1.baseChange ℚ_[p]).represents (hp p).choose := (hp p).choose_spec.1
    have h2 : (Q2.baseChange ℚ_[p]).represents (hp p).choose := (hp p).choose_spec.2
    rw [represents_iff_of_rank_two (nondegenerate_baseChange
      (nondegenerate_weightedSumSquares _)) ((Pi.basisFun ℚ (Fin 2)).baseChange ℚ_[p])] at h1 h2
    · simp only [hasseMinkoskiInv.of_baseChange_weightedSumSquares ℚ_[p], Fin.zero_eta,
        Fin.isValue, Matrix.cons_val_zero, eq_ratCast, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Units.val_neg, Rat.cast_neg] at h1 h2
      refine ⟨?_, ?_⟩
      · simp [← h1, baseChange_discr, weightedSumSquares_discr, Units.smul_def]
      · simp [← h2, baseChange_discr, weightedSumSquares_discr, Units.smul_def]
  -- `(xr, - ab)_∞ = (a, b)_∞` and `(xr, - cd)_∞ = (-c, -d)_∞`
  have hxr' : hilbertSym xr.1 (-(w 0) * w 1) = hilbertSym ((w 0) : ℝ) (w 1) ∧
      hilbertSym xr.1 (-(w 2) * w 3) =hilbertSym (-w 2 : ℝ) (-w 3) := by
    have h1 : (Q1.baseChange ℝ).represents xr := hxr.1
    have h2 : (Q2.baseChange ℝ).represents xr := hxr.2
    rw [represents_iff_of_rank_two (nondegenerate_baseChange
      (nondegenerate_weightedSumSquares _)) ((Pi.basisFun ℚ (Fin 2)).baseChange ℝ)] at h1 h2
    · simp only [hasseMinkoskiInv.of_baseChange_weightedSumSquares ℝ, Fin.zero_eta,
        Fin.isValue, Matrix.cons_val_zero, eq_ratCast, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Units.val_neg, Rat.cast_neg] at h1 h2
      refine ⟨?_, ?_⟩
      · simp [← h1, baseChange_discr, weightedSumSquares_discr, Units.smul_def]
      · simp [← h2, baseChange_discr, weightedSumSquares_discr, Units.smul_def, mul_comm]
  -- There exists `x : ℚ` with `(xₚ, - ab)ᵥ = (a, b)ᵥ` and `(xₚ, - cd)ᵥ = (-c, -d)ᵥ`
  -- for each place `v`.
  obtain ⟨x, hx⟩ : ∃ (x : ℚˣ), (∀ (p : Nat.Primes),
      hilbertSym (x : ℚ_[p]) (-(w 0) * w 1) = hilbertSym (w 0 : ℚ_[p]) (w 1) ∧
      hilbertSym (x : ℚ_[p]) (-(w 2) * w 3) = hilbertSym (-w 2 : ℚ_[p]) (-w 3)) ∧
      hilbertSym (x : ℝ) (-(w 0) * w 1) = hilbertSym (w 0 : ℝ) (w 1) ∧
      hilbertSym (x : ℝ) (-(w 2) * w 3) = hilbertSym (-w 2 : ℝ) (-w 3) := by
    have := exists_rat_with_two_prescribed_hilbertSym
      (ep := fun p ↦ hilbertSym ((w 0) : ℚ_[p]) (w 1))
      (ep' := fun p ↦ hilbertSym ((-w 2): ℚ_[p]) (-w 3))
      (er := hilbertSym (w 0 : ℝ) (w 1)) (er' := hilbertSym (-w 2 : ℝ ) (-w 3))
      (-(w 0) * w 1) (-(w 2) * w 3)
      (by aesop (add norm eq_one_or_neg_one_of_ne_zero))
      (by aesop (add norm eq_one_or_neg_one_of_ne_zero))
      (by aesop (add norm eq_one_or_neg_one_of_ne_zero))
      (by aesop (add norm eq_one_or_neg_one_of_ne_zero))
    simp only [neg_mul, Units.val_neg, Units.val_mul, Rat.cast_neg,
      Rat.cast_mul] at this ⊢ hxr' hp'
    rw [this]
    refine ⟨⟨almost_all_one _ _, almost_all_one (-w ⟨2, by omega⟩) (-w ⟨3, by omega⟩)⟩,
      ⟨prod_eq_one _ _, ?_⟩, fun p ↦ ⟨(hp p).choose, hp' p⟩ , ⟨xr, hxr'⟩⟩
    exact_mod_cast prod_eq_one (-w ⟨2, by omega⟩) (-w ⟨3, by omega⟩)
  -- We conclude by showing that `x` is represented by `Q1` and `Q2`.
  refine ⟨x, ?_, ?_⟩
  · rw [represents_iff_sub_isotropic (nondegenerate_weightedSumSquares _)]
    exact isotropic_of_rank_three _ (by simp) (nondegenerate_prod
      (nondegenerate_weightedSumSquares _) (nondegenerate_weightedSumSquares _))
      ⟨fun p _ ↦ isotropic_prod_neg (hx.1 ⟨p, Fact.out⟩).1, isotropic_prod_neg hx.2.1⟩
  · rw [represents_iff_sub_isotropic (nondegenerate_weightedSumSquares _)]
    apply isotropic_of_rank_three _ (by simp) (nondegenerate_prod
      (nondegenerate_weightedSumSquares _) (nondegenerate_weightedSumSquares _))
    refine ⟨fun p _ ↦ ?_, ?_⟩
    · apply isotropic_prod_neg (w := ![-w ⟨2, by omega⟩, -w ⟨3, by omega⟩])
      convert (hx.1 ⟨p, Fact.out⟩).2 using 1 <;> simp
    · apply isotropic_prod_neg (w := ![-w ⟨2, by omega⟩, -w ⟨3, by omega⟩])
      convert hx.2.2 using 1 <;> simp

end QuadraticForm.EverywhereLocallyIsotropic
