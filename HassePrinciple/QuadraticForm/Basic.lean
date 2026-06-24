/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct

/-! # Quadratic forms -/

@[expose] public section

namespace QuadraticMap

section Represents

section CommSemiring

variable {R M₁ M₂ N : Type*} [CommSemiring R] [AddCommMonoid M₁] [Module R M₁]
  [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid N] [Module R N]

/-- A quadratic form is isotropic if it vanishes on some nonzero vector. -/
abbrev Isotropic (Q : QuadraticMap R M₁ N) := ¬ Q.Anisotropic

/-- `Q : QuadraticMap R M N` represents `n : N` if there exists a nonzero `x : V` such that
  `Q x = 0`. -/
def represents (Q : QuadraticMap R M₁ N) (n : N) : Prop :=
  ∃ x : M₁, Q x = n ∧ x ≠ 0

variable {Q : QuadraticMap R M₁ N} {Q' : QuadraticMap R M₂ N}

lemma represents_zero_iff_isotropic :
    Q.represents 0 ↔ Q.Isotropic := by simp [Isotropic, Anisotropic, represents]

lemma Equivalent.represents (h : Q.Equivalent Q') {n : N} (hQ : Q.represents n) :
    Q'.represents n := by
  rcases h with ⟨f⟩
  rcases hQ with ⟨x, hxQ, hx0⟩
  exact ⟨f.toFun x, by simp [hxQ, hx0]⟩

lemma Equivalent.represents_iff (h : Q.Equivalent Q') (n : N) :
    Q.represents n ↔ Q'.represents n :=
  ⟨fun hQ ↦ h.represents hQ, fun hQ ↦ h.symm.represents hQ⟩

lemma Equivalent.isotropic (h : Q.Equivalent Q') (hQ : Q.Isotropic) :
    Q'.Isotropic := by
  rw [← represents_zero_iff_isotropic] at hQ ⊢
  exact Equivalent.represents h hQ

lemma Equivalent.isotropic_iff (h : Q.Equivalent Q') :
    Q.Isotropic ↔ Q'.Isotropic :=
  ⟨fun hQ ↦ h.isotropic hQ, fun hQ ↦ h.symm.isotropic hQ⟩

end CommSemiring

section CommRing

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

lemma nondegenerate_of_anisotropic [Invertible (2 : R)] {Q : QuadraticMap R M N}
    (hQ : Q.Anisotropic) : Q.Nondegenerate := by
  rw [nondegenerate_iff_radical_eq_bot, eq_bot_iff]
  exact fun m hm ↦ hQ m (mem_radical_iff'.mp hm).1

open QuadraticMap

-- The rank zero case of Hasse-Minkowski will follow trivially from this lemma:
lemma anisotropic_of_rank_zero [IsDomain R] [StrongRankCondition R] [Module.Finite R M]
    [Module.IsTorsionFree R M] (hr : Module.finrank R M = 0) (Q : QuadraticMap R M N) :
    Q.Anisotropic := by
  rw [Module.finrank_zero_iff] at hr
  exact fun x _ ↦ Subsingleton.eq_zero x

-- The rank one case of Hasse-Minkowski will follow from:
lemma anisotropic_of_rank_one [IsDomain R] [StrongRankCondition R] [Module.IsTorsionFree R M]
    (hr : Module.finrank R M = 1) {Q : QuadraticMap R M N} (hQ : Q ≠ 0) :
    Q.Anisotropic := by
  sorry

end CommRing

end Represents

section WeightedSumSquares

variable {S R ι : Type*} [Monoid S] [CommSemiring R] [Fintype ι]
  [DistribMulAction S R] [SMulCommClass S R R] {w w' : ι → Sˣ}

lemma mul_unit_isotropic {a : Sˣ} (h : ∀ (i : ι), w' i = a * w i) :
    (weightedSumSquares R w').Isotropic → (weightedSumSquares R w).Isotropic := by
  contrapose!
  intro hw x h0
  simp only [weightedSumSquares_apply, h, mul_smul, ← Finset.smul_sum, smul_eq_zero_iff_eq] at h0
  simp only [Anisotropic, weightedSumSquares_apply] at hw
  exact hw x h0

lemma mul_unit_isotropic_iff {a : Sˣ} (h : ∀ (i : ι), w' i = a * w i) :
    (weightedSumSquares R w).Isotropic ↔ (weightedSumSquares R w').Isotropic :=
  ⟨mul_unit_isotropic (by simp[h]: ∀ (i : ι), w i = a⁻¹ * w' i), mul_unit_isotropic h⟩

end WeightedSumSquares

end QuadraticMap

namespace QuadraticForm

lemma degenerate_baseChange {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M]
    [Module R M] [Invertible (2 : R)] {Q : QuadraticForm R M}
    (hQ : ¬ Q.Nondegenerate) :
    ¬ (Q.baseChange A).Nondegenerate := by
  sorry

section Field

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

section NormalizedWeightedSumSquares

open Module _root_.QuadraticMap

variable [Invertible (2 : K)] [FiniteDimensional K V] [NeZero (Module.finrank K V)]

theorem isotropic_iff_weightedSumSquares_units_of_nondegenerate {Q : QuadraticForm K V}
    (hQ : Q.Nondegenerate) :
    ∃ (w : Fin (finrank K V) → Kˣ), w (0 : Fin (finrank K V)) = 1 ∧
      (Q.Isotropic ↔ (weightedSumSquares K w).Isotropic) := by
  obtain ⟨w₀, hw₀⟩ := equivalent_weightedSumSquares_units_of_nondegenerate' Q
    (nondegenerate_associated_iff.mpr hQ).1
  let w₁ : Fin (finrank K V) → Kˣ := fun i => w₀ 0 * w₀ i
  let w : Fin (finrank K V) → Kˣ := fun i => w₁ i / (w₀ 0) ^ 2
  refine ⟨w, by simp [w, w₁, pow_two], ?_⟩
  have hw₁ : (weightedSumSquares K w₁).Equivalent (weightedSumSquares K w) :=
    ⟨isometryEquivWeightedSumSquaresWeightedSumSquares (w := fun i ↦ (w₁ i : K))
      (fun i ↦ (w₀ 0)) (by simp [w])⟩
  rw [hw₀.isotropic_iff, mul_unit_isotropic_iff (w' := fun i ↦ w₀ 0 * w₀ i) (a := w₀ 0) (by simp),
    hw₁.isotropic_iff]

theorem isotropic_iff_weightedSumSquares_squarefree_units_of_nondegenerate {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] [NeZero (Module.finrank ℚ V)]
    {Q : QuadraticForm ℚ V} (hQ : Q.Nondegenerate) :
    ∃ (w : Fin (finrank ℚ V) → ℤ), w (0 : Fin (finrank ℚ V)) = 1 ∧
      ∀ n, w n ≠ 0 ∧ Squarefree (w n) ∧
      (Q.Isotropic ↔ (weightedSumSquares ℚ w).Isotropic) := by
  sorry

end NormalizedWeightedSumSquares

-- Condition (ii) seems annoying to state, can we avoid it?
lemma represents_iff_sub_isotropic {Q : QuadraticForm K V} (hQ : Q.Isotropic)
    (hQ' : Q.Nondegenerate) (r : Kˣ) :
    Q.represents r ↔
      (Q.prod (QuadraticMap.weightedSumSquares K ![-r])).Isotropic := sorry

lemma prod_isotropic_iff {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) {Q' : QuadraticForm K W}
    (hQ' : Q'.Nondegenerate) :
    (Q.prod Q').Isotropic ↔ ∃ r : Kˣ, Q.represents r ∧ Q'.represents r := sorry

lemma prod_isotropic_iff' {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) {Q' : QuadraticForm K W}
    (hQ' : Q'.Nondegenerate) :
    (Q.prod Q').Isotropic ↔ ∃ r : Kˣ,
      (Q.prod (QuadraticMap.weightedSumSquares K ![-r])).Isotropic ∧
      (Q'.prod (QuadraticMap.weightedSumSquares K ![-r])).Isotropic := sorry

end Field

section Hyperbolic

open Module

section CommRing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

-- If needed for any particular result, replace `[CommRing R]` by `[Field R]`.

/-- A quadratic form is hyperbolic if it is equivalent to the form X^2 - Y^2. -/
def IsHyperbolic (Q : QuadraticForm R V) : Prop :=
  Q.Equivalent (QuadraticMap.weightedSumSquares R ![1, -1])

/-- The quadratic form `XY` on a two dimensional free `R`-module. -/
noncomputable abbrev XY (b : Basis (Fin 2) R V) : QuadraticForm R V where
  toFun v := b.repr v 0 * b.repr v 1
  toFun_smul r v := sorry
  exists_companion' := by
    let B : LinearMap.BilinMap R V R := {
      toFun v := {
        toFun w := b.repr v 0 * b.repr w 1 + b.repr w 0 * b.repr v 1
        map_add' v w := sorry
        map_smul' := sorry
      }
      map_add' w z := sorry
      map_smul' r w := sorry
    }
    exact ⟨B, by sorry⟩

lemma XY_isHyperbolic (b : Basis (Fin 2) R V) :
    IsHyperbolic (XY b) := sorry

lemma equivalent_hyperbolic_add {Q : QuadraticForm R V} (hQ : Q.Isotropic)
    (hQ' : Q.Nondegenerate) (r : R) :
    ∃ (A B : QuadraticForm R V), A.IsHyperbolic ∧ Q.Equivalent (A + B) := sorry

lemma represents_of_isotropic_of_nondegenerate {Q : QuadraticForm R V} (hQ : Q.Isotropic)
    (hQ' : Q.Nondegenerate) (r : R) :
    Q.represents r := sorry

end CommRing

end Hyperbolic

section Discr

variable {R M n : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]
  [Fintype n] [DecidableEq n] (b : Module.Basis n R M) {Q : QuadraticForm R M}

lemma nondegenerate_iff_discr_ne_zero [IsDomain R] :
    Q.Nondegenerate ↔ Q.discr b ≠ 0 := by
  sorry

end Discr

end QuadraticForm
