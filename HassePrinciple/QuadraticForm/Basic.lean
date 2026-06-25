/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.ForMathlib.LinearAlgebra.BilinearForm.TensorProduct
public import HassePrinciple.ForMathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Quadratic forms -/

@[expose] public section

namespace QuadraticForm

/-- The product of two quadratic forms. -/
abbrev prod {R M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁]
    [Module R M₂] (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) : QuadraticForm R (M₁ × M₂) :=
  QuadraticMap.prod Q₁ Q₂

/-- `weightedSumSquares` as a `QuadraticForm` (TODO: update in Mathlib). -/
abbrev weightedSumSquares {S : Type*} (R : Type*) [CommSemiring R] {ι : Type*}
    [Fintype ι] [Monoid S] [DistribMulAction S R] [SMulCommClass S R R] (w : ι → S) :
    QuadraticForm R (ι → R) :=
  QuadraticMap.weightedSumSquares R w

lemma weightedSumSquares_toMatrix {S : Type*} (R : Type*) [CommRing R] [Invertible (2 : R)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid S] [DistribMulAction S R]
    [SMulCommClass S R R] (w : ι → S) :
    toMatrix (Pi.basisFun R ι) (weightedSumSquares R w) = Matrix.diagonal fun i ↦ w i • 1 := by
  ext i j
  simp only [toMatrix, LinearMap.toMatrix₂_apply, Pi.basisFun_apply, QuadraticMap.associated_apply,
    QuadraticMap.weightedSumSquares_apply, Pi.add_apply, Module.End.smul_def,
    QuadraticMap.half_moduleEnd_apply_eq_half_smul, smul_eq_mul, Matrix.diagonal_apply]
  split_ifs with hij
  · simp only [hij, Pi.single_apply, mul_ite, mul_one, mul_zero, smul_ite, smul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_eq_single j (fun _ _ hkj ↦ by simp [hkj]) (by aesop)]
    · simp only [↓reduceIte]
      ring_nf
      have h4 : (4 : R) = 2 * 2 := by ring
      rw [← mul_smul_one, mul_right_comm _ _ 2]
      simp only [h4, ← mul_assoc, invOf_mul_self', one_mul]
      ring
  · simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, smul_ite, smul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_eq_add i j hij (fun _ _ hkj ↦ by simp [hkj]) (by aesop) (by aesop)]
    simp [(Ne.symm hij), hij]

lemma weightedSumSquares_discr {S : Type*} (R : Type*) [CommRing R] [Invertible (2 : R)] {ι : Type*}
    [Fintype ι] [DecidableEq ι] [CommMonoid S] [DistribMulAction S R] [SMulCommClass S R R]
    (w : ι → S) : discr (Pi.basisFun R ι) (weightedSumSquares R w) = ∏ (i : ι), w i • 1 := by
  rw [← Matrix.det_diagonal, discr, weightedSumSquares_toMatrix]

lemma baseChange_toMatrix {R n M₁ : Type*} [Fintype n] [DecidableEq n] (A : Type*) [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [CommRing A] [Algebra R A] [Invertible (2 : R)]
    [Invertible (2 : A)] (b : Module.Basis n R M₁) {Q : QuadraticForm R M₁} :
    (Q.baseChange A).toMatrix (b.baseChange A) = (Q.toMatrix b).map (algebraMap R A) := by
  ext i j
  have h2 : algebraMap R A 2 = 2 := by
    have : (2 : R) = 1 + 1 := by ring
    simp [this]; ring
  have : Invertible ((algebraMap R A) 2) := by rw [h2]; infer_instance
  have h2' : (algebraMap R A) ⅟2 = ⅟2 := by simp [map_invOf, h2]
  have h (j) : Q (b j) • ⅟(2 : A) = ⅟2 * (Q (b j) • 1) := by simp
  simp only [toMatrix, LinearMap.toMatrix₂_apply, Module.Basis.baseChange_apply,
    QuadraticMap.associated_apply, baseChange_tmul, mul_one, Module.End.smul_def, map_sub,
    QuadraticMap.half_moduleEnd_apply_eq_half_smul, smul_eq_mul, LinearMap.map_smul_of_tower,
    Matrix.map_apply, map_mul, h2']
  congr
  · have h0 (x y) :  QuadraticMap.polar (⇑(algebraMap R A)) x y = 0 := by simp [QuadraticMap.polar]
    simp only [QuadraticMap.map_add, baseChange_tmul, mul_one,
      Algebra.algebraMap_eq_smul_one (Q (b i)), Algebra.algebraMap_eq_smul_one (Q (b j))]
    simp only [add_assoc, add_right_inj]
    rw [← QuadraticMap.polarBilin_apply_apply]
    simp [polarBilin_baseChange,  Algebra.algebraMap_eq_smul_one, h0]
  · rw [h i, Algebra.algebraMap_eq_smul_one (Q (b i))]
  · rw [h j, Algebra.algebraMap_eq_smul_one (Q (b j))]

lemma baseChange_discr {R n M₁ : Type*} [Fintype n] [DecidableEq n] (A : Type*) [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [CommRing A] [Algebra R A] [Invertible (2 : R)]
    [Invertible (2 : A)] (b : Module.Basis n R M₁) {Q : QuadraticForm R M₁} :
    (Q.baseChange A).discr (b.baseChange A) = algebraMap R A (Q.discr b) := by
  simp [discr, baseChange_toMatrix, Matrix.det_apply]

end QuadraticForm

namespace QuadraticMap

open QuadraticForm

variable {R M N P : Type*} [CommRing R] [Invertible (2 : R)]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [AddCommGroup P] [Module R P]

lemma Equivalent.baseChange (A : Type*) [CommRing A] [Algebra R A] [Invertible (2 : A)]
    {Q₁ : QuadraticForm R M} {Q₂ : QuadraticForm R N}
    (h : Q₁.Equivalent Q₂) : (Q₁.baseChange A).Equivalent (Q₂.baseChange A) := by
  obtain ⟨f⟩ := h
  use LinearEquiv.baseChange R A M N f
  intro a
  induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp
    | add x y hx hy =>
      have : (Q₂.baseChange A).polarBilin
          (((f.toLinearEquiv.baseChange R A M N)).toLinearMap x)
          ((((f.toLinearEquiv.baseChange R A M N)).toLinearMap y)) =
          (Q₁.baseChange A).polarBilin x y := by
        simp only [polarBilin_baseChange, LinearEquiv.coe_baseChange, ← LinearMap.compl₁₂_apply,
          ← LinearMap.BilinForm.baseChange_compl₁₂]
        congr
        ext m n
        simp [polar, -map_add, ← map_add f]
      simpa [polar, ← hx, ← hy] using this

-- TODO: change in Mathlib
theorem polarBilin_injective' :
    Function.Injective (polarBilin : QuadraticMap R M N → _) :=
  polarBilin_injective (isUnit_of_invertible 2)

theorem polarBilin_ext_iff {Q₁ Q₂ : QuadraticMap R M N} :
    Q₁ = Q₂ ↔ Q₁.polarBilin = Q₂.polarBilin :=
  ⟨fun h ↦ by rw [h], fun h ↦ by apply QuadraticMap.polarBilin_injective' h⟩

end QuadraticMap

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

variable {R M M' N A : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] [AddCommGroup N] [Module R N] [CommRing A] [Algebra R A]

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

theorem Equivalent.nondegenerate [IsDomain R] [Module.IsTorsionFree R M] [Module.IsTorsionFree R M']
    [Invertible (2 : R)] {Q : QuadraticMap R M N} {Q' : QuadraticMap R M' N} (h : Q.Equivalent Q')
    (hQ : Q.Nondegenerate) : Q'.Nondegenerate := by
  rw [nondegenerate_iff_radical_eq_bot] at hQ ⊢
  have : Module.Finite R ↥Q.radical := by rw [hQ]; exact Module.Finite.bot R M
  have : Module.Finite R ↥Q'.radical := by
    obtain ⟨e⟩ := h
    rw [← e.map_radical]
    exact Module.Finite.map Q.radical e.toLinearEquiv.toLinearMap
  rw [← Submodule.finrank_eq_zero, h.symm.rank_radical_eq, Submodule.finrank_eq_zero]
  exact hQ

theorem Equivalent.nondegenerate_iff [IsDomain R] [Module.IsTorsionFree R M]
    [Module.IsTorsionFree R M'] [Invertible (2 : R)] {Q : QuadraticMap R M N}
    {Q' : QuadraticMap R M' N} (h : Q.Equivalent Q') :
    Q.Nondegenerate ↔ Q'.Nondegenerate :=
  ⟨fun hQ ↦ h.nondegenerate hQ, fun hQ' ↦ h.symm.nondegenerate hQ'⟩

lemma nondegenerate_weightedSumSquares {k : Type*} [Field k] [Invertible (2 : k)] {n : ℕ}
    (w : Fin n → kˣ) : (weightedSumSquares k w).Nondegenerate := by
  have heq : (weightedSumSquares k w).Equivalent (weightedSumSquares k (fun i ↦ (w i : k))) :=
    Equivalent.refl (weightedSumSquares k w)
  apply heq.symm.nondegenerate
  simp [nondegenerate_iff_radical_eq_bot, QuadraticForm.radical_weightedSumSquares, Pi.spanSubset]

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
    [Module R M] [Invertible (2 : R)] {Q : QuadraticForm R M} (hQ : ¬ Q.Nondegenerate) :
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

theorem isotropic_iff_weightedSumSquares_squarefree_units_of_nondegenerate {V : Type*}
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] [NeZero (Module.finrank ℚ V)]
    {Q : QuadraticForm ℚ V} (hQ : Q.Nondegenerate) :
    ∃ (w : Fin (finrank ℚ V) → ℤ), w (0 : Fin (finrank ℚ V)) = 1 ∧
      ∀ n, w n ≠ 0 ∧ Squarefree (w n) ∧
      (Q.Isotropic ↔ (weightedSumSquares ℚ w).Isotropic) := by
  sorry

end NormalizedWeightedSumSquares

-- Condition (ii) seems annoying to state, can we avoid it?
lemma represents_iff_sub_isotropic {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) (r : Kˣ) :
    Q.represents r ↔
      (Q.prod (QuadraticMap.weightedSumSquares K ![-r])).Isotropic := sorry

lemma prod_isotropic_iff {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) {Q' : QuadraticForm K W}
    (hQ' : Q'.Nondegenerate) :
    (Q.prod (-Q')).Isotropic ↔ ∃ r : Kˣ, Q.represents r ∧ Q'.represents r := sorry

lemma prod_isotropic_iff' {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) {Q' : QuadraticForm K W}
    (hQ' : Q'.Nondegenerate) :
    (Q.prod (-Q')).Isotropic ↔ ∃ r : Kˣ,
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

variable {R M N P n : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  [Fintype n] [DecidableEq n] (b : Module.Basis n R M) {Q : QuadraticForm R M}

lemma nondegenerate_iff_discr_ne_zero [IsDomain R] :
    Q.Nondegenerate ↔ Q.discr b ≠ 0 := by
  sorry

/-- The base change of a nondegenerate quadratic form is nondegenerate. -/
lemma nondegenerate_baseChange [IsDomain R] [Module.Free R M] [Module.Finite R M] {A : Type*}
    [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] [Invertible (2 : A)]
    (hQ : Q.Nondegenerate) : (Q.baseChange A).Nondegenerate := by
  let b := Module.Free.chooseBasis R M
  rw [nondegenerate_iff_discr_ne_zero b] at hQ
  rw [nondegenerate_iff_discr_ne_zero (b.baseChange A), baseChange_discr,
    ← map_zero (algebraMap R A)]
  simp [hQ]

/-- Given quadratic forms `Q` and `Q'` with matrices `A` and `B` with respect to bases `b` and `b'`,
respectively, the matrix associated is the block diagonal matrix `[[A, 0], [0, B]]`. -/
theorem toMatrix_prod {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [IsDomain R] {Q' : QuadraticForm R N} (b : Module.Basis ι R M)
    (b' : Module.Basis κ R N) :
    (toMatrix (b.prod b') (Q.prod Q')) = Matrix.fromBlocks (toMatrix b Q) 0 0 (toMatrix b' Q') := by
  simp only [Matrix.ext_iff_blocks, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j; simp [Matrix.toBlocks₁₁, toMatrix]
  · ext i j; simp [Matrix.toBlocks₁₂, toMatrix]
  · ext i j; simp [Matrix.toBlocks₂₁, toMatrix]
  · ext i j; simp [Matrix.toBlocks₂₂, toMatrix]

/-- The discriminant of the product of quadratic forms is the product of the discriminants. -/
theorem discr_prod {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [IsDomain R] {Q' : QuadraticForm R N} (b : Module.Basis ι R M)
    (b' : Module.Basis κ R N) :
    discr (b.prod b') (Q.prod Q') = discr b Q * discr b' Q' := by
  simp [discr, prod, toMatrix_prod]

/-- The product of two nondegenerate quadratic forms is nondegenerate. -/
lemma nondegenerate_prod [IsDomain R] [Module.Free R M] [Module.Finite R M]
    [Module.Free R N] [Module.Finite R N] {Q' : QuadraticForm R N}
    (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate) :
    (Q.prod Q').Nondegenerate := by
  let b := Module.Free.chooseBasis R M
  let b' := Module.Free.chooseBasis R N
  rw [nondegenerate_iff_discr_ne_zero b] at hQ
  rw [nondegenerate_iff_discr_ne_zero b'] at hQ'
  rw [nondegenerate_iff_discr_ne_zero (b.prod b'), discr_prod]
  aesop

open _root_.QuadraticMap

theorem polar_weightedSumSquares {S R ι : Type*} [CommRing R] [Fintype ι]
    [Monoid S] [DistribMulAction S R] [SMulCommClass S R R] (w : ι → S) :
    polar (weightedSumSquares R w) = fun x y ↦ ∑ (i : ι), 2 * (w i) • (x i) * (y i) := by
  ext x y
  simp only [polar, weightedSumSquares_apply, Pi.add_apply, ← Finset.sum_sub_distrib, add_mul,
    mul_add, smul_add]
  apply Finset.sum_congr rfl
  intro i _
  ring_nf
  rw [mul_smul_comm, mul_comm (x i)]


end Discr

section BaseChange

open TensorProduct _root_.QuadraticMap

variable {R A M₁ M₂ : Type*} [CommRing R] [CommRing A] [Algebra R A] [Invertible (2 : R)]
  [Invertible (2 : A)] [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂]

lemma baseChange_prod (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    ((Q₁.prod Q₂).baseChange A).Equivalent ((Q₁.baseChange A).prod (Q₂.baseChange A)) :=
  ⟨TensorProduct.prodRight R A A M₁ M₂, by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul => simp [prodRight_tmul, add_smul]
    | add x y hx hy =>
      have : polar (Q₁.baseChange A) ((prodRight R A A M₁ M₂) x).1 ((prodRight R A A M₁ M₂) y).1 +
          polar (Q₂.baseChange A) ((prodRight R A A M₁ M₂) x).2 ((prodRight R A A M₁ M₂) y).2 =
          polar ((Q₁.prod Q₂).baseChange A) x y := by
        simp [← polarBilin_apply_apply, QuadraticForm.polarBilin_baseChange,
          LinearMap.BilinForm.baseChange_compl₁₂, prodRight_fst, prodRight_snd]
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        QuadraticMap.prod_apply, map_add] at hx hy ⊢
      simp only [Prod.fst_add, Prod.snd_add, QuadraticMap.map_add (Q₁.baseChange A),
        QuadraticMap.map_add (Q₂.baseChange A), QuadraticMap.map_add ((Q₁.prod Q₂).baseChange A),
        ← hx, ← hy, ← this]
      ring⟩

lemma baseChange_prod_neg (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    ((Q₁.prod (-Q₂)).baseChange A).Equivalent ((Q₁.baseChange A).prod (- Q₂.baseChange A)) := by
  apply (baseChange_prod Q₁ (-Q₂) (A := A)).trans
  convert Equivalent.refl ((Q₁.baseChange A).prod (-Q₂.baseChange A))
  ext; simp

variable (R A) in
theorem baseChange_weightedSumSquares {ι : Type*} [Fintype ι] (w : ι → R) :
    ((weightedSumSquares R w).baseChange A).Equivalent
      (weightedSumSquares A (fun i ↦ algebraMap R A (w i))) := by
  classical exact ⟨piScalarRight R A A ι, by
    have hp (x y : A ⊗[R] (ι → R)) :
      ∑ (x_1 : ι), (algebraMap R A) (w x_1) * ((piScalarRightHom R A A ι) y x_1 *
          (piScalarRightHom R A A ι) x x_1) +
          (∑ x_1, (algebraMap R A) (w x_1) * ((piScalarRightHom R A A ι) x x_1 *
          (piScalarRightHom R A A ι) y x_1)) =
            polar (⇑(QuadraticForm.baseChange A (weightedSumSquares R w))) x y := by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a x =>
          simp only [piScalarRightHom_tmul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
          induction y using TensorProduct.induction_on with
          | zero => simp
          | tmul b y =>
            simp only [piScalarRightHom_tmul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
              ← polarBilin_apply_apply, polarBilin_baseChange, LinearMap.BilinForm.baseChange_tmul]
            simp only [Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, one_mul,
              ← Finset.sum_add_distrib, polarBilin, polar_weightedSumSquares, smul_eq_mul,
              LinearMap.mk₂_apply, Finset.sum_smul]
            congr
            ext c
            simp [Algebra.smul_def, map_ofNat]
            ring
          | add b b' hb hb'  =>
            simp only [← polarBilin_apply_apply, map_add, Pi.add_apply] at *
            simp only [← hb, ← hb', ← Finset.sum_add_distrib, mul_add, smul_add]
            congr; ext c;
            simp [Algebra.smul_def]
            ring
        | add a b ha hb =>
          simp only [← polarBilin_apply_apply, map_add, Pi.add_apply, LinearMap.add_apply] at *
          simp only [← ha, ← hb, ← Finset.sum_add_distrib]
          congr; ext x; ring
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul a f =>
      simp only [Algebra.algebraMap_eq_smul_one, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
        LinearEquiv.coe_coe, piScalarRight_apply, piScalarRightHom_tmul, weightedSumSquares_apply,
        Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul, smul_eq_mul, one_mul,
        baseChange_tmul, Finset.sum_smul]
      exact Finset.sum_congr rfl (fun _ _ ↦ by ring_nf)
    | add x y hx hy =>
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        piScalarRight_apply, weightedSumSquares_apply, smul_eq_mul] at hx hy
      simp [mul_add, add_mul, smul_eq_mul, Finset.sum_add_distrib, hx, hy,
        QuadraticMap.map_add ((weightedSumSquares R w).baseChange A), ← hp x y]
      ring⟩

end BaseChange

end QuadraticForm
