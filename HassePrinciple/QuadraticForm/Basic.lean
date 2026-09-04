/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández, Chi-Yun Hsu
-/
module

public import HassePrinciple.ForMathlib.LinearAlgebra.BilinearForm.TensorProduct
public import HassePrinciple.ForMathlib.LinearAlgebra.LinearIndependent.Basis
public import HassePrinciple.ForMathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Quadratic forms -/

@[expose] public section

universe u
namespace QuadraticForm

open _root_.QuadraticMap in
theorem equivalent_weightedSumSquares_units_of_nondegenerate {K V : Type*} [Field K]
    [Invertible (2 : K)] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (hn : Module.finrank K V = n) {Q : QuadraticForm K V}
    (hQ : LinearMap.SeparatingLeft (associated Q)) :
    ∃ w : Fin n → Kˣ, Equivalent Q (QuadraticMap.weightedSumSquares K w) := by
  subst hn
  exact equivalent_weightedSumSquares_units_of_nondegenerate' Q hQ

-- TODO: add section variables (after Mathlib PR)

/-- The product of two quadratic forms. -/
abbrev prod {R M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁]
    [Module R M₂] (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) : QuadraticForm R (M₁ × M₂) :=
  QuadraticMap.prod Q₁ Q₂

/-- Specialization of `QuadraticMap.restrict` to `QuadraticForm`, to allow for dot notation. -/
abbrev restrict {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (Q : QuadraticForm R M) (U : Submodule R M) : QuadraticForm R U := QuadraticMap.restrict Q U

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

/-- This generalizes Mathlib's `weightedSumSquaresCongr`. -/
def weightedSumSquaresCongr' {ι κ S R : Type*} [Fintype ι] [Fintype κ] [CommSemiring R]
    [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    {w : ι → S} {w' : κ → S} (f : ι ≃ κ) (h : w = w'.comp f) :
    (weightedSumSquares R w).IsometryEquiv (weightedSumSquares R w') where
  toFun m k := m (f.symm k)
  map_add' m n  := by ext; simp
  map_smul' r m := by ext; simp
  invFun m i    := m (f i)
  left_inv m    := by simp
  right_inv m   := by simp
  map_app' m    := by
    simp only [QuadraticMap.weightedSumSquares_apply, h, Function.comp_apply]
    exact Finset.sum_equiv f.symm (by simp) (by simp)

lemma weightedSumSquaresCongr'_equivalent {ι κ S R : Type*} [Fintype ι] [Fintype κ] [CommSemiring R]
    [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    {w : ι → S} {w' : κ → S} (f : ι ≃ κ) (h : w = w'.comp f) :
    (weightedSumSquares R w).Equivalent (weightedSumSquares R w') := ⟨weightedSumSquaresCongr' f h⟩

open Module _root_.QuadraticMap

lemma discr_reindex {R M : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]
    {ι κ : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (b : Basis ι R M) (Q : QuadraticForm R M) :
    Q.discr (b.reindex e) = Q.discr b := by
  simp only [discr, Matrix.det_apply]
  rw [Finset.sum_equiv (t := Finset.univ) (e.equivCongr e) (by simp)]
  intro g _
  simp only [Equiv.equivCongr_apply_apply, toMatrix, LinearMap.toMatrix₂_apply,
    associated_apply, End.smul_def, half_moduleEnd_apply_eq_half_smul, smul_eq_mul,
    Basis.coe_reindex, Function.comp_apply, Equiv.symm_apply_apply]
  rw [Equiv.Perm.sign_eq_sign_of_equiv g ((e.equivCongr e) g) e (by intro i; simp),
    Finset.prod_equiv (t := Finset.univ) e (by simp)]
  simp

lemma IsometryEquiv.discr {R M N : Type*} [CommRing R] [Invertible (2 : R)]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {ι κ : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (b₁ : Basis ι R M) (b₂ : Basis κ R N) {Q₁ : QuadraticForm R M}
    {Q₂ : QuadraticForm R N} (f : Q₁.IsometryEquiv Q₂) :
    Q₁.discr b₁ = Q₂.discr b₂ * (f.toLinearEquiv.toMatrix (b₁.reindex e) b₂).det ^ 2 := by
  rw [← Q₁.discr_reindex e b₁]
  have hcomp : Q₁ = Q₂.comp f := by ext; simp
  simp [QuadraticForm.discr, hcomp, toMatrix_comp (b₁.reindex e) b₂ _ (f.toLinearEquiv : M →ₗ[R] N)]
  ring

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

open Module

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

open Module QuadraticMap Submodule

-- The rank zero case of Hasse-Minkowski will follow trivially from this lemma:
lemma anisotropic_of_rank_zero [IsDomain R] [StrongRankCondition R] [Module.Finite R M]
    [IsTorsionFree R M] (hr : finrank R M = 0) {Q : QuadraticMap R M N} :
    Q.Anisotropic := by
  rw [finrank_zero_iff] at hr
  exact fun x _ ↦ Subsingleton.eq_zero x

-- The rank one case of Hasse-Minkowski will follow from:
/-
Proof idea: Pick `b` so that `Q(b) ≠ 0`. Let `x` be such that `Q(x) = 0`.
Then by the rank one assumption, `r • x + s • b = 0` for some `r` and `s` not both zero.
Then `s² Q(b) = Q (s • b) = Q (- r • x) = Q (r • x) = r² Q(x) = 0`.
Because `Q(b) ≠ 0` and N is torsion free, we have `s² = 0`, so `s = 0`.
Then `r • x = 0` and `r ≠ 0`. Hence `x = 0`.
-/
open Finsupp in
lemma anisotropic_of_rank_one [IsDomain R] [IsTorsionFree R M] [IsTorsionFree R N]
    (hr : finrank R M = 1) {Q : QuadraticMap R M N} (hQ : Q ≠ 0) :
    Q.Anisotropic := by
  intro x hx
  obtain ⟨b, hb⟩ : ∃ m, Q m ≠ 0 := by simpa [Q.ext_iff] using hQ
  obtain ⟨r, s, hrs, h0⟩ : ∃ (r s : R), r • x + s • b = 0 ∧ (r ≠ 0 ∨ s ≠ 0) := by
    rw [finrank, Cardinal.toNat_eq_one] at hr
    have hdep : ¬ LinearIndependent R ![x, b] :=
      fun hli ↦ (by simpa [hr] using LinearIndependent.cardinal_lift_le_rank hli)
    obtain ⟨l, hl_sum, hl_ne_zero⟩ : ∃ l, (linearCombination R ![x, b]) l = 0 ∧ l ≠ 0 := by
      simpa [linearIndependent_iff] using hdep
    refine ⟨l 0, l 1, ?_, (by contrapose! hl_ne_zero; ext i; fin_cases i <;> simp [hl_ne_zero])⟩
    simp only [linearCombination, coe_lsum, sum,
      LinearMap.coe_smulRight, LinearMap.id_coe, id_eq] at hl_sum
    rw [Finset.sum_subset (Finset.subset_univ _)
      (fun _ _ hi ↦ by rw [(notMem_support_iff).mp hi, zero_smul])] at hl_sum
    simpa [Fin.sum_univ_two] using hl_sum
  have h : s ^ 2 • Q b = 0 := by
    calc
      s ^ 2 • Q b
        = Q (s • b) := ((pow_two s).symm ▸ (Q.toFun_smul s b)).symm
      _ = Q (-r • x) := congrArg _ ((neg_smul r x).symm ▸ (eq_neg_of_add_eq_zero_right hrs))
      _ = 0 := by simp [QuadraticMap.map_smul, hx]
  simp_all

lemma isotropic_iff_zero_of_rank_one [IsDomain R] [IsTorsionFree R M] [IsTorsionFree R N]
    (hr : finrank R M = 1) {Q : QuadraticMap R M N} :
    Q.Isotropic ↔ Q = 0 :=
  ⟨fun hQ ↦ by contrapose! hQ; exact anisotropic_of_rank_one hr hQ,
    fun hQ ↦ by simp [hQ, Isotropic, Anisotropic, ← rank_pos_iff_exists_ne_zero (R := R),
      rank_eq_one_iff_finrank_eq_one.mpr hr]⟩

variable (R M N) in
lemma degenerate_zero [StrongRankCondition R] (hM : 0 < finrank R M) :
    ¬ (0 : QuadraticMap R M N).Nondegenerate := by
  intro h0
  have := h0.radical_eq_bot
  simp only [radical, zero_apply, true_and, mk_eq_bot, AddSubmonoid.mk_eq_bot, LinearMap.ext_iff,
    AddSubsemigroup.coe_set_mk,  polarBilin_apply_apply, FunLike.coe_zero, LinearMap.zero_apply]
    at this
  have : Subsingleton M := by
    apply subsingleton_of_forall_eq 0 fun m ↦ ?_
    simp [← Set.mem_singleton_iff, ← this, polar]
  linarith [finrank_eq_zero_of_subsingleton R M]

lemma two_le_finrank_of_isotropic_of_nondegenerate [IsDomain R] [StrongRankCondition R]
    [Module.Finite R M] [IsTorsionFree R M] [IsTorsionFree R N] {Q : QuadraticMap R M N}
    (hQ : Q.Isotropic) (hQ' : Q.Nondegenerate) : 2 ≤ finrank R M := by
  by_contra h
  simp only [not_le, Order.lt_two_iff, Nat.le_one_iff_eq_zero_or_eq_one] at h
  rcases h with h0 | h1
  · exact hQ (anisotropic_of_rank_zero h0)
  · exact hQ (anisotropic_of_rank_one h1 fun h0 ↦ degenerate_zero R M N (by omega) (h0 ▸ hQ'))

theorem Equivalent.nondegenerate [IsDomain R] [IsTorsionFree R M] [IsTorsionFree R M']
    [Invertible (2 : R)] {Q : QuadraticMap R M N} {Q' : QuadraticMap R M' N} (h : Q.Equivalent Q')
    (hQ : Q.Nondegenerate) : Q'.Nondegenerate := by
  rw [nondegenerate_iff_radical_eq_bot] at hQ ⊢
  have : Module.Finite R ↥Q.radical := by rw [hQ]; exact Module.Finite.bot R M
  have : Module.Finite R ↥Q'.radical := by
    obtain ⟨e⟩ := h
    rw [← e.map_radical]
    exact Module.Finite.map Q.radical e.toLinearEquiv.toLinearMap
  rw [← finrank_eq_zero, h.symm.rank_radical_eq, finrank_eq_zero]
  exact hQ

theorem Equivalent.nondegenerate_iff [IsDomain R] [IsTorsionFree R M] [IsTorsionFree R M']
    [Invertible (2 : R)] {Q : QuadraticMap R M N} {Q' : QuadraticMap R M' N} (h : Q.Equivalent Q') :
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

lemma weightedSumSquares_mul_squares_equivalent [IsScalarTower S R R] {w w' : ι → S}
    (u : ι → Sˣ) (h : ∀ i, w' i * u i ^ 2 = w i) :
    Equivalent (weightedSumSquares R w) (weightedSumSquares R w') :=
  ⟨QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares u h⟩

end WeightedSumSquares

end QuadraticMap

namespace QuadraticForm

open _root_.QuadraticMap LinearMap Submodule TensorProduct

/-
Chiyun: Added `[Module.FaithfullyFlat R A]`. Counterexample otherwise: R = ℤ, A = ℤ/3ℤ, M = ℤ,
Q : ℤ → ℤ/3ℤ given by Q(x) = x². Then Q is degenerate but Q.baseChange A is nondegenerate.
-/
lemma degenerate_baseChange {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.FaithfullyFlat R A] [AddCommGroup M] [Module R M] [Invertible (2 : R)]
    {Q : QuadraticForm R M} (hQ : ¬ Q.Nondegenerate) :
    ¬ (Q.baseChange A).Nondegenerate := by
  contrapose! hQ
  have : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  simp only [← nondegenerate_associated_iff, associated_baseChange, LinearMap.Nondegenerate,
    separatingLeft_iff_linear_nontrivial, separatingRight_iff_linear_flip_nontrivial] at hQ ⊢
  refine ⟨fun x hx ↦ (Module.FaithfullyFlat.one_tmul_eq_zero_iff R M x).mp
    (hQ.1 _ (AlgebraTensorModule.ext (by simp [hx]))), fun y hy ↦ ?_⟩
  have hy' : BilinForm.flip (associated Q) y = 0 := by simpa [hy]
  exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff R M y).mp
    (hQ.2 _ (AlgebraTensorModule.ext (by simp [hy', BilinForm.baseChange_flip])))

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
    weightedSumSquares_mul_squares_equivalent (w := fun i ↦ (w₁ i : K)) (fun i ↦ w₀ 0) (by simp [w])
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

variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The quadratic form `XY` on a two dimensional free `R`-module. -/
noncomputable abbrev XY (b : Basis (Fin 2) R V) : QuadraticForm R V where
  toFun v := b.repr v 0 * b.repr v 1
  toFun_smul r v := by simp; ring
  exists_companion' := by
    let B : LinearMap.BilinMap R V R := {
      toFun v := {
        toFun w := b.repr v 0 * b.repr w 1 + b.repr w 0 * b.repr v 1
        map_add' w z  := by simp; ring
        map_smul' r w := by simp; ring }
      map_add' w z  := by ext; simp; ring
      map_smul' r w := by ext; simp; ring }
    exact ⟨B, fun v w ↦ by simp [B]; ring⟩

/-- A quadratic form is hyperbolic if it is equivalent to the form `XY`. -/
def IsHyperbolic (Q : QuadraticForm R V) : Prop :=
  Q.Equivalent (XY (Pi.basisFun R (Fin 2)))

lemma XY_isHyperbolic (b : Basis (Fin 2) R V) : IsHyperbolic (XY b) := ⟨{
  toLinearEquiv := b.equivFun
  map_app' v := by simp }⟩

lemma _root_.QuadraticMap.Equivalent.isHyperbolic {Q : QuadraticForm R V} {Q' : QuadraticForm R W}
    (hQ : Q.IsHyperbolic) (heq : Q'.Equivalent Q) : Q'.IsHyperbolic :=
  heq.trans hQ

theorem represents_of_isHyperbolic [Nontrivial R] {Q : QuadraticForm R V} (hQ : Q.IsHyperbolic)
    (r : R) : represents Q r := by
  apply hQ.symm.represents
  simp only [represents, QuadraticMap.coe_mk, Fin.isValue, Pi.basisFun_repr, ne_eq]
  exact ⟨![r, 1], by simp, by simp [one_ne_zero]⟩

theorem restrict_isHyperbolic_of_polar [IsDomain R] [Module.Free R V] {Q : QuadraticForm R V}
    {x y : V} (hx0 : x ≠ 0) (hQx : Q x = 0) (hQy : Q y = 0) (hQxy : polar Q x y = 1) :
    (Q.restrict (span R {x, y})).IsHyperbolic := by
  have hxy : LinearIndependent R ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h0 : a = 0 ∨ b = 0 := by
      have h : Q (a • x + b • y) = 0 := by rw [hab, map_zero]
      simpa [QuadraticMap.map_add, QuadraticMap.map_smul, hQx, hQy, hQxy, Or.comm] using h
    aesop
  apply Equivalent.trans ?_ (XY_isHyperbolic (basisSpanPair hxy))
  exact ⟨{
    toLinearEquiv := LinearEquiv.ofEq _ _ rfl
    map_app' v := by
      simp only [LinearEquiv.ofEq_rfl, LinearEquiv.refl_toLinearMap, AddHom.toFun_eq_coe,
        coe_toAddHom, id_coe, id_eq, QuadraticMap.coe_mk, Fin.isValue,
        QuadraticMap.restrict_apply]
      conv_rhs => rw [← basisSpanPair_add_repr hxy v]
      simp [QuadraticMap.map_add, QuadraticMap.map_smul, hQx, hQy, hQxy, mul_comm] }⟩

/-- The orthogonal complement of `S : Set V` with respect to the quadratic form `Q` is the
`R`-submodule of `V` consisting of elements that are `Q`-orthogonal to every `s : S`.

Note that if `S` contains isotropic elements, then `S ∩ (Q.orthoCompl S)` may be nontrivial.
-/
@[simps]
def orthoCompl (Q : QuadraticForm R V) (S : Set V) : Submodule R V where
  carrier := {v : V | ∀ (w : S), Q.IsOrtho v w}
  add_mem' {v v'} hv hv' := by simp_all [Q.isOrtho_def, QuadraticMap.map_add]
  zero_mem' := by simp [Q.isOrtho_def]
  smul_mem' r v hrv := by simp_all [Q.isOrtho_def, QuadraticMap.map_add]

lemma mem_orthoCompl (Q : QuadraticForm R V) (S : Set V) (v : V) :
    v ∈ Q.orthoCompl S ↔ ∀ (w : S), Q.IsOrtho v w := by
  simp [orthoCompl]

/-- Given a quadratic form `Q` and an `R`-submodule `S` of `V`, `Q.toDual S` is the linear map
  `V →ₗ[R] Module.Dual R S` sending `v : V` to the `R`-linear map `s ↦ polar Q v s`. -/
def toDual (Q : QuadraticForm R V) (S : Submodule R V) :
    V →ₗ[R] Module.Dual R S where
  toFun v :=
  { toFun s   := polar Q v s
    map_add'  := by simp
    map_smul' := by simp }
  map_add' v s  := by ext; simp
  map_smul' r v := by ext; simp

lemma orthoCompl_eq_ker_toDual (Q : QuadraticForm R V) (S : Submodule R V) :
    Q.orthoCompl S = (Q.toDual S).ker := by
  ext v
  simp [mem_orthoCompl, toDual, LinearMap.ext_iff, Q.isOrtho_def, polar, sub_eq_iff_eq_add']

variable [Invertible (2 : R)] (b : Basis (Fin 2) R V)

/-- IsometryEquiv between `XY b` and `(weightedSumSquares R ![(1 : Rˣ), -1])`. -/
noncomputable def xyIsometryEquivSumSquares :
    IsometryEquiv (XY b) (weightedSumSquares R ![(1 : Rˣ), -1]) :=
  { __ := b.equivFun.trans (!![⅟2, ⅟2; -⅟2, ⅟2].toLinearEquiv (Pi.basisFun R (Fin 2))
          (by have : ⅟(2 : R) * ⅟2 + ⅟2 * ⅟2 = ⅟2 := by simp [← mul_two, mul_assoc]
              simp [this, isUnit_of_invertible ⅟(2 : R)]))
    map_app' v := by
      have : 4 * ⅟(2 : R) ^ 2  = 1 := by
        rw [← two_add_two_eq_four, ← mul_two, pow_two, mul_mul_mul_comm]
        simp
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, AddHom.toFun_eq_coe, coe_toAddHom,
        LinearEquiv.coe_coe, LinearEquiv.trans_apply, Basis.equivFun_apply,
        Matrix.toLinearEquiv_apply, Matrix.toLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_fin_one, Pi.basisFun_repr, Fin.sum_univ_two, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Pi.basisFun_apply, neg_mul,
        weightedSumSquares_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
        mul_one, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero,
        one_smul, one_ne_zero, zero_add, Units.neg_smul, QuadraticMap.coe_mk]
      ring_nf
      simp [mul_comm _ (4 : R), ← mul_assoc, this] }

lemma Xsq_sub_Ysq_isHyperbolic : IsHyperbolic (weightedSumSquares R ![(1 : Rˣ), -1]) := by
  simp only [IsHyperbolic, Nat.succ_eq_add_one, Nat.reduceAdd]
  exact Nonempty.intro (xyIsometryEquivSumSquares (Pi.basisFun R (Fin 2))).symm

lemma equivalent_Xsq_sub_Ysq_of_isHyperbolic {Q : QuadraticForm R V} (hQ : Q.IsHyperbolic) :
    Q.Equivalent (weightedSumSquares R ![(1 : Rˣ), -1]) :=
  hQ.trans Xsq_sub_Ysq_isHyperbolic.symm

end CommRing

section Field

variable {K V : Type*} [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]

lemma IsHyperbolic.nondegenerate {Q : QuadraticForm K V} (hQ : Q.IsHyperbolic) :
    Q.Nondegenerate :=
  (equivalent_Xsq_sub_Ysq_of_isHyperbolic hQ).nondegenerate_iff.mpr
    (nondegenerate_weightedSumSquares _)

lemma radical_eq_orthoCompl_top (Q : QuadraticForm K V) :
    Q.radical = (Q.orthoCompl ⊤) := by
  ext v
  simp only [mem_radical_iff', Set.top_eq_univ, mem_orthoCompl, QuadraticMap.isOrtho_def,
    Subtype.forall, Set.mem_univ, forall_const]
  refine ⟨fun ⟨h0, h⟩ ↦ by simp [h, h0], fun h ↦ ?_⟩
  have h0 : Q v = 0 := by
    have h2 : ¬ (2 : K) * 2 = 2 := by field_simp; grind
    specialize h v
    simpa [← two_smul K v, QuadraticMap.map_smul, ← two_mul, h2] using h
  simp [h0, h]

lemma radical_restrict_eq_inf (Q : QuadraticForm K V) (S : Submodule K V) :
    map S.subtype (Q.restrict S).radical = (S ⊓ (Q.orthoCompl S)) := by
  rw [radical_eq_orthoCompl_top]
  ext v
  simp [mem_orthoCompl]
  simp [QuadraticMap.isOrtho_def]

section Finite

variable [Module.Finite K V] {Q : QuadraticForm K V}

lemma nondegenerate_iff_toDual_bijective : Q.Nondegenerate ↔ Function.Bijective (Q.toDual ⊤) := by
  have hinj : Function.Bijective (Q.toDual ⊤) ↔ Function.Injective (Q.toDual ⊤) := by
    rw [Function.Bijective, LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)]
    simp
  simp [hinj, nondegenerate_iff_radical_eq_bot, ← ker_eq_bot, Q.radical_eq_orthoCompl_top,
    ← orthoCompl_eq_ker_toDual]

lemma toDual_surjective (hQ : Q.Nondegenerate) (S : Submodule K V) :
    Function.Surjective (Q.toDual S) := by
  have : Q.toDual S = LinearMap.comp (dualMap (inclusion (by simp))) (Q.toDual ⊤) := by
    ext v s
    simp [toDual]
  simp only [this, LinearMap.comp, LinearMap.coe_mk, AddHom.coe_mk]
  exact (LinearMap.dualMap_surjective_iff.mpr (inclusion_injective (by simp))).comp
    (nondegenerate_iff_toDual_bijective.mp hQ).surjective

lemma finrank_eq_add (hQ : Q.Nondegenerate) (S : Submodule K V) :
    finrank K V = finrank K S + finrank K (Q.orthoCompl S) := by
  rw [← LinearMap.finrank_range_add_finrank_ker (Q.toDual S), ← orthoCompl_eq_ker_toDual,
    Nat.add_right_cancel_iff, (Q.toDual S).range_eq_top_of_surjective (toDual_surjective hQ S),
    finrank_top, Subspace.dual_finrank_eq]

lemma orthoCompl_orthoCompl (hQ : Q.Nondegenerate) (S : Submodule K V) :
    (Q.orthoCompl (Q.orthoCompl S)) = S := by
  have := finrank_eq_add hQ S
  rw [finrank_eq_add hQ (Q.orthoCompl S), add_comm, Nat.add_right_cancel_iff] at this
  rw [eq_comm]
  apply eq_of_le_of_finrank_eq _ this.symm
  intro s hs
  simp only [coe_orthoCompl, SetLike.coe_sort_coe, Subtype.forall, mem_orthoCompl,
    Set.mem_ofPred_eq]
  intro v hv
  exact (hv s hs).symm

lemma nondegenerate_orthoCompl (hQ : Q.Nondegenerate) {S : Submodule K V}
    (hS : (Q.restrict S).Nondegenerate) : (Q.restrict (Q.orthoCompl S)).Nondegenerate := by
  have hrS := radical_restrict_eq_inf Q S
  have hrSc := radical_restrict_eq_inf Q (Q.orthoCompl S)
  rw [orthoCompl_orthoCompl hQ S, inf_comm] at hrSc
  simp only [nondegenerate_iff_radical_eq_bot] at hQ hS ⊢
  simp only [hS, Submodule.map_bot] at hrS
  simp only [← hrS, ← map_bot (Q.orthoCompl S).subtype] at hrSc
  rwa [(map_injective_of_injective (Q.orthoCompl S).injective_subtype).eq_iff] at hrSc

lemma nondegenerate_orthoCompl_iff (hQ : Q.Nondegenerate) (S : Submodule K V) :
    (Q.restrict S).Nondegenerate ↔ (Q.restrict (Q.orthoCompl S)).Nondegenerate :=
  ⟨fun hS ↦ nondegenerate_orthoCompl hQ hS,
    fun hS ↦ orthoCompl_orthoCompl hQ S ▸ nondegenerate_orthoCompl hQ hS⟩

lemma orthoCompl_isCompl (hQ : Q.Nondegenerate) {S : Submodule K V}
    (hQS : (Q.restrict S).Nondegenerate) : IsCompl S  (Q.orthoCompl S) := by
  rw [isCompl_iff_disjoint _ _ (finrank_eq_add hQ S).le, disjoint_iff, ← radical_restrict_eq_inf,
    ← map_bot S.subtype, (map_injective_of_injective S.injective_subtype).eq_iff,
    nondegenerate_iff_radical_eq_bot.mp hQS]

/-- If `Q` is a nondegenerate quadratic form, then `prodEquivOfIsCompl U (Q.orthoCompl U)` is an
  isometry. -/
noncomputable def _root_.Submodule.prodOrthoComplEquiv (hQ : Q.Nondegenerate) {U : Submodule K V}
    (hU : (Q.restrict U).Nondegenerate) :
    ((Q.restrict U).prod (Q.restrict (Q.orthoCompl U))).IsometryEquiv Q where
  __ := prodEquivOfIsCompl U (Q.orthoCompl U) (orthoCompl_isCompl hQ hU)
  map_app' v := by
    simp only [coe_prodEquivOfIsCompl, AddHom.toFun_eq_coe, coe_toAddHom, coprod_apply,
      subtype_apply, QuadraticMap.prod_apply, QuadraticMap.restrict_apply]
    have := v.2.2 v.1
    rw [Q.isOrtho_def] at this
    grind

lemma equivalent_isHyperbolic_add (hQ : Q.Isotropic) (hQ' : Q.Nondegenerate) :
    ∃ (A : QuadraticForm K (Fin 2 → K)) (B : QuadraticForm K (Fin (finrank K V - 2) → K)),
      A.IsHyperbolic ∧ Q.Equivalent (A.prod B) := by
  -- Since `Q` is isotropic, there exists a nonzero `x` with `Q x = 0`.
  simp only [Isotropic, Anisotropic, not_forall] at hQ
  obtain ⟨x, hQx, hx0⟩ := hQ
  -- Since `Q` is nondegenerate, there exists `z` with `polar Q x z = 1`.
  obtain ⟨z, hxz⟩ : ∃ (z : V), polar Q x z = 1 := by
    obtain ⟨z, hxz⟩ : ∃ (z : V), polar Q x z ≠ 0 := by
      by_contra! h
      simp only [nondegenerate_iff_radical_eq_bot, radical, mk_eq_bot, AddSubmonoid.mk_eq_bot,
        AddSubsemigroup.coe_set_mk, Set.eq_singleton_iff_unique_mem,
        Set.mem_ofPred_eq, map_zero, and_self, and_imp, true_and] at hQ'
      exact hx0 (hQ' x hQx (LinearMap.ext_iff.mpr h))
    exact ⟨(1/ (polar Q x z)) • z, by simp [inv_mul_eq_one₀ hxz]⟩
  -- `Q` vanishes at `y := z - (polar Q z z)/2 • x`, and `polar Q x y = 1`.
  let y : V := z - (2 : K)⁻¹ • (polar Q z z) • x
  have hQy : Q y = 0 := by
    simp [y, hxz, sub_eq_add_neg, QuadraticMap.map_add, QuadraticMap.map_smul, polar_comm Q z, hQx,
      ← mul_assoc]
  have hxy : polar Q x y = 1 := by
    simp only [polar, hQx, hQy]
    simp [sub_eq_add_neg, QuadraticMap.map_add Q, hQx, QuadraticMap.map_smul, QuadraticMap.map_neg,
       polar_comm Q z, hxz, y, ← mul_assoc]
  -- `x` and `y` are linearly independent.
  have hxy' : ∀ (a : K), a • x ≠ y := by
    by_contra! ha
    obtain ⟨a, hay⟩ := ha
    simp only [polar, ← hay] at hxy
    nth_rw 1 [← one_smul K x, ← add_smul] at hxy
    simp only [QuadraticMap.map_smul, hQx, smul_eq_mul, mul_zero, sub_self] at hxy
    exact one_ne_zero hxy.symm
  -- The restriction of `Q` to `span{x, y}` is hyperbolic, and `Q` is equivalent to the product
  -- of the restrictions to `span{x, y}` and its `Q`-orthogonal complement.
  let U := span K {x, y}
  have hU : finrank K U = 2 := by
    have : Fintype ({x, y} : Set V) := Fintype.ofFinite _
    rw [finrank_span_set_eq_card (linearIndepOn_id_pair hx0 hxy'), Set.toFinset_card,
      Set.fintypeCard_eq_ncard, Set.ncard_pair (by simpa [one_smul] using hxy' 1)]
  let W := Q.orthoCompl U
  have hW : finrank K W = finrank K V - 2 := by simp [finrank_eq_add hQ' U, W, hU]
  let QU : QuadraticForm K U := Q.restrict U
  let QW : QuadraticForm K W := Q.restrict W
  have hQU : QU.IsHyperbolic := restrict_isHyperbolic_of_polar hx0 hQx hQy (by simp [hxy])
  have hQU' : QU.Nondegenerate := hQU.nondegenerate
  have hprod : Q.Equivalent (QU.prod QW) := ⟨(prodOrthoComplEquiv hQ' hQU').symm⟩
  obtain ⟨wU, hwU⟩ := equivalent_weightedSumSquares_units_of_nondegenerate 2 hU
    (QU.nondegenerate_associated_iff.mpr hQU').1
  obtain ⟨wW, hwW⟩ := equivalent_weightedSumSquares_units_of_nondegenerate (finrank K V - 2) hW
    (QW.nondegenerate_associated_iff.mpr (nondegenerate_orthoCompl hQ' hQU')).1
  exact ⟨weightedSumSquares K wU, weightedSumSquares K wW, hwU.symm.isHyperbolic hQU,
    hprod.trans (hwU.prod hwW)⟩

lemma represents_of_isotropic_of_nondegenerate (hQ : Q.Isotropic) (hQ' : Q.Nondegenerate) (r : K) :
    Q.represents r := by
  obtain ⟨H, Q', hH, heq⟩ := equivalent_isHyperbolic_add hQ hQ'
  apply heq.symm.represents
  have hr : represents H r := represents_of_isHyperbolic hH r
  simp only [represents, ne_eq, QuadraticMap.prod_apply] at hr ⊢
  obtain ⟨x, hxr, hx0⟩ := hr
  exact ⟨(x, 0), by simp [hxr], by simp [hx0]⟩

end Finite

end Field

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
    {Q' : QuadraticForm R N} (b : Module.Basis ι R M) (b' : Module.Basis κ R N) :
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
    {Q' : QuadraticForm R N} (b : Module.Basis ι R M) (b' : Module.Basis κ R N) :
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
