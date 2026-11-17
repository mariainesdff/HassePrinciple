/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández, Chi-Yun Hsu
-/
module

public import HassePrinciple.ForMathlib.LinearAlgebra.Determinant
public import HassePrinciple.HilbertSymbol.Basic
public import HassePrinciple.HilbertSymbol.ExistenceTheorem
public import HassePrinciple.QuadraticForm.LowRank
public import HassePrinciple.QuadraticForm.Chain
public import HassePrinciple.NumberTheory.ApproximationTheorem
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Data.Fin.Basic

public import Mathlib.Data.Sym.Sym2

/-! # The Hasse-Minkowski invariant -/

@[expose] public section

section Prelim

lemma LinearMap.separatingLeft_of_equivalent {R M M' N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M'] [AddCommGroup N] [Module R N]
    [Invertible (2 : R)] {Q : QuadraticMap R M N} {Q' : QuadraticMap R M' N} (h : Q.Equivalent Q')
    (hQ : LinearMap.SeparatingLeft Q.associated) :
    LinearMap.SeparatingLeft Q'.associated := by
  obtain ⟨f, hf⟩ := h
  intro x hx
  have finvx_zero : f.symm x = 0 := by
    refine hQ _ (fun y ↦ ?_)
    simpa [QuadraticMap.associated_apply, ← hf (f.symm x + y), ← hf (f.symm x), ← hf y]
      using hx (f y)
  simpa using finvx_zero

end Prelim

theorem QuadraticForm.nondegenerate_iff_map_basis_ne_zero {R M ι : Type*}
    [CommRing R] [IsDomain R] [Invertible (2 : R)] [AddCommGroup M] [Module R M] [Finite ι]
    {Q : QuadraticForm R M} {v : Module.Basis ι R M} (hv : Q.associated.IsOrthoᵢ v) :
    Q.Nondegenerate ↔ ∀ i : ι, Q (v i) ≠ 0 := by
  refine ⟨fun hQ ↦ ?_, fun h ↦ ?_⟩
  · refine fun i hi ↦ hv.not_isOrtho_basis_self_of_separatingLeft ?_ i ?_
    · exact (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
    simpa [QuadraticMap.associated_eq_self_apply] using hi
  · rw [← QuadraticMap.nondegenerate_associated_iff]
    simp only [LinearMap.Nondegenerate]
    have := Fintype.ofFinite ι
    constructor
    all_goals
    intro x hx
    refine v.forall_coord_eq_zero_iff.mp (fun i ↦ ?_)
    have hi := hx (v i)
    rw [← v.sum_repr x] at hi
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply] at hi
    rw [Finset.sum_eq_single i] at hi
    · simpa [QuadraticMap.associated_eq_self_apply, h i] using hi
    · intro j _ hj
      simp [hv hj, hv hj.symm]
    · simp

open QuadraticForm in
theorem hilbertSym.eq_one_iff_represents_one {k : Type*} [Field k] [Invertible (2 : k)]
  {w : Fin 2 → k} (hw : w 0 ≠ 0 ∧ w 1 ≠ 0) :
    hilbertSym (w 0) (w 1) = 1 ↔ (weightedSumSquares k w).represents (1 : kˣ) := by
  have hdef : hilbertSym (w 0 : k) (w 1) = 1 ↔
      ∃ z x y : k, (z, x, y) ≠ (0, 0, 0) ∧ w 0 * x ^ 2 + w 1 * y ^ 2 - z ^ 2 = 0 := by
    simp [hilbertSym, hw]
    grind
  rw [hdef,
    (represents_iff_sub_isotropic
      ((QuadraticForm.nondegenerate_iff_map_basis_ne_zero
        (weightedSumSquares_isOrthoᵢ_basisFun w)).mpr (by simp [hw]))) 1,
    ← QuadraticMap.represents_zero_iff_isotropic]
  dsimp [QuadraticMap.represents]
  refine ⟨fun ⟨z, x, y, hne, hrep⟩ ↦
    ⟨(![x, y], ![z]), ⟨by simpa [pow_two, Units.smul_def, sub_eq_add_neg] using hrep, ?_⟩⟩,
    fun ⟨x, ⟨hrep, hne⟩⟩ ↦
    ⟨x.2 0, x.1 0, x.1 1, ?_, by simpa [pow_two, Units.smul_def, sub_eq_add_neg] using hrep⟩⟩
  · simp only [Prod.mk_eq_zero, Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_true]
    rw [and_comm]
    simpa using hne
  · contrapose hne
    simp only [Fin.isValue, Prod.mk.injEq] at hne
    ext i <;>
    fin_cases i
    · exact hne.2.1
    · exact hne.2.2
    · exact hne.1

namespace QuadraticForm

variable {k : Type*} [Field k]

-- Let `V` and `W` be `k`-vector spaces.
variable {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

-- Let `Q` be a quadratic form on `V`.
variable (Q : QuadraticForm k V)

-- Similarly defined in RankFour.lean
private noncomputable def finThreeLinearEquivProd :
    (Fin 3 → k) ≃ₗ[k] (Fin 2 → k) × (Fin 1 → k) where
  toFun x := ⟨![x 0, x 1], ![x 2]⟩
  map_add' x y  := by simp
  map_smul' r x := by simp
  invFun x a := ![x.1 0, x.1 1, x.2 0] a
  left_inv x := by ext a; fin_cases a <;> simp
  right_inv x := by ext a <;> fin_cases a <;> simp

-- Similarly proven in RankFour.lean
private theorem weightedSumSquares_equiv_prod (w : Fin 2 → kˣ) (a : kˣ) :
    (weightedSumSquares k ![w 0, w 1, a]).Equivalent
      ((weightedSumSquares k w).prod (weightedSumSquares k ![a])) :=
 ⟨finThreeLinearEquivProd, fun f ↦ by simp [finThreeLinearEquivProd, Fin.sum_univ_three]⟩

/-- Auxiliary definition for `hasseMinkowskiInv`. -/
-- CY : Changed `kˣ` to `k` to define `hasseMinkowskiInvBasis`
noncomputable def hasseMinkowskiInvAux {n : ℕ} (w : Fin n → k) : ℤ :=
  ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1) (w p.2)

lemma hasseMinkowskiInvAux_def {n : ℕ} (w : Fin n → k) :
    hasseMinkowskiInvAux w =
      ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2) := rfl

noncomputable abbrev hilbertSym_Sym2 {n : ℕ} (w : Fin n → k) (z : Sym2 (Fin n)) : ℤ :=
  Sym2.lift ⟨fun i j ↦ hilbertSym (w i) (w j), by simp [hilbertSym.comm]⟩ z

lemma hasseMinkowskiInvAux_Sym2 {n : ℕ} (w : Fin n → k) :
    hasseMinkowskiInvAux w = ∏ z : Sym2 (Fin n) with ¬z.IsDiag, hilbertSym_Sym2 w z := by
  refine Finset.prod_bij (fun p _ ↦ s(p.1, p.2)) ?_ ?_ ?_ (by simp)
  · -- lands in the non-diagonal part
    rintro ⟨i, j⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    simpa [Sym2.mk_isDiag_iff] using hp.ne
  · -- injective
    rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij hij'
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h ⊢
    rcases h with h1 | h2
    · exact h1
    · rw [h2.1, h2.2] at hij
      exact absurd hij (lt_asymm hij')
  · -- surjective
    intro z
    refine Sym2.ind (fun i j ↦ ?_) z
    simp only [Finset.mem_filter, Finset.mem_univ, Sym2.mk_isDiag_iff, true_and, Sym2.eq,
      Prod.mk.eta, Sym2.rel_iff', Prod.swap_prod_mk, exists_prop, Prod.exists, Prod.mk.injEq]
    intro hij
    rcases lt_trichotomy i j with h | h | h
    · exact ⟨i, j, by simp [h]⟩
    · contradiction
    · exact ⟨j, i, by simp [h]⟩

-- PR 43815
def _root_.Equiv.sym2Congr {α β : Type*} (e : α ≃ β) : Sym2 α ≃ Sym2 β where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv x := by
    rw [Sym2.map_map, Equiv.symm_comp_self, Sym2.map_id, id_eq]
  right_inv x := by
    rw [Sym2.map_map, Equiv.self_comp_symm, Sym2.map_id, id_eq]

lemma hasseMinkowskiInvAux.eq_of_perm {n : ℕ} (w : Fin n → k) (e : Fin n ≃ Fin n) :
    hasseMinkowskiInvAux (w ∘ e) = hasseMinkowskiInvAux w := by
  rw [hasseMinkowskiInvAux_Sym2, hasseMinkowskiInvAux_Sym2]
  let e2 := e.sym2Congr
  have hlift_comp_map : ∏ z : (Sym2 (Fin n)) with ¬z.IsDiag, hilbertSym_Sym2 w (e2 z) =
      ∏ z : (Sym2 (Fin n)) with ¬z.IsDiag, hilbertSym_Sym2 (w ∘ e) z := by
    refine Finset.prod_congr rfl (fun z hz ↦ ?_)
    simp only [Equiv.sym2Congr, Equiv.coe_fn_mk, e2]
    exact congrFun (Sym2.lift_comp_map _) z
  rw [← hlift_comp_map]
  refine Finset.prod_equiv e2 (fun z ↦ ?_) (by simp)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_iff_not]
  refine ⟨Sym2.IsDiag.map, ?_⟩
  simpa [e2, Equiv.sym2Congr, Sym2.map_map] using Sym2.IsDiag.map (f := e.symm) (z := e2 z)

-- CY : This lemma is probably not useful enough to be put into Mathlib separately.
lemma _root_.Fin.prod_lt_succ {M : Type*} [CommMonoid M] {n : ℕ}
    (f : Fin (n + 1) → Fin (n + 1) → M) :
    ∏ p : Fin (n + 1) × Fin (n + 1) with p.1 < p.2, f p.1 p.2 =
      (∏ j : Fin n, f 0 j.succ) *
        ∏ p : Fin n × Fin n with p.1 < p.2, f p.1.succ p.2.succ := by
  simp [Finset.prod_filter, Fintype.prod_prod_type, Fin.prod_univ_succ, Fin.succ_pos,
    Fin.succ_lt_succ_iff]

-- `[Invertible (2 : k)]` for `discr`
lemma hasseMinkowskiInvAux.succ {n : ℕ} [NeZero n] [Invertible (2 : k)]
    [hilbertSym.HasBilinHilbertSym k] (w : Fin (n + 1) → k) :
    hasseMinkowskiInvAux w =
      hilbertSym (w 0) (w 0 * (weightedSumSquares k w).discr (Pi.basisFun k _)) *
        hasseMinkowskiInvAux (w ∘ Fin.succ) := by
  rw [hasseMinkowskiInvAux_def (fun i ↦ (w i : k)),
    Fin.prod_lt_succ (fun i j ↦ hilbertSym (w i : k) (w j : k)), hasseMinkowskiInvAux_def]
  congr
  rw [weightedSumSquares_discr, Fin.prod_univ_succ, ← mul_assoc, mul_comm]
  simp only [smul_eq_mul, mul_one]
  by_cases hw0 : w 0 = 0
  · simpa [hilbertSym, hw0] using NeZero.out
  rw [← sq, hilbertSym.mul_right_square_eq hw0, hilbertSym.HasBilinHilbertSym.prod_right_eq]
  exact ⟨0, by simp⟩

lemma hasseMinkowskiInvAux.eq_of_equivalent_of_succ_eq {n : ℕ} {w w' : Fin (n + 1) → k}
    [NeZero n] [Invertible (2 : k)] [hilbertSym.HasBilinHilbertSym k]
    (h : (weightedSumSquares k w).Equivalent (weightedSumSquares k w'))
    (ih : hasseMinkowskiInvAux (w ∘ Fin.succ) = hasseMinkowskiInvAux (w' ∘ Fin.succ))
    (h0 : w 0 = w' 0) :
    hasseMinkowskiInvAux w = hasseMinkowskiInvAux w' := by
  rw [hasseMinkowskiInvAux.succ w, hasseMinkowskiInvAux.succ w', ih, h0]
  apply congrArg (· * hasseMinkowskiInvAux (w' ∘ Fin.succ))
  rw [IsometryEquiv.discr (Equiv.refl _) (Pi.basisFun _ _) (Pi.basisFun _ _) (Classical.choice h),
    ← mul_assoc]
  exact hilbertSym.mul_right_square_eq (LinearEquiv.det_toMatrix_ne_zero _ _ _)

lemma weight_eq_of_apply_basisFun_eq {n : ℕ} {w w' : Fin (n + 1) → k} [Invertible (2 : k)]
    (f : (weightedSumSquares k w).IsometryEquiv (weightedSumSquares k w'))
    (hf : Pi.basisFun k (Fin (n + 1)) 0 = ((Pi.basisFun k (Fin (n + 1))).map f) 0) :
    w 0 = w' 0 := by
  have h0 := f.map_app (Pi.basisFun k (Fin (n + 1)) 0)
  simp only [Pi.basisFun_apply, QuadraticMap.IsometryEquiv.coe_toLinearEquiv,
    QuadraticMap.weightedSumSquares_apply, Module.Basis.map_apply] at h0 hf
  rw [← hf] at h0
  repeat rw [Finset.sum_eq_single 0 (fun b hb hb0 ↦ by simp [hb0]) (fun h0 ↦ by simp at h0)] at h0
  simpa using h0.symm

open LinearEquiv in
lemma exists_reindex_weight_eq_of_isContiguous {n : ℕ} {w w' : Fin (n + 1) → k} [Invertible (2 : k)]
    (f : (weightedSumSquares k w).IsometryEquiv (weightedSumSquares k w'))
    (hf : ((Pi.basisFun k (Fin (n + 1))).map f).IsContiguous (Pi.basisFun k (Fin (n + 1)))) :
    ∃ e e' : Fin (n + 1) ≃ Fin (n + 1),
      (∀ m, (weightedSumSquares k (w' ∘ e'))
        ((funCongrLeft k k e).trans (f.toLinearEquiv.trans (funCongrLeft k k e')) m) =
          (weightedSumSquares k (w ∘ e)) m) ∧
      Pi.basisFun k (Fin (n + 1)) 0 =
        ((Pi.basisFun k (Fin (n + 1))).map
          ((funCongrLeft k k e).trans (f.toLinearEquiv.trans (funCongrLeft k k e')))) 0 := by
  obtain ⟨i, j, hij⟩ := hf
  use Equiv.swap 0 i, Equiv.swap 0 j
  constructor
  · intro m
    rw [weightedSumSquares_comp_equiv w', weightedSumSquares_comp_equiv w]
    simp only [Equiv.symm_swap, trans_apply, funCongrLeft_apply,
      QuadraticMap.IsometryEquiv.coe_toLinearEquiv, QuadraticMap.comp_apply, coe_coe,
      QuadraticMap.weightedSumSquares_apply, LinearMap.funLeft_apply, Equiv.swap_apply_self,
      smul_eq_mul]
    have hm := f.map_app ((funCongrLeft k k (Equiv.swap 0 i)) m)
    simpa only [funCongrLeft_apply, QuadraticMap.weightedSumSquares_apply, LinearMap.funLeft_apply,
      smul_eq_mul] using hm
  · simp only [Module.Basis.map_apply, trans_apply]
    simp only [Module.Basis.map_apply] at hij
    simp only [Pi.basisFun_apply, QuadraticMap.IsometryEquiv.coe_toLinearEquiv,
      funCongrLeft_apply] at hij ⊢
    ext x
    simp only [LinearMap.funLeft_apply, Equiv.swap_apply_def]
    have : (LinearMap.funLeft k k (Equiv.swap 0 i)) (Pi.single 0 1) = Pi.single i 1 := by
      ext y
      rw [LinearMap.funLeft_apply, Equiv.swap_apply_def]
      by_cases hy0 : y = 0 <;>
      by_cases hyi : y = i <;>
      simp_all
    by_cases hx0 : x = 0 <;>
    by_cases hxi : x = j <;>
    simp_all

theorem equivalent_weightedSumSquares_succ {n : ℕ} {w w' : Fin (n + 1) → k} [Invertible (2 : k)]
    (f : (weightedSumSquares k w).IsometryEquiv (weightedSumSquares k w')) (h0 : w 0 = w' 0) :
    (weightedSumSquares k (w ∘ Fin.succ)).Equivalent (weightedSumSquares k (w' ∘ Fin.succ)) := by
  sorry

open LinearEquiv in
lemma hasseMinkowskiInvAux.eq_of_equivalent_of_IsContiguous {n : ℕ} {w w' : Fin (n + 1) → k}
    [Invertible (2 : k)] [hilbertSym.HasBilinHilbertSym k] [NeZero n]
    (f : (weightedSumSquares k w).IsometryEquiv (weightedSumSquares k w'))
    (ih : ∀ {w0 w0' : Fin n → k},
      (weightedSumSquares k w0).Equivalent (weightedSumSquares k w0') →
        hasseMinkowskiInvAux w0 = hasseMinkowskiInvAux w0')
    (hf : ((Pi.basisFun k (Fin (n + 1))).map f).IsContiguous (Pi.basisFun k (Fin (n + 1)))) :
    hasseMinkowskiInvAux w = hasseMinkowskiInvAux w' := by
  obtain ⟨e, e', heq, h0⟩ := exists_reindex_weight_eq_of_isContiguous f hf
  let e'fe : (weightedSumSquares k (w ∘ e)).IsometryEquiv (weightedSumSquares k (w'∘ e')) :=
    ⟨(funCongrLeft k k e).trans (f.toLinearEquiv.trans (funCongrLeft k k e')), heq⟩
  rw [← hasseMinkowskiInvAux.eq_of_perm w e, ← hasseMinkowskiInvAux.eq_of_perm w' e']
  refine hasseMinkowskiInvAux.eq_of_equivalent_of_succ_eq  ⟨e'fe⟩ (ih ?_) ?_
  · exact equivalent_weightedSumSquares_succ e'fe (weight_eq_of_apply_basisFun_eq e'fe h0)
  · simpa using (weight_eq_of_apply_basisFun_eq e'fe h0)

section hasseMinkowskiInvBasis

open Module

noncomputable def hasseMinkowskiInvBasis {n : ℕ} {Q : QuadraticForm k V} {b : Basis (Fin n) k V}
    [Invertible (2 : k)] (_ : Q.associated.IsOrthoᵢ b) : ℤ :=
  hasseMinkowskiInvAux fun i ↦ Q (b i)

lemma hasseMinkowskiInvAux_Basis {n : ℕ} [Invertible (2 : k)] (w : Fin n → k) :
    hasseMinkowskiInvAux w = ((weightedSumSquares k w).hasseMinkowskiInvBasis
      (weightedSumSquares_isOrthoᵢ_basisFun w)) := by
  congr 1
  ext i
  rw [QuadraticMap.weightedSumSquares_apply,
    Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
  simp

-- Generalize existing `QuadraticForm.isometryEquivWeightedSumSquares` from field to ring,
-- from vector space to module, and from basis indexed by `Fin (finrank K V)` to `ι`
noncomputable def isometryEquivWeightedSumSquares' {R M ι : Type*} [CommRing R]
    [Invertible (2 : R)] [AddCommGroup M] [Module R M] [Fintype ι] {Q : QuadraticForm R M}
    {v : Basis ι R M} (hv : Q.associated.IsOrthoᵢ v) :
    Q.IsometryEquiv (QuadraticMap.weightedSumSquares R fun i ↦ Q (v i)) :=
  { v.equivFun with
    map_app' := fun x ↦ by
      rw [← Q.basisRepr_eq_of_iIsOrtho v hv]
      exact (Q.isometryEquivBasisRepr v).map_app x }

theorem _root_.Module.Basis.map_isometryEquivWeightedSumSquares' {R M ι : Type*} [CommRing R]
    [Invertible (2 : R)] [AddCommGroup M] [Module R M] [Fintype ι] {Q : QuadraticForm R M}
    {v : Basis ι R M} (hv : Q.associated.IsOrthoᵢ v) :
    v.map (Q.isometryEquivWeightedSumSquares' hv) = Pi.basisFun R ι := by
  classical
  refine Basis.eq_of_apply_eq fun i ↦ ?_
  simp only [isometryEquivWeightedSumSquares', Basis.map_apply, Pi.basisFun_apply]
  ext j
  simp [Pi.single_apply, eq_comm]

theorem _root_.Module.Basis.map_isometryEquivWeightedSumSquares'_symm {R M ι : Type*} [CommRing R]
    [Invertible (2 : R)] [AddCommGroup M] [Module R M] [Fintype ι] {Q : QuadraticForm R M}
    {v : Basis ι R M} (hv : Q.associated.IsOrthoᵢ v) :
    (Pi.basisFun R ι).map (Q.isometryEquivWeightedSumSquares' hv).symm = v := by
  refine Basis.eq_of_apply_eq fun i ↦ ?_
  have h : (Q.isometryEquivWeightedSumSquares' hv).toLinearEquiv (v i) = Pi.basisFun R ι i := by
    rw [← v.map_isometryEquivWeightedSumSquares' hv, Basis.map_apply]
  rw [Basis.map_apply, ← h]
  exact (Q.isometryEquivWeightedSumSquares' hv).toLinearEquiv.symm_apply_apply (v i)

-- CY : Add this to Mathlib. Somehow I could not find this easy lemma.
lemma _root_.Module.Basis.map_map {ι R M₁ M₂ M₃ : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (b : Basis ι R M₁) (f : M₁ ≃ₗ[R] M₂) (g : M₂ ≃ₗ[R] M₃) :
    (b.map f).map g = b.map (f.trans g) :=
  Basis.eq_of_apply_eq fun i ↦ by simp [Basis.map_apply]

lemma hasseMinkowskiInvBasis_eq_of_isContiguous {n : ℕ} {Q : QuadraticForm k V}
    {b b' : Basis (Fin (n + 1)) k V}
    [Invertible (2 : k)] [hilbertSym.HasBilinHilbertSym k] [NeZero n]
    (hb : Q.associated.IsOrthoᵢ b) (hb' : Q.associated.IsOrthoᵢ b')
    (ih : ∀ {w0 w0' : Fin n → k}, (weightedSumSquares k w0).Equivalent (weightedSumSquares k w0') →
      hasseMinkowskiInvAux w0 = hasseMinkowskiInvAux w0')
    (hc : b.IsContiguous b') :
    Q.hasseMinkowskiInvBasis hb = Q.hasseMinkowskiInvBasis hb' := by
  simp only [hasseMinkowskiInvBasis]
  let w := fun i ↦ Q (b i)
  let w' := fun i ↦ Q (b' i)
  let fb := Q.isometryEquivWeightedSumSquares' hb
  let fb' := Q.isometryEquivWeightedSumSquares' hb'
  let f := fb.symm.trans fb'
  refine hasseMinkowskiInvAux.eq_of_equivalent_of_IsContiguous f ih ?_
  simp only [f, fb]
  have hc_map := hc.map fb'.toLinearEquiv
  rw [Module.Basis.map_isometryEquivWeightedSumSquares',
    ← b.map_isometryEquivWeightedSumSquares'_symm hb, Basis.map_map] at hc_map
  exact hc_map

lemma hasseMinkowskiInvBasis_eq_of_chain {n : ℕ} {Q : QuadraticForm k V}
    {b b' : Basis (Fin (n + 1)) k V}
    [Invertible (2 : k)] [hilbertSym.HasBilinHilbertSym k] [NeZero n]
    (hb : Q.associated.IsOrthoᵢ b) (hb' : Q.associated.IsOrthoᵢ b')
    (ih : ∀ {w0 w0' : Fin n → k}, (weightedSumSquares k w0).Equivalent (weightedSumSquares k w0') →
      hasseMinkowskiInvAux w0 = hasseMinkowskiInvAux w0')
    (c : Module.Basis.Chain Q b b') :
    -- (basis : Fin (m + 1) → Basis (Fin (n + 1)) k V)
    -- (basis_ortho : ∀ i : Fin (m + 1), Q.associated.IsOrthoᵢ (basis i))
    -- (basis_zero : basis 0 = b)
    -- (basis_m_sub_one : basis ⟨m, lt_add_one m⟩ = b')
    -- (basis_isContiguous : ∀ i, ∀ (hi : i < m),
    --   (basis ⟨i, by omega⟩).IsContiguous (basis ⟨i + 1, by omega⟩)) :
    -- (C : Module.Basis.Chain (weightedSumSquares k w')
    -- (Pi.basisFun k (Fin (n + 1))) ((Pi.basisFun k (Fin (n + 1))).map f)):
    hasseMinkowskiInvBasis hb = hasseMinkowskiInvBasis hb' := by
  obtain ⟨m, basis, basis_ortho, basis_zero, basis_m_sub_one, basis_isContiguous⟩ := c
  induction m generalizing b with
  | zero =>
  simp only [Fin.isValue, Nat.reduceAdd, Fin.zero_eta, not_lt_zero, IsEmpty.forall_iff,
    implies_true] at *
  rw [basis_zero] at basis_m_sub_one
  refine hasseMinkowskiInvBasis_eq_of_isContiguous hb hb' ih ?_
  use 0, 0
  exact congrArg (fun b ↦ b 0) basis_m_sub_one
  | succ m ih' =>
  let basis' := basis ∘ Fin.succ
  have ih' := ih' (basis_ortho 1) basis' (by simp [basis', basis_ortho]) (by simp [basis'])
    (by simp [basis', basis_m_sub_one]) (fun i hi ↦ basis_isContiguous (i + 1) (by omega))
  rw [← ih']
  refine hasseMinkowskiInvBasis_eq_of_isContiguous hb _ ih ?_
  simpa [basis_zero] using basis_isContiguous 0 (by omega)

lemma hasseMinkowskiInvBasis_map {n : ℕ} {Q : QuadraticForm k V} {Q' : QuadraticForm k W}
    {b : Basis (Fin n) k V} [Invertible (2 : k)] (f : Q.IsometryEquiv Q')
    (hb : Q.associated.IsOrthoᵢ b) (hb' : Q'.associated.IsOrthoᵢ (b.map f.toLinearEquiv)) :
    Q.hasseMinkowskiInvBasis hb = Q'.hasseMinkowskiInvBasis hb' := by
  unfold hasseMinkowskiInvBasis
  congr 1
  ext i
  rw [Basis.map_apply]
  exact (f.map_app (b i)).symm

end hasseMinkowskiInvBasis

lemma weightedSumSquares_basisFun {R ι : Type*} [CommRing R]
    [Invertible (2 : R)] [Fintype ι] (w : ι → R) (i : ι) :
    weightedSumSquares R w (Pi.basisFun R ι i) = w i := by
  classical
  rw [QuadraticMap.weightedSumSquares_apply, Finset.sum_eq_single i]
  · simp [Pi.basisFun_apply]
  · intro j _ hj
    simp [Pi.basisFun_apply, Pi.single_eq_of_ne hj]
  · simp

-- Compare `nondegenerate_weightedSumSquares`
lemma separatingLeft_weightedSumSquares {R ι : Type*} [CommRing R] [IsDomain R]
    [Invertible (2 : R)] [Fintype ι] (w : ι → Rˣ) :
    LinearMap.SeparatingLeft (QuadraticMap.associated (weightedSumSquares R w)) := by
  refine LinearMap.IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self (Pi.basisFun R ι)
    (weightedSumSquares_isOrthoᵢ_basisFun fun i ↦ (w i : R)) fun i hi ↦ ?_
  have h : weightedSumSquares R (fun i ↦ (w i : R)) (Pi.basisFun R ι i) = 0 := by
    have h2 := hi
    rw [QuadraticMap.associated_eq_self_apply] at h2
    exact h2
  rw [weightedSumSquares_basisFun] at h
  exact (w i).ne_zero h

lemma hasseMinkowskiInvAux.eq_of_equivalent_of_chain {n : ℕ} {w w' : Fin (n + 1) → k}
    [Invertible (2 : k)] [hilbertSym.HasBilinHilbertSym k] [NeZero n]
    (f : (weightedSumSquares k w).IsometryEquiv (weightedSumSquares k w'))
    (ih : ∀ {w0 w0' : Fin n → k}, (weightedSumSquares k w0).Equivalent (weightedSumSquares k w0') →
      hasseMinkowskiInvAux w0 = hasseMinkowskiInvAux w0')
    (c : Module.Basis.Chain (weightedSumSquares k w')
      ((Pi.basisFun k (Fin (n + 1))).map f) (Pi.basisFun k (Fin (n + 1)))) :
    hasseMinkowskiInvAux w= hasseMinkowskiInvAux w' := by
  rw [hasseMinkowskiInvAux_Basis w, hasseMinkowskiInvAux_Basis w']
  have hb : (weightedSumSquares k w').associated.IsOrthoᵢ
    ((Pi.basisFun k _).map f.toLinearEquiv) := sorry
  rw [hasseMinkowskiInvBasis_map f _ hb]
  exact hasseMinkowskiInvBasis_eq_of_chain hb (weightedSumSquares_isOrthoᵢ_basisFun w') ih c

lemma exists_eq_zero_of_equivalent {ι ι' : Type*} {w : ι → k} {w' : ι' → k} [Invertible (2 : k)]
    [Fintype ι] [Fintype ι'] (h : (weightedSumSquares k w).Equivalent (weightedSumSquares k w'))
    (hw : ∃ i, w i = 0) : ∃ j, w' j = 0 := by
  classical
  obtain ⟨f⟩ := h
  obtain ⟨i, hi⟩ := hw
  -- isometries preserve the associated bilinear form
  have key : ∀ x y, (weightedSumSquares k w').associated (f x) (f y) =
      (weightedSumSquares k w).associated x y := fun x y => by
    simp only [QuadraticMap.associated_apply, ← map_add, f.map_app]
  -- f e_i ≠ 0, so it has a nonzero coordinate j
  have hne : f (Pi.single i 1) ≠ 0 := fun h0 ↦ (by simpa using congrArg f.symm h0)
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  refine ⟨j, ?_⟩
  have hp := key (Pi.single i 1) (f.symm (Pi.single j 1))
  rw [f.apply_symm_apply, associated_weightedSumSquares, associated_weightedSumSquares] at hp
  -- right side: e_i is in the radical because w i = 0
  have hR : ∑ l, w l • ((Pi.single i (1 : k) : ι → k) l * (f.symm (Pi.single j 1)) l) = 0 :=
    Finset.sum_eq_zero fun l _ => by
      by_cases hl : l = i
      · subst hl; simp [hi]
      · simp [Pi.single_eq_of_ne hl]
  -- left side: only the j-th term survives
  have hL : ∑ l, w' l • ((f (Pi.single i 1)) l * (Pi.single j (1 : k) : ι' → k) l) =
      w' j * (f (Pi.single i 1)) j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hl; simp [Pi.single_eq_of_ne hl]
    · simp
  rw [hL, hR] at hp
  -- simpa [hj] using hp
  sorry

lemma hasseMinkowskiInvAux.eq_of_equivalent {n n' : ℕ} {w : Fin n → k} {w' : Fin n' → k}
    [Invertible (2 : k)] -- `[Invertible (2 : k)]` is used in `eq_one_iff_represents_one`
    [hilbertSym.HasBilinHilbertSym k]
    (h : (weightedSumSquares k w).Equivalent (weightedSumSquares k w')) :
    hasseMinkowskiInvAux w = hasseMinkowskiInvAux w' := by
  have eq : n' = n := by
    obtain ⟨e⟩ := h
    simpa only [Module.finrank_fin_fun] using e.toLinearEquiv.finrank_eq.symm
  subst n'
  match hn : n with
  | 0       => simp [hasseMinkowskiInvAux]
  | 1       =>
  dsimp [hasseMinkowskiInvAux]
  have hempty : ({p : Fin 1 × Fin 1 | p.1 < p.2} : Finset (Fin 1 × Fin 1)) = ∅ := by simp
  simp [hempty]
  | 2       =>
  dsimp [hasseMinkowskiInvAux]
  have hsingle (w : Fin 2 → k) :
    ∏ p : Fin 2 × Fin 2 with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2) =
    hilbertSym (w 0 : k) (w 1) := Finset.prod_eq_single (0, 1) (by grind) (fun h ↦ by simp at h)
  rw [hsingle w, hsingle w']
  have degenerate_iff : w 0 = 0 ∨ w 1 = 0 ↔ w' 0 = 0 ∨ w' 1 = 0 := by
    refine ⟨fun h0 ↦ ?_, fun h0' ↦ ?_⟩
    · exact Fin.exists_fin_two.mp (exists_eq_zero_of_equivalent h (Fin.exists_fin_two.mpr h0))
    · exact Fin.exists_fin_two.mp (exists_eq_zero_of_equivalent h.symm (Fin.exists_fin_two.mpr h0'))
  by_cases h0 : w 0 = 0 ∨ w 1 = 0
  · have h0' := degenerate_iff.mp h0
    simp [hilbertSym, h0, h0']
  have h0' := degenerate_iff.not.mp h0
  push Not at h0 h0'
  by_cases hone : hilbertSym (w' 0 : k) (w' 1 : k) = 1
  · rw [hone, hilbertSym.eq_one_iff_represents_one h0]
    rw [hilbertSym.eq_one_iff_represents_one h0'] at hone
    exact (QuadraticMap.Equivalent.represents_iff h 1).mpr hone
  · have hnegone : hilbertSym (w' 0 : k) (w' 1 : k) = -1 := by
      simpa [hone] using
        hilbertSym.eq_one_or_neg_one_of_ne_zero h0'.1 h0'.2
    rw [hnegone]
    rw [not_congr (hilbertSym.eq_one_iff_represents_one h0'),
      ← QuadraticMap.Equivalent.represents_iff h (1 : kˣ),
      ← not_congr (hilbertSym.eq_one_iff_represents_one h0)] at hone
    simpa [hone] using
      hilbertSym.eq_one_or_neg_one_of_ne_zero h0.1 h0.2
  | (r + 3) =>
  obtain ⟨f⟩ := h
  let b' := (Pi.basisFun k (Fin (r + 3)))
  let b := b'.map f.toLinearEquiv
  have chain : Module.Basis.Chain (weightedSumSquares k w') b b' := by sorry
  refine hasseMinkowskiInvAux.eq_of_equivalent_of_chain f ?_ chain
  exact hasseMinkowskiInvAux.eq_of_equivalent

variable [FiniteDimensional k V] [FiniteDimensional k W]

section invertibleTwo

variable [Invertible (2 : k)]

/-- Let `Q` be a quadratic form on `V` such that `Q.associated` is `SeparatingLeft`, and
suppose that `Q` is equivalent to the diagonal quadratic form `a_1 X_1^2 + ⋯ + a_n X_n ^ 2`.
The Hasse-Minkowski invariant of `Q` is defined as the product `∏_{i < j} (a_i, a_j)`, where
`(·, ·)` denotes the Hilbert symbol.

This is denoted by `ε(Q)` in Serre's book. -/
noncomputable def hasseMinkowskiInv {Q : QuadraticForm k V}
    (hQ : LinearMap.SeparatingLeft Q.associated) : ℤ :=
  hasseMinkowskiInvAux
    (fun i ↦ ((equivalent_weightedSumSquares_units_of_nondegenerate' Q hQ).choose i : k))

namespace hasseMinkowskiInv

open _root_.QuadraticMap

variable {Q : QuadraticForm k V} {Q' : QuadraticForm k W}
  (hQ : LinearMap.SeparatingLeft Q.associated)
  [hilbertSym.HasBilinHilbertSym k]

lemma weightedSumSquares {n : ℕ} (w : Fin n → kˣ) :
    hasseMinkowskiInv
      (nondegenerate_associated_iff.mpr (nondegenerate_weightedSumSquares w)).1 =
      ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2) := by
  simp only [hasseMinkowskiInv, ← hasseMinkowskiInvAux_def (fun i ↦ (w i : k))]
  exact hasseMinkowskiInvAux.eq_of_equivalent
    ((equivalent_weightedSumSquares_units_of_nondegenerate' (QuadraticMap.weightedSumSquares k w))
      (nondegenerate_associated_iff.mpr (nondegenerate_weightedSumSquares w)).1).choose_spec.symm

lemma weightedSumSquares_two (w : Fin 2 → kˣ) :
    hasseMinkowskiInv
      (nondegenerate_associated_iff.mpr (nondegenerate_weightedSumSquares w)).1 =
      hilbertSym (w 0 : k) (w 1) := by
  rw [hasseMinkowskiInv.weightedSumSquares, Finset.prod_eq_single (0, 1)
      (by grind) (fun h ↦ by simp at h)]

lemma weightedSumSquares_three (w : Fin 3 → kˣ) :
    hasseMinkowskiInv
      (nondegenerate_associated_iff.mpr (nondegenerate_weightedSumSquares w)).1 =
      hilbertSym (w 0 : k) (w 1) * hilbertSym (w 0 : k) (w 2) * hilbertSym (w 1 : k) (w 2) := by
  have h : ({p : Fin 3 × Fin 3 | p.1 < p.2} : Finset (Fin 3 × Fin 3)) =
      {(0, 1), (0, 2), (1, 2)} := by
    ext p
    refine ⟨fun hp ↦ ?_, fun hp ↦ by aesop⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.isValue, Finset.mem_insert,
        Finset.mem_singleton] at hp ⊢
      have h1 : p.1 = 0 ∨ p.1 = 1 ∨ p.1 = 2 := by omega
      have h2 : p.2 = 0 ∨ p.2 = 1 ∨ p.2 = 2 := by omega
      aesop
  rw [hasseMinkowskiInv.weightedSumSquares,
    Finset.prod_congr h (g := fun p ↦ hilbertSym (w p.1 : k) (w p.2)) (by simp)]
  simp [mul_assoc]

lemma eq_of_equivalent_weightedSumSquares {n : ℕ} {w : Fin n → kˣ}
    (h : Q.Equivalent (QuadraticMap.weightedSumSquares k w)) :
    hasseMinkowskiInv hQ =
      hasseMinkowskiInv (LinearMap.separatingLeft_of_equivalent h hQ) := by
  dsimp [hasseMinkowskiInv]
  have hQeq := (equivalent_weightedSumSquares_units_of_nondegenerate' Q hQ).choose_spec
  have hweq := (equivalent_weightedSumSquares_units_of_nondegenerate'
    (QuadraticMap.weightedSumSquares k w) (LinearMap.separatingLeft_of_equivalent h hQ)).choose_spec
  exact hasseMinkowskiInvAux.eq_of_equivalent ((hQeq.symm.trans h).trans hweq)

lemma eq_of_equivalent (h : Q.Equivalent Q') :
    hasseMinkowskiInv hQ =
      hasseMinkowskiInv (LinearMap.separatingLeft_of_equivalent h hQ) := by
  obtain ⟨w, hw⟩ := equivalent_weightedSumSquares_units_of_nondegenerate' Q hQ
  have hw' : Q'.Equivalent (QuadraticMap.weightedSumSquares k w) := by
    let f := Classical.choice h
    let g := Classical.choice hw
    exact ⟨f.symm.trans g⟩
  rw [eq_of_equivalent_weightedSumSquares hQ hw,
    eq_of_equivalent_weightedSumSquares (LinearMap.separatingLeft_of_equivalent h hQ) hw']

lemma eq_one_or_neg_one :
    hasseMinkowskiInv hQ = 1 ∨ hasseMinkowskiInv hQ = - 1 := by
  obtain ⟨w, hw⟩ := equivalent_weightedSumSquares_units_of_nondegenerate' Q hQ
  rw [eq_of_equivalent_weightedSumSquares hQ hw, weightedSumSquares]
  refine Finset.prod_induction
    (fun (p : Fin (Module.finrank k V) × Fin (Module.finrank k V)) ↦ hilbertSym (w p.1 : k) (w p.2))
    (fun n ↦ n = 1 ∨ n = -1) (by grind) (by simp) (fun x hx ↦ ?_)
  exact hilbertSym.eq_one_or_neg_one_of_ne_zero (by simp) (by simp)

open Module TensorProduct in
lemma of_baseChange_weightedSumSquares {R : Type*} (A : Type*) [Field R]
    [Invertible (2 : R)] [Field A] [Invertible (2 : A)] [hilbertSym.HasBilinHilbertSym A]
    [Algebra R A] (w : Fin 2 → Rˣ) :
    hasseMinkowskiInv
      ((nondegenerate_associated_iff.mpr
        (nondegenerate_baseChange (A := A) (nondegenerate_weightedSumSquares w))).1) =
      hilbertSym (algebraMap R A (w ⟨0, by omega⟩)) (algebraMap R A (w ⟨1, by omega⟩)) := by
  have h2 : finrank A (A ⊗[R] (Fin 2 → R)) = 2 := by simp
  rw [hasseMinkowskiInv.eq_of_equivalent_weightedSumSquares
    (w := ![Units.map (algebraMap R A) (w ⟨0, by omega⟩),
       Units.map (algebraMap R A) (w ⟨1, by omega⟩)]) _
    (((baseChange_weightedSumSquares _ _ _).trans (Equivalent.refl _))), weightedSumSquares_two]
  simp

open Module hilbertSym HasBilinHilbertSym in
lemma prod_rank_one (b : Basis (Fin 2) k V) (a : kˣ) (h : Q.Nondegenerate) :
    hasseMinkowskiInv
      ((Q.prod (QuadraticMap.weightedSumSquares k ![a])).nondegenerate_associated_iff.mpr
        (nondegenerate_prod h (nondegenerate_weightedSumSquares _))).1 =
    hilbertSym (a : k) (Q.discr b) *
      hasseMinkowskiInv (Q.nondegenerate_associated_iff.mpr h).1 := by
  let Qa := Q.prod (QuadraticMap.weightedSumSquares k ![a])
  obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate 2
    (by simp [finrank_eq_card_basis b]) (nondegenerate_associated_iff.mpr h).1
  have hwa : Qa.Equivalent (QuadraticMap.weightedSumSquares k ![w 0, w 1, a]) :=
    (hw.prod (Equivalent.refl _)).trans (weightedSumSquares_equiv_prod w a).symm
  have hQa := (Qa.nondegenerate_associated_iff.mpr
    (nondegenerate_prod h (nondegenerate_weightedSumSquares _))).1
  have hilbertSym_eq : hilbertSym (a : k) (Q.discr b) = hilbertSym (a : k) (w 0 * w 1) := by
    -- Q and Qw are equivalent, so Q.discr b and Qw.discr (Pi.basisFun k (Fin 2)) differ by a square
    -- hilbertSym is invariant under multiplication by squares
    -- The discriminant of a weightedSumSquares is the product of its coefficients
    simp [IsometryEquiv.discr (Equiv.refl (Fin 2)) b (Pi.basisFun k (Fin 2)) (Classical.choice hw),
      mul_right_square_eq (LinearEquiv.det_toMatrix_ne_zero _ _ _), weightedSumSquares_discr,
      Units.smul_def]
  -- Change goal to hasseMinkowskiInv Qwa = hilbertSym (a : k) (Q.discr b) * hasseMinkowskiInv Qw
  -- With HasBilinHilbertSym, the two sides can be proven to be equal
  simp [eq_of_equivalent_weightedSumSquares hQa hwa,
    eq_of_equivalent_weightedSumSquares (Q.nondegenerate_associated_iff.mpr h).1 hw, hilbertSym_eq,
    mul_left_eq, comm (a := (a : k)), weightedSumSquares_two, weightedSumSquares_three]
  ring_nf

end hasseMinkowskiInv

end invertibleTwo

open hilbertSym Module _root_.QuadraticMap
section CharZero

variable {Q} [CharZero k] [hilbertSym.HasBilinHilbertSym k] (hQ : Q.Nondegenerate)

private lemma represents_zero_iff_of_rank_three_aux (b : Basis (Fin 3) k V) (hQ : Q.Nondegenerate)
    {w : Fin 3 → kˣ} (hw : Q.Equivalent (weightedSumSquares k w))
    (heq : hilbertSym (-w 2 * w 0 : k) (-w 2 * w 1) = hilbertSym (-1) (-Q.discr b) *
        hasseMinkowskiInv (Q.nondegenerate_associated_iff.mpr hQ).1) :
    Q.Isotropic ↔ hilbertSym (-1) (-Q.discr b) =
        hasseMinkowskiInv (Q.nondegenerate_associated_iff.mpr hQ).1 := by
  have hw' : w = ![w 0, w 1, w 2] := List.ofFn_inj.mp rfl
  set s := hilbertSym (-1) (-Q.discr b)
  set ε := hasseMinkowskiInv (Q.nondegenerate_associated_iff.mpr hQ).1 with hε_def
  have hs1 : s = 1 ∨ s = -1 := eq_one_or_neg_one_of_ne_zero (by simp)
    (neg_ne_zero.mpr ((nondegenerate_iff_discr_ne_zero b).mp hQ))
  have hε1 : ε = 1 ∨ ε = -1 :=
    hasseMinkowskiInv.eq_one_or_neg_one (Q.nondegenerate_associated_iff.mpr hQ).1
  have hsε : s = ε ↔ s * ε = 1 := by
    rcases hs1 with hs1 | hs1 <;> rcases hε1 with hε1 | hε1 <;> simp [hs1, hε1]
  have hε : ε = hilbertSym (w 0 : k) (w 1) * hilbertSym (w 0 : k) (w 2) *
      hilbertSym (w 1 : k) (w 2) := by
    simp [ε, hasseMinkowskiInv.eq_of_equivalent _ hw,
      hasseMinkowskiInv.weightedSumSquares_three]
  rw [hw.isotropic_iff, hw', weightedSumSquares_isotropic_iff_hilbertSym_eq_one, hsε, heq]

section HasBilinHilbertSym

open HasBilinHilbertSym

lemma represents_zero_iff_of_rank_three (b : Basis (Fin 3) k V) :
    Q.Isotropic ↔
      hilbertSym (-1) (-Q.discr b) =
        hasseMinkowskiInv (Q.nondegenerate_associated_iff.mpr hQ).1 := by
  obtain ⟨w, hw⟩ := equivalent_weightedSumSquares_units_of_nondegenerate 3
    (by simp [finrank_eq_card_basis b]) (Q.nondegenerate_associated_iff.mpr hQ).1
  -- Set up notation for readability
  let ⟨fw⟩ := hw
  let a₀ := w 0
  let a₁ := w 1
  let a₂ := w 2
  let u := ((LinearMap.toMatrix b (Pi.basisFun k (Fin 3))) fw.toLinearEquiv).det
  set s := hilbertSym (-1) (-Q.discr b)
  set ε := hasseMinkowskiInv (Q.nondegenerate_associated_iff.mpr hQ).1 with hε_def
  have hε : ε = hilbertSym (a₀ : k) a₁ * hilbertSym (a₀ : k) a₂ * hilbertSym (a₁ : k) a₂ := by
    simp [ε, hasseMinkowskiInv.eq_of_equivalent _ hw,
      hasseMinkowskiInv.weightedSumSquares_three, a₀, a₁, a₂]
  rw [represents_zero_iff_of_rank_three_aux b hQ hw]
  -- Computation using properties of the Hilbert Symbol
  calc hilbertSym (-a₂ * a₀ : k) (-a₂ * a₁)
    _ = hilbertSym (-1 : k) (- 1) * hilbertSym (-1 : k) a₀ * hilbertSym (-1 : k) a₁ *
        hilbertSym (a₂ : k) a₂ *
        (hilbertSym (a₀ : k) a₁ * hilbertSym (a₀ : k) a₂ * hilbertSym (a₁ : k) a₂) := by
        rw [← neg_one_mul (a₂ : k)]
        simp only [mul_right_eq, mul_left_eq]
        rw [comm (a := (a₂ : k)) (b := -1), comm (a := (a₀ : k)) (b := -1),
          comm (a := (a₂ : k)) (b := a₁)]
        ring_nf
        rw [sq_eq_one_iff.mpr (eq_one_or_neg_one_of_ne_zero (by simp) (by simp))]
        simp
    _ = hilbertSym (-1 : k) (- 1) * hilbertSym (-1 : k) a₀ * hilbertSym (-1 : k) a₁ *
        hilbertSym (a₂ : k) a₂ * ε := by simp [hε]
    _ = hilbertSym (-1 : k) (- 1) * hilbertSym (-1 : k) a₀ * hilbertSym (-1 : k) a₁ *
        hilbertSym (-1 : k) a₂ * ε := by
        congr 2
        rw [← left_neg_mul (a := -1)]
        simp
    _ = hilbertSym (-1 : k) (- 1) * hilbertSym (-1 : k) (a₀ * a₁ * a₂) * ε := by
      rw [mul_right_eq, mul_right_eq]
      ring
    _ = hilbertSym (-1 : k) (- (a₀ * a₁ * a₂)) * ε := by
      rw [← neg_one_mul (_ * _), mul_right_eq (b := -1)]
    _ = hilbertSym (-1 : k) (- (a₀ * a₁ * a₂ * u ^ 2)) * ε := by
      rw [← neg_mul _ ((u : k) ^ 2), mul_right_square_eq]
      exact LinearEquiv.det_toMatrix_ne_zero _ _ _
    _ = s * ε := by simp [s, discr_three b fw, u, a₀, a₁, a₂]

lemma represents_iff_of_rank_two (b : Basis (Fin 2) k V) (a : kˣ) :
    Q.represents a ↔
      hilbertSym (a : k) (-Q.discr b) =
        hasseMinkowskiInv (Q.nondegenerate_associated_iff.mpr hQ).1 := by
  let ε := hasseMinkowskiInv (Q.nondegenerate_associated_iff.mpr hQ).1
  let fa := Q.prod (weightedSumSquares k ![-a])
  have hfa : fa.Nondegenerate := nondegenerate_prod hQ (nondegenerate_weightedSumSquares _)
  let b' := b.prod (Pi.basisFun k (Fin 1))
  let e := (finSumFinEquiv (m := 2) (n := 1))
  -- Change LHS of goal to hilbertSym (-1, -fa.discr b') = hasseMinkowskiInv fa
  rw [represents_iff_sub_isotropic hQ a, represents_zero_iff_of_rank_three hfa (b'.reindex e)]
  have hdisc : fa.discr (b'.reindex e) = - (Q.discr b * a) := by
    rw [fa.discr_reindex e b', discr_prod]
    field_simp [(nondegenerate_iff_discr_ne_zero b).mp hQ]
    simp [weightedSumSquares_discr, Units.smul_def]
  have hHM : hasseMinkowskiInv (fa.nondegenerate_associated_iff.mpr hfa).1 =
      hilbertSym ((-1) * (a : k)) ((-1) * -Q.discr b) * ε := by
    simpa using hasseMinkowskiInv.prod_rank_one b (-a) hQ
  -- Simplify left hand side (-1, discr) to (-1, d) * (a, -1)
  simp only [hdisc, Nat.succ_eq_add_one, Nat.reduceAdd, neg_neg, mul_right_eq, comm (b := (a : k))]
  -- Simplify right hand side (-a, d) * ε to (-1, d) * (a, -1) * (a, -d) * ε
  rw [hHM, mul_left_eq]
  nth_rw 1 [mul_neg]
  rw [neg_mul, one_mul, neg_neg, mul_right_eq]
  -- Cancel out (-1, d) * (a, -1) from both sides to get 1 = (a, -d) * ε
  have hnezero :  hilbertSym (-1) (discr b Q) ≠ 0 := ne_zero_of_ne_zero (by simp)
    ((nondegenerate_iff_discr_ne_zero b).mp hQ)
  have hnezero' : hilbertSym (a : k) (-1) ≠ 0 := ne_zero_of_ne_zero (by simp) (by simp)
  simp only [mul_assoc, mul_eq_mul_left_iff, ne_eq, hnezero', not_false_eq_true, left_eq_mul₀,
    hnezero, or_false, eq_comm]
  -- Using the fact (a, -d) = ±1 to conclude (a, -d) = ε
  have one_neg_one : hilbertSym (↑a) (-discr b Q) = 1 ∨ hilbertSym (↑a) (-discr b Q) = -1 :=
    eq_one_or_neg_one_of_ne_zero (by simp)
    (neg_ne_zero.mpr ((nondegenerate_iff_discr_ne_zero b).mp hQ))
  exact one_neg_one.elim (fun h ↦ by simp [h, ε]) (fun h ↦ by simp [h, ε, neg_eq_iff_eq_neg])

end HasBilinHilbertSym

end CharZero

end QuadraticForm
