/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández, Chi-Yun Hsu
-/
module

public import HassePrinciple.ForMathlib.LinearAlgebra.Determinant
public import HassePrinciple.QuadraticForm.Chain
public import HassePrinciple.QuadraticForm.LowRank

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

/-- Given a weight `w : Fin n → k`, `hilbertSymSym2` lifts `fun i j ↦ hilbertSym (w i) (w j)`
from `Fin n × Fin n` to `Sym2 (Fin n)`. -/
noncomputable abbrev hilbertSymSym2 {n : ℕ} (w : Fin n → k) (z : Sym2 (Fin n)) : ℤ :=
  Sym2.lift ⟨fun i j ↦ hilbertSym (w i) (w j), by simp [hilbertSym.comm]⟩ z

lemma hasseMinkowskiInvAux_eq_prod_sym2 {n : ℕ} (w : Fin n → k) :
    hasseMinkowskiInvAux w = ∏ z : Sym2 (Fin n) with ¬z.IsDiag, hilbertSymSym2 w z := by
  refine Finset.prod_bij (fun p _ ↦ s(p.1, p.2)) (by simp_all [ne_of_lt]) (by grind) ?_ (by simp)
  -- surjective
  intro z
  refine Sym2.ind (fun i j ↦ ?_) z
  simp [Finset.mem_filter]
  grind

-- This definition is included in PR 43815, which has not been merged to Mahlib yet.
/-- An equivalence `e : α ≃ β` induces an equivalence `Sym2.map e : Sym2 α ≃ Sym2 β`. -/
def _root_.Equiv.sym2Congr {α β : Type*} (e : α ≃ β) : Sym2 α ≃ Sym2 β where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv x := by
    rw [Sym2.map_map, Equiv.symm_comp_self, Sym2.map_id, id_eq]
  right_inv x := by
    rw [Sym2.map_map, Equiv.self_comp_symm, Sym2.map_id, id_eq]

lemma hasseMinkowskiInvAux.eq_of_equiv {n : ℕ} (w : Fin n → k) (e : Fin n ≃ Fin n) :
    hasseMinkowskiInvAux (w ∘ e) = hasseMinkowskiInvAux w := by
  have hlift_comp_map : ∏ z : (Sym2 (Fin n)) with ¬z.IsDiag, hilbertSymSym2 w (e.sym2Congr z) =
      ∏ z : (Sym2 (Fin n)) with ¬z.IsDiag, hilbertSymSym2 (w ∘ e) z := by
    refine Finset.prod_congr rfl (fun z hz ↦ ?_)
    simp [Equiv.sym2Congr, hilbertSymSym2, Sym2.lift_map_apply]
  rw [hasseMinkowskiInvAux_eq_prod_sym2, hasseMinkowskiInvAux_eq_prod_sym2, ← hlift_comp_map,
    Finset.prod_equiv _ (fun z ↦ ?_) (by aesop)]
  simp [Equiv.sym2Congr, Sym2.isDiag_map e.injective]

-- CY : This lemma is probably not useful enough to be put into Mathlib separately.
lemma _root_.Fin.prod_lt_succ {M : Type*} [CommMonoid M] {n : ℕ}
    (f : Fin (n + 1) → Fin (n + 1) → M) :
    ∏ p : Fin (n + 1) × Fin (n + 1) with p.1 < p.2, f p.1 p.2 =
      (∏ j : Fin n, f 0 j.succ) *
        ∏ p : Fin n × Fin n with p.1 < p.2, f p.1.succ p.2.succ := by
  simp [Finset.prod_filter, Fintype.prod_prod_type, Fin.prod_univ_succ, Fin.succ_pos,
    Fin.succ_lt_succ_iff]

lemma hasseMinkowskiInvAux.of_succ {n : ℕ} [NeZero n] [Invertible (2 : k)]
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
  rw [hasseMinkowskiInvAux.of_succ w, hasseMinkowskiInvAux.of_succ w', ih, h0]
  apply congrArg (· * hasseMinkowskiInvAux (w' ∘ Fin.succ))
  rw [IsometryEquiv.discr (Equiv.refl _) (Pi.basisFun _ _) (Pi.basisFun _ _) (Classical.choice h),
    ← mul_assoc]
  exact hilbertSym.mul_right_square_eq (LinearEquiv.det_toMatrix_ne_zero _ _ _)

lemma weight_eq_of_basisFun_apply_eq {n : ℕ} {w w' : Fin (n + 1) → k} {i : Fin (n + 1)}
    (f : (weightedSumSquares k w).IsometryEquiv (weightedSumSquares k w'))
    (hf : Pi.basisFun k (Fin (n + 1)) i = ((Pi.basisFun k (Fin (n + 1))).map f) i) :
    w i = w' i := by
  have hi := f.map_app (Pi.basisFun k (Fin (n + 1)) i)
  simp only [Pi.basisFun_apply, QuadraticMap.IsometryEquiv.coe_toLinearEquiv,
    QuadraticMap.weightedSumSquares_apply, Module.Basis.map_apply] at hi hf
  rw [← hf] at hi
  repeat rw [Finset.sum_eq_single i (fun b _ hb ↦ by simp [hb]) (fun h ↦ by simp at h)] at hi
  simpa using hi.symm

open LinearEquiv in
lemma exists_reindex_weight_eq_of_isContiguous {n : ℕ} {w w' : Fin (n + 1) → k}
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
    by_cases hxj : x = j <;>
    simp_all

theorem exists_eq_zero_of_equivalent_of_zero {ι ι' : Type*} {w : ι → k} {w' : ι' → k}
    [Invertible (2 : k)] [Fintype ι] [Fintype ι']
    (h : (weightedSumSquares k w).Equivalent (weightedSumSquares k w')) (hw : ∃ i, w i = 0) :
    ∃ j, w' j = 0 := by
  classical
  obtain ⟨f⟩ := h
  obtain ⟨i, hi⟩ := hw
  -- Let `j` be a nonzero coordinate of `f e_i`.
  obtain ⟨j, hj⟩ := Function.ne_iff.mp (by simp : f (Pi.single i 1) ≠ 0)
  simp only [Pi.zero_apply, ne_eq] at hj
  refine ⟨j, ?_⟩
  -- Isometries preserve the associated bilinear form
  have hassociated_map_app : ∀ x y, (weightedSumSquares k w').associated (f x) (f y) =
      (weightedSumSquares k w).associated x y := by
    intro x y
    simp [QuadraticMap.associated_apply, ← map_add]
  -- `B_w' (f (e i), e j) = B_w (e i, f.symm (e j))` simplifies to
  -- `w' j * (j-coordinate of f (e i)) = w i * (i-coordinate of f.symm (e j))`
  have heq := hassociated_map_app (Pi.single i 1) (f.symm (Pi.single j 1))
  rw [f.apply_symm_apply, associated_weightedSumSquares w, associated_weightedSumSquares w',
    Finset.sum_eq_single i (fun l _ hl ↦ by simp [hl]) (fun h0 ↦ by simp at h0),
    Finset.sum_eq_single j (fun l _ hl ↦ by simp [hl]) (fun h0 ↦ by simp at h0)] at heq
  simpa [hi, hj] using heq

-- CY : This theorem and `exists_reindex_weight_eq_of_isContiguous` has similar conclusion.
-- I have not thought hard about whether we can combine them.
open LinearEquiv in
theorem exists_reindex_weight_eq_of_eq_zero {n : ℕ} {w w' : Fin (n + 1) → k} [Invertible (2 : k)]
    (f : (weightedSumSquares k w).IsometryEquiv (weightedSumSquares k w'))
    (hw : ∃ i, w i = 0) :
    ∃ e e' : Fin (n + 1) ≃ Fin (n + 1),
      (∀ m, (weightedSumSquares k (w' ∘ e'))
        ((funCongrLeft k k e).trans (f.toLinearEquiv.trans (funCongrLeft k k e')) m) =
          (weightedSumSquares k (w ∘ e)) m) ∧
      (w ∘ e) 0 = (w' ∘ e') 0 := by
  obtain ⟨j, hj⟩ := exists_eq_zero_of_equivalent_of_zero ⟨f⟩ hw
  obtain ⟨i, hi⟩ := hw
  use Equiv.swap 0 i, Equiv.swap 0 j
  refine ⟨fun m ↦ ?_, by simp_all⟩
  rw [weightedSumSquares_comp_equiv w', weightedSumSquares_comp_equiv w]
  simp only [Equiv.symm_swap, trans_apply, funCongrLeft_apply,
    QuadraticMap.IsometryEquiv.coe_toLinearEquiv, QuadraticMap.comp_apply, coe_coe,
    QuadraticMap.weightedSumSquares_apply, LinearMap.funLeft_apply, Equiv.swap_apply_self,
    smul_eq_mul]
  have hm := f.map_app ((funCongrLeft k k (Equiv.swap 0 i)) m)
  simpa only [funCongrLeft_apply, QuadraticMap.weightedSumSquares_apply, LinearMap.funLeft_apply,
    smul_eq_mul] using hm

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
  rw [← hasseMinkowskiInvAux.eq_of_equiv w e, ← hasseMinkowskiInvAux.eq_of_equiv w' e']
  refine hasseMinkowskiInvAux.eq_of_equivalent_of_succ_eq ⟨e'fe⟩ (ih ?_) ?_
  · exact equivalent_weightedSumSquares_succ e'fe (weight_eq_of_basisFun_apply_eq e'fe h0)
  · simpa using (weight_eq_of_basisFun_apply_eq e'fe h0)

-- CY : This theorem and `eq_of_equivalent_of_IsContiguous` has similar conclusion.
-- I have not thought hard about whether we can combine them.
open LinearEquiv in
lemma hasseMinkowskiInvAux.eq_of_equivalent_of_zero {n : ℕ} {w w' : Fin (n + 1) → k}
    [Invertible (2 : k)] [hilbertSym.HasBilinHilbertSym k] [NeZero n]
    (f : (weightedSumSquares k w).IsometryEquiv (weightedSumSquares k w'))
    (ih : ∀ {w0 w0' : Fin n → k},
      (weightedSumSquares k w0).Equivalent (weightedSumSquares k w0') →
        hasseMinkowskiInvAux w0 = hasseMinkowskiInvAux w0')
    (hw : ∃ i, w i = 0) :
    hasseMinkowskiInvAux w = hasseMinkowskiInvAux w' := by
  obtain ⟨e, e', heq, h0⟩ := exists_reindex_weight_eq_of_eq_zero f hw
  let e'fe : (weightedSumSquares k (w ∘ e)).IsometryEquiv (weightedSumSquares k (w'∘ e')) :=
    ⟨(funCongrLeft k k e).trans (f.toLinearEquiv.trans (funCongrLeft k k e')), heq⟩
  rw [← hasseMinkowskiInvAux.eq_of_equiv w e, ← hasseMinkowskiInvAux.eq_of_equiv w' e']
  apply hasseMinkowskiInvAux.eq_of_equivalent_of_succ_eq ⟨e'fe⟩
    (ih (equivalent_weightedSumSquares_succ e'fe h0))
  simpa using h0

section hasseMinkowskiInvBasis

open Module

/-- The Hasse-Minkowski invariant of a quadratic form with respect to a basis. -/
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

/-- Generalize existing `QuadraticForm.isometryEquivWeightedSumSquares` from field to ring,
from vector space to module, and from basis indexed by `Fin (finrank K V)` to `ι`. -/
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

lemma hasseMinkowskiInvAux.eq_of_equivalent_of_chain {n : ℕ} {w w' : Fin (n + 1) → k}
    [Invertible (2 : k)] [hilbertSym.HasBilinHilbertSym k] [NeZero n]
    (f : (weightedSumSquares k w).IsometryEquiv (weightedSumSquares k w'))
    (ih : ∀ {w0 w0' : Fin n → k}, (weightedSumSquares k w0).Equivalent (weightedSumSquares k w0') →
      hasseMinkowskiInvAux w0 = hasseMinkowskiInvAux w0')
    (c : Module.Basis.Chain (weightedSumSquares k w')
      ((Pi.basisFun k (Fin (n + 1))).map f) (Pi.basisFun k (Fin (n + 1)))) :
    hasseMinkowskiInvAux w= hasseMinkowskiInvAux w' := by
  rw [hasseMinkowskiInvAux_Basis w, hasseMinkowskiInvAux_Basis w']
  have hb := f.isOrthoᵢ_map (weightedSumSquares_isOrthoᵢ_basisFun w)
  rw [hasseMinkowskiInvBasis_map f _ hb]
  exact hasseMinkowskiInvBasis_eq_of_chain hb (weightedSumSquares_isOrthoᵢ_basisFun w') ih c

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
    · exact Fin.exists_fin_two.mp
        (exists_eq_zero_of_equivalent_of_zero h (Fin.exists_fin_two.mpr h0))
    · exact Fin.exists_fin_two.mp
        (exists_eq_zero_of_equivalent_of_zero h.symm (Fin.exists_fin_two.mpr h0'))
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
  by_cases hw : ∃ i, w i = 0
  · obtain ⟨f⟩ := h
    exact hasseMinkowskiInvAux.eq_of_equivalent_of_zero f hasseMinkowskiInvAux.eq_of_equivalent hw
  have hw' : ¬∃ i, w' i = 0 := by
    contrapose! hw
    exact exists_eq_zero_of_equivalent_of_zero h.symm hw
  push Not at hw'
  have hNondeg : (weightedSumSquares (R := k) w').Nondegenerate := by
    apply (QuadraticMap.nondegenerate_iff_map_basis_ne_zero
      (weightedSumSquares_isOrthoᵢ_basisFun w')).mpr
    intro i
    simp only [Pi.basisFun_apply, QuadraticMap.weightedSumSquares_apply, smul_eq_mul, ne_eq]
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (fun h0 ↦ by simp at h0)]
    simp [hw']
  obtain ⟨f⟩ := h
  let b' := (Pi.basisFun k (Fin (r + 3)))
  let b := b'.map f.toLinearEquiv
  have hdim : 3 ≤ Fintype.card (Fin (r + 3)) := by simp
  have hSepLeft := (QuadraticMap.nondegenerate_associated_iff.mpr hNondeg).1
  have hb' := weightedSumSquares_isOrthoᵢ_basisFun w'
  have hb := f.isOrthoᵢ_map (weightedSumSquares_isOrthoᵢ_basisFun w)
  obtain ⟨c⟩ := Module.Basis.chain_of_nondegenerate hdim hNondeg hb hb'
  exact hasseMinkowskiInvAux.eq_of_equivalent_of_chain f hasseMinkowskiInvAux.eq_of_equivalent c

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
