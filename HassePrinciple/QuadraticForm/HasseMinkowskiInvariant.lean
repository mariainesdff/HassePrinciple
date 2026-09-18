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

/-! # The Hasse-Minkowski invariant -/

@[expose] public section

section Prelim

lemma LinearMap.separatingLeft_of_equivalent {R M M' N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M'] [AddCommGroup N] [Module R N]
    [Invertible (2 : R)] {Q : QuadraticMap R M N} {Q' : QuadraticMap R M' N} (h : Q.Equivalent Q')
    (hQ : LinearMap.SeparatingLeft Q.associated) :
    LinearMap.SeparatingLeft Q'.associated := by
  sorry

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
noncomputable def hasseMinkowskiInvAux {n : ℕ} (w : Fin n → kˣ) : ℤ :=
  ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2)

lemma hasseMinkowskiInvAux_def {n : ℕ} (w : Fin n → kˣ) :
    hasseMinkowskiInvAux w =
      ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2) := rfl

lemma hasseMinkowskiInvAux.eq_of_equivalent {n m : ℕ} {w : Fin n → kˣ} {w' : Fin m → kˣ}
    (h : (QuadraticMap.weightedSumSquares k w).Equivalent (QuadraticMap.weightedSumSquares k w')) :
    hasseMinkowskiInvAux w = hasseMinkowskiInvAux w' := by
  sorry

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
  hasseMinkowskiInvAux (equivalent_weightedSumSquares_units_of_nondegenerate' Q hQ).choose

namespace hasseMinkowskiInv

open _root_.QuadraticMap

variable {Q : QuadraticForm k V} {Q' : QuadraticForm k W}
  (hQ : LinearMap.SeparatingLeft Q.associated)

lemma weightedSumSquares {n : ℕ} (w : Fin n → kˣ) :
    hasseMinkowskiInv
      (nondegenerate_associated_iff.mpr (nondegenerate_weightedSumSquares w)).1 =
      ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2) := by
  simp only [hasseMinkowskiInv, ← hasseMinkowskiInvAux_def w]
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
      have h1 : p.1 = 0 ∨ p.1 = 1 ∨ p.1 = 2  := by omega
      have h2 : p.2 = 0 ∨ p.2 = 1 ∨ p.2 = 2  := by omega
      aesop
  rw [hasseMinkowskiInv.weightedSumSquares,
    Finset.prod_congr h (g := fun p ↦ hilbertSym (w p.1 : k) (w p.2)) (by simp)]
  simp [mul_assoc]

lemma eq_of_equivalent_weightedSumSquares {n : ℕ} {w : Fin n → kˣ}
    (h : Q.Equivalent (QuadraticMap.weightedSumSquares k w)) :
    hasseMinkowskiInv hQ =
      hasseMinkowskiInv (LinearMap.separatingLeft_of_equivalent h hQ) := by
  sorry

lemma eq_of_equivalent (h : Q.Equivalent Q') :
    hasseMinkowskiInv hQ =
      hasseMinkowskiInv (LinearMap.separatingLeft_of_equivalent h hQ) := by
  sorry

lemma eq_one_or_neg_one :
    hasseMinkowskiInv hQ = 1 ∨ hasseMinkowskiInv hQ = - 1 := sorry

open Module TensorProduct in
lemma of_baseChange_weightedSumSquares {R : Type*} (A : Type*) [Field R]
    [Invertible (2 : R)] [Field A] [Invertible (2 : A)] [Algebra R A] (w : Fin 2 → Rˣ) :
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
lemma prod_rank_one [HasBilinHilbertSym k] (b : Basis (Fin 2) k V) (a : kˣ) (h : Q.Nondegenerate) :
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

variable {Q} [CharZero k] (hQ : Q.Nondegenerate)

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

variable [HasBilinHilbertSym k]

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
