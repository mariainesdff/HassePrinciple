/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
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

variable {k : Type*} [Field k] --[CharZero k]

-- Let `V` and `W` be `k`-vector spaces.
variable {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

-- Let `Q` be a quadratic form on `V`.
variable (Q : QuadraticForm k V)

/-- Auxiliary definition for `hasseMinkoskiInv`. -/
noncomputable def hasseMinkoskiInvAux {n : ℕ} (w : Fin n → kˣ) : ℤ :=
  ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2)

lemma hasseMinkoskiInvAux_def {n : ℕ} (w : Fin n → kˣ) :
    hasseMinkoskiInvAux w =
      ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2) := rfl

lemma hasseMinkoskiInvAux.eq_of_equivalent {n m : ℕ} {w : Fin n → kˣ} {w' : Fin m → kˣ}
    (h : (QuadraticMap.weightedSumSquares k w).Equivalent (QuadraticMap.weightedSumSquares k w')) :
    hasseMinkoskiInvAux w = hasseMinkoskiInvAux w' := by
  sorry

variable [Invertible (2 : k)] [FiniteDimensional k V] [FiniteDimensional k W]

/-- Let `Q` be a quadratic form on `V` such that `Q.associated` is `SeparatingLeft`, and
suppose that `Q` is equivalent to the diagonal quadratic form `a_1 X_1^2 + ⋯ + a_n X_n ^ 2`.
The Hasse-Minkowski invariant of `Q` is defined as the product `∏_{i < j} (a_i, a_j)`, where
`(·, ·)` denotes the Hilbert symbol.

This is denoted by `ε(Q)` in Serre's book. -/
noncomputable def hasseMinkoskiInv {Q : QuadraticForm k V}
    (hQ : LinearMap.SeparatingLeft Q.associated) : ℤ :=
  hasseMinkoskiInvAux (equivalent_weightedSumSquares_units_of_nondegenerate' Q hQ).choose

namespace hasseMinkoskiInv

open _root_.QuadraticMap

variable {Q : QuadraticForm k V} {Q' : QuadraticForm k W}
  (hQ : LinearMap.SeparatingLeft Q.associated)

lemma weightedSumSquares {n : ℕ} (w : Fin n → kˣ) :
    hasseMinkoskiInv
      (nondegenerate_associated_iff.mpr (nondegenerate_weightedSumSquares w)).1 =
      ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2) := by
  simp only [hasseMinkoskiInv, ← hasseMinkoskiInvAux_def w]
  exact hasseMinkoskiInvAux.eq_of_equivalent
    ((equivalent_weightedSumSquares_units_of_nondegenerate' (QuadraticMap.weightedSumSquares k w))
      (nondegenerate_associated_iff.mpr (nondegenerate_weightedSumSquares w)).1).choose_spec.symm

lemma weightedSumSquares_two (w : Fin 2 → kˣ) :
    hasseMinkoskiInv
      (nondegenerate_associated_iff.mpr (nondegenerate_weightedSumSquares w)).1 =
      hilbertSym (w 0 : k) (w 1) := by
  rw [hasseMinkoskiInv.weightedSumSquares, Finset.prod_eq_single (0, 1)
      (by grind) (fun h ↦ by simp at h)]

lemma weightedSumSquares_three (w : Fin 3 → kˣ) :
    hasseMinkoskiInv
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
  rw [hasseMinkoskiInv.weightedSumSquares,
    Finset.prod_congr h (g := fun p ↦ hilbertSym (w p.1 : k) (w p.2)) (by simp)]
  simp [mul_assoc]

lemma eq_of_equivalent_weightedSumSquares {n : ℕ} {w : Fin n → kˣ}
    (h : Q.Equivalent (QuadraticMap.weightedSumSquares k w)) :
    hasseMinkoskiInv hQ =
      hasseMinkoskiInv (LinearMap.separatingLeft_of_equivalent h hQ) := by
  sorry

lemma eq_of_equivalent (h : Q.Equivalent Q') :
    hasseMinkoskiInv hQ =
      hasseMinkoskiInv (LinearMap.separatingLeft_of_equivalent h hQ) := by
  sorry

lemma eq_one_or_neg_one :
    hasseMinkoskiInv hQ = 1 ∨ hasseMinkoskiInv hQ = - 1 := sorry

open Module TensorProduct in
lemma of_baseChange_weightedSumSquares {R : Type*} (A : Type*) [Field R]
    [Invertible (2 : R)] [Field A] [Invertible (2 : A)] [Algebra R A] (w : Fin 2 → Rˣ) :
    hasseMinkoskiInv
      ((nondegenerate_associated_iff.mpr
        (nondegenerate_baseChange (A := A) (nondegenerate_weightedSumSquares w))).1) =
      hilbertSym (algebraMap R A (w ⟨0, by omega⟩)) ( algebraMap R A (w ⟨1, by omega⟩)) := by
  have h2 : finrank A (A ⊗[R] (Fin 2 → R)) = 2 := by simp
  rw [hasseMinkoskiInv.eq_of_equivalent_weightedSumSquares
    (w := ![Units.map (algebraMap R A) (w ⟨0, by omega⟩),
       Units.map (algebraMap R A) (w ⟨1, by omega⟩)]) _
    (((baseChange_weightedSumSquares _ _ _).trans (Equivalent.refl _))), weightedSumSquares_two]
  simp

end hasseMinkoskiInv

open hilbertSym Module _root_.QuadraticMap
section Field

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : Q.Nondegenerate)

private lemma represents_zero_iff_of_rank_three_aux (b : Basis (Fin 3) K V) (hQ : Q.Nondegenerate)
    {w : Fin 3 → Kˣ} (hw : Q.Equivalent (weightedSumSquares K w))
    (heq : hilbertSym (-w 2 * w 0 : K) (-w 2 * w 1) = hilbertSym (-1) (-Q.discr b) *
        hasseMinkoskiInv (Q.nondegenerate_associated_iff.mpr hQ).1) :
    Q.Isotropic ↔ hilbertSym (-1) (-Q.discr b) =
        hasseMinkoskiInv (Q.nondegenerate_associated_iff.mpr hQ).1 := by
  have hw' : w = ![w 0, w 1, w 2] := List.ofFn_inj.mp rfl
  set s := hilbertSym (-1) (-Q.discr b)
  set ε := hasseMinkoskiInv (Q.nondegenerate_associated_iff.mpr hQ).1 with hε_def
  have hs1 : s = 1 ∨ s = -1 := eq_one_or_neg_one_of_ne_zero (by simp)
    (neg_ne_zero.mpr ((nondegenerate_iff_discr_ne_zero b).mp hQ))
  have hε1 : ε = 1 ∨ ε = -1 :=
    hasseMinkoskiInv.eq_one_or_neg_one (Q.nondegenerate_associated_iff.mpr hQ).1
  have hsε : s = ε ↔ s * ε = 1 := by
    rcases hs1 with hs1 | hs1 <;> rcases hε1 with hε1 | hε1 <;> simp [hs1, hε1]
  have hε : ε = hilbertSym (w 0 : K) (w 1) * hilbertSym (w 0 : K) (w 2) *
      hilbertSym (w 1 : K) (w 2) := by
    simp [ε, hasseMinkoskiInv.eq_of_equivalent _ hw,
      hasseMinkoskiInv.weightedSumSquares_three]
  rw [hw.isotropic_iff, hw', weightedSumSquares_isotropic_iff_hilbertSym_eq_one, hsε, heq]

end Field

namespace Real

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {Q : QuadraticForm ℝ V}
  (hQ : Q.Nondegenerate)

lemma represents_zero_iff_of_rank_three (b : Basis (Fin 3) ℝ V) :
    Q.Isotropic ↔
      hilbertSym (-1) (-Q.discr b) =
        hasseMinkoskiInv (Q.nondegenerate_associated_iff.mpr hQ).1 := by
  obtain ⟨w, hw⟩ := equivalent_weightedSumSquares_three_units_of_nondegenerate
    ( by simp [finrank_eq_card_basis b]) (Q.nondegenerate_associated_iff.mpr hQ).1
  -- Set up notation for readability
  let ⟨fw⟩ := hw
  let a₀ := w 0
  let a₁ := w 1
  let a₂ := w 2
  let u := ((LinearMap.toMatrix b (Pi.basisFun ℝ (Fin 3))) fw.toLinearEquiv).det
  set s := hilbertSym (-1) (-Q.discr b)
  set ε := hasseMinkoskiInv (Q.nondegenerate_associated_iff.mpr hQ).1 with hε_def
  have hε : ε = hilbertSym (a₀ : ℝ) a₁ * hilbertSym (a₀ : ℝ) a₂ * hilbertSym (a₁ : ℝ) a₂ := by
    simp [ε, hasseMinkoskiInv.eq_of_equivalent _ hw,
      hasseMinkoskiInv.weightedSumSquares_three, a₀, a₁, a₂]
  rw [represents_zero_iff_of_rank_three_aux b hQ hw]
  -- Computation using properties of the Hilbert Symbol
  calc hilbertSym (-a₂ * a₀ : ℝ) (-a₂ * a₁)
      _ = hilbertSym (-1 : ℝ) (- 1) * hilbertSym (-1 : ℝ) a₀ * hilbertSym (-1 : ℝ) a₁ *
          hilbertSym (a₂ : ℝ) a₂ *
          (hilbertSym (a₀ : ℝ) a₁ * hilbertSym (a₀ : ℝ) a₂ * hilbertSym (a₁ : ℝ) a₂) := by
          rw [← neg_one_mul (a₂ : ℝ)]
          simp only [real_mul_right_eq, real_mul_left_eq]
          rw [comm (a := (a₂ : ℝ)) (b := -1), comm (a := (a₀ : ℝ)) (b := -1),
            comm (a := (a₂ : ℝ)) (b := a₁)]
          ring_nf
          rw [sq_eq_one_iff.mpr (eq_one_or_neg_one_of_ne_zero (by simp) (by simp))]
          simp
      _ = hilbertSym (-1 : ℝ) (- 1) * hilbertSym (-1 : ℝ) a₀ * hilbertSym (-1 : ℝ) a₁ *
          hilbertSym (a₂ : ℝ) a₂ * ε := by simp [hε]
      _ = hilbertSym (-1 : ℝ) (- 1) * hilbertSym (-1 : ℝ) a₀ * hilbertSym (-1 : ℝ) a₁ *
          hilbertSym (-1 : ℝ) a₂ * ε := by
          congr 2
          rw [← left_neg_mul (a := -1)]
          simp
      _ = hilbertSym (-1 : ℝ) (- 1) * hilbertSym (-1 : ℝ) (a₀ * a₁ * a₂) * ε := by
        rw [real_mul_right_eq, real_mul_right_eq]
        ring
      _ = hilbertSym (-1 : ℝ) (- (a₀ * a₁ * a₂)) * ε := by
        rw [← neg_one_mul (_ * _), real_mul_right_eq (b := -1)]
      _ = hilbertSym (-1 : ℝ) (- (a₀ * a₁ * a₂ * u ^ 2)) * ε := by
        rw [← neg_mul _ ((u : ℝ) ^ 2), mul_right_square_eq]
        exact LinearEquiv.det_toMatrix_ne_zero _ _ _
      _ = s * ε := by simp [s, discr_three b fw, u, a₀, a₁, a₂]

lemma represents_iff_of_rank_two (b : Basis (Fin 2) ℝ V) (a : ℝ) :
    Q.represents a ↔
      hilbertSym a (-Q.discr b) =
        hasseMinkoskiInv (Q.nondegenerate_associated_iff.mpr hQ).1 := by
  sorry

end Real

namespace Padic

variable {p : ℕ} [Fact (Nat.Prime p)] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  [FiniteDimensional ℚ_[p] V] {Q : QuadraticForm ℚ_[p] V}
  (hQ : Q.Nondegenerate)

lemma represents_zero_iff_of_rank_three (b : Basis (Fin 3) ℚ_[p] V) :
    Q.Isotropic ↔
      hilbertSym (-1) (-Q.discr b) =
        hasseMinkoskiInv (Q.nondegenerate_associated_iff.mpr hQ).1 := by
  obtain ⟨w, hw⟩ := equivalent_weightedSumSquares_three_units_of_nondegenerate
    ( by simp [finrank_eq_card_basis b]) (Q.nondegenerate_associated_iff.mpr hQ).1
  -- Set up notation for readability
  let ⟨fw⟩ := hw
  let a₀ := w 0
  let a₁ := w 1
  let a₂ := w 2
  let u := ((LinearMap.toMatrix b (Pi.basisFun ℚ_[p] (Fin 3))) fw.toLinearEquiv).det
  set s := hilbertSym (-1) (-Q.discr b)
  set ε := hasseMinkoskiInv (Q.nondegenerate_associated_iff.mpr hQ).1 with hε_def
  have hε : ε = hilbertSym (a₀ : ℚ_[p]) a₁ * hilbertSym (a₀ : ℚ_[p]) a₂ *
      hilbertSym (a₁ : ℚ_[p]) a₂ := by
    simp [ε, hasseMinkoskiInv.eq_of_equivalent _ hw,
      hasseMinkoskiInv.weightedSumSquares_three, a₀, a₁, a₂]
  rw [represents_zero_iff_of_rank_three_aux b hQ hw]
  -- Computation using properties of the Hilbert Symbol
  calc hilbertSym (-a₂ * a₀ : ℚ_[p]) (-a₂ * a₁)
      _ = hilbertSym (-1 : ℚ_[p]) (- 1) * hilbertSym (-1 : ℚ_[p]) a₀ * hilbertSym (-1 : ℚ_[p]) a₁ *
          hilbertSym (a₂ : ℚ_[p]) a₂ * (hilbertSym (a₀ : ℚ_[p]) a₁ * hilbertSym (a₀ : ℚ_[p]) a₂ *
            hilbertSym (a₁ : ℚ_[p]) a₂) := by
          rw [← neg_one_mul (a₂ : ℚ_[p])]
          simp only [padic_mul_right_eq, padic_mul_left_eq]
          rw [comm (a := (a₂ : ℚ_[p])) (b := -1), comm (a := (a₀ : ℚ_[p])) (b := -1),
            comm (a := (a₂ : ℚ_[p])) (b := a₁)]
          ring_nf
          rw [sq_eq_one_iff.mpr (eq_one_or_neg_one_of_ne_zero (by simp) (by simp))]
          simp
      _ = hilbertSym (-1 : ℚ_[p]) (- 1) * hilbertSym (-1 : ℚ_[p]) a₀ * hilbertSym (-1 : ℚ_[p]) a₁ *
          hilbertSym (a₂ : ℚ_[p]) a₂ * ε := by simp [hε]
      _ = hilbertSym (-1 : ℚ_[p]) (- 1) * hilbertSym (-1 : ℚ_[p]) a₀ * hilbertSym (-1 : ℚ_[p]) a₁ *
          hilbertSym (-1 : ℚ_[p]) a₂ * ε := by
          congr 2
          rw [← left_neg_mul (a := -1)]
          simp
      _ = hilbertSym (-1 : ℚ_[p]) (- 1) * hilbertSym (-1 : ℚ_[p]) (a₀ * a₁ * a₂) * ε := by
        rw [padic_mul_right_eq, padic_mul_right_eq]
        ring
      _ = hilbertSym (-1 : ℚ_[p]) (- (a₀ * a₁ * a₂)) * ε := by
        rw [← neg_one_mul (_ * _), padic_mul_right_eq (b := -1)]
      _ = hilbertSym (-1 : ℚ_[p]) (- (a₀ * a₁ * a₂ * u ^ 2)) * ε := by
        rw [← neg_mul _ ((u : ℚ_[p]) ^ 2), mul_right_square_eq]
        exact LinearEquiv.det_toMatrix_ne_zero _ _ _
      _ = s * ε := by simp [s, discr_three b fw, u, a₀, a₁, a₂]

lemma represents_iff_of_rank_two (b : Basis (Fin 2) ℚ_[p] V) (a : ℚ_[p]) :
    Q.represents a ↔
      hilbertSym a (-Q.discr b) =
        hasseMinkoskiInv (Q.nondegenerate_associated_iff.mpr hQ).1 := by
  sorry

end Padic

end QuadraticForm
