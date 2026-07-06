/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.HilbertSymbol.Basic
public import HassePrinciple.QuadraticForm.Basic

@[expose] public section

namespace QuadraticForm

open Module _root_.QuadraticMap

section Rank3

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  (hQ : Q.Nondegenerate)

lemma discr_three (b : Basis (Fin 3) K V) {w : Fin 3 → Kˣ}
    (fw : Q.IsometryEquiv (weightedSumSquares K w)) :
    discr b Q = w 0 * w 1 * w 2 *
      ((LinearMap.toMatrix b (Pi.basisFun K (Fin 3))) fw.toLinearEquiv).det ^ 2 := by
  rw [IsometryEquiv.discr (Equiv.refl _) b (Pi.basisFun K (Fin 3)) fw]
  simp [weightedSumSquares_discr, Units.smul_def, smul_eq_mul, mul_one, Fin.prod_univ_three]

lemma weightedSumSquares_isotropic_iff_hilbertSym_eq_one' {R : Type*} [Field R] (a b : Rˣ) :
    (weightedSumSquares R ![a, b, 1]).Isotropic ↔ hilbertSym (-a : R) (-b) = 1 := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, ← represents_zero_iff_isotropic, represents,
    weightedSumSquares_apply, Units.smul_def, smul_eq_mul, Fin.sum_univ_three, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Units.val_one, one_mul, ne_eq,
    hilbertSym, neg_mul, neg_eq_zero, Units.ne_zero, or_self, ↓reduceIte, Prod.mk.injEq, not_and,
    sub_neg_eq_add, Int.reduceNeg, ite_eq_left_iff, not_exists, reduceCtorEq, imp_false,
    not_forall, not_not, pow_two]
  refine ⟨fun ⟨x, hx, hx0⟩ ↦ ⟨x 2, x 0, x 1, ?_, ?_⟩,
      fun ⟨x, y, z, h0, h⟩ ↦ ⟨![y, z, x], ?_, by aesop⟩⟩
  · intros h0 h1 h2
    simp only [funext_iff, Fin.forall_iff, Pi.zero_apply, not_forall] at hx0
    grind
  · simp only [← hx]
    ring
  · simp only [← h, Matrix.cons_val]
    ring

lemma weightedSumSquares_isotropic_iff_hilbertSym_eq_one {R : Type*} [Field R] (a b c : Rˣ) :
    (weightedSumSquares R ![a, b, c]).Isotropic ↔ hilbertSym (-c * a : R) (-c * b) = 1 := by
  let c' : Rˣˣ := ⟨c, c⁻¹, by simp, by simp⟩
  rw [mul_unit_isotropic_iff (a := c) (w' := ![c * a, c * b, c * c])
      (by simp [Fin.forall_fin_succ]),
    (weightedSumSquares_mul_squares_equivalent  (w' := ![c * a, c * b, 1]) ![1, 1, c']
      (by simp [Fin.forall_fin_succ, pow_two, c'])).isotropic_iff,
    weightedSumSquares_isotropic_iff_hilbertSym_eq_one']
  simp

theorem equivalent_weightedSumSquares_three_units_of_nondegenerate {K V : Type*}
    [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V] (hr : finrank K V = 3)
    {Q : QuadraticForm K V} (hQ : LinearMap.SeparatingLeft (QuadraticMap.associated Q)) :
    ∃ (w : Fin 3 → Kˣ), QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares K w) := by
  have : FiniteDimensional K V := finite_of_finrank_eq_succ hr
  obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  refine ⟨![w ⟨0, by omega⟩, w ⟨1, by omega⟩, w ⟨2, by omega⟩], ?_⟩
  apply hw.trans
  apply (weightedSumSquaresCongr'_equivalent (finCongr hr) ?_)
  ext n
  cases n with
  | mk n hn =>
    have hn : n = 0 ∨ n = 1 ∨ n = 2  := by omega
    aesop

end Rank3

end QuadraticForm
