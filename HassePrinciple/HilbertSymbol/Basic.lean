/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.Padics.Lemmas
public import HassePrinciple.Padics.Legendre
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-! # The Hilbert symbol -/

@[expose] public section

-- Notation:
namespace PadicInt

/-- epsilon(u) is the class modulo 2 of (u-1)/2. -/
noncomputable abbrev epsilon (u : (PadicInt 2)ˣ) : ℤ :=
  if (u.val).appr 2 % 4 = 1 then 0 else 1

/-- omega(u) is the class modulo 2 of (u^2-1)/8. -/
noncomputable abbrev omega (u : (PadicInt 2)ˣ) : ℤ :=
  if (u.val).appr 3 % 8 = 1 ∨ (u.val).appr 3 % 8 = 7 then 0 else 1

end PadicInt

-- `k` is a field and typically will be either `ℝ` or `ℚ_[p]`, but we need less for the definition.

/-- The Hilbert symbol of a and b in k is defined as 0 if either a or b is 0, and it is 1 if there
is a nontrivial solution to the equation `z^2 - a*x^2 - b*y^2 = 0`, and -1 otherwise. -/
noncomputable def hilbertSym {k : Type*} [Field k] (a b : k) : ℤ := by
  classical exact if a = 0 ∨ b = 0 then 0
    else if ∃ z x y : k, (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 then 1
    else -1

namespace hilbertSym

section Field

variable {k : Type*} [Field k] {a b : k} (a' b' : k)

/-- If `a` and `b` are nonzero, then `hilbertSym a b` is nonzero. -/
lemma ne_zero_of_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : hilbertSym a b ≠ 0 := by
  simp [hilbertSym, ha, hb]
  split_ifs <;> simp

/-- If `a` and `b` are multiplied by a square, the Hilbert symbol is unchanged. -/
@[simp]
lemma mul_square_eq (ha' : a' ≠ 0) (hb' : b' ≠ 0) :
  hilbertSym (a * a'^2) (b * b'^2) = hilbertSym a b := by
  simp only [hilbertSym, mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, Prod.mk.injEq, not_and, Int.reduceNeg]
  by_cases ha : a = 0
  · simp [ha]
  · by_cases hb : b = 0
    · simp [hb]
    · simp only [mul_eq_zero, ha, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
        false_or, hb, Prod.mk.injEq, not_and, Int.reduceNeg, or_self, ↓reduceIte]
      rw [if_neg (by aesop)]
      split_ifs with h h' h'
      · rfl
      · obtain ⟨z, x, y, h0, heq⟩ := h
        exact h' ⟨z, (a' * x), (b' * y), by aesop, by rw [← heq]; ring⟩
      · obtain ⟨z, x, y, h0, heq⟩ := h'
        apply h ⟨ z, (1/a'*x), (1/b'*y), by aesop, by field_simp; rw [heq]⟩
      · rfl

/-- The Hilbert symbol is commutative. -/
lemma comm : hilbertSym a b = hilbertSym b a := by
  simp only [hilbertSym, ne_eq, Prod.mk.injEq, not_and, Int.reduceNeg]
  by_cases ha : a = 0
  · simp [ha]
  · by_cases hb : b = 0
    · simp [hb]
    · simp only [ha, hb, or_self, ↓reduceIte, Prod.mk.injEq, not_and, Int.reduceNeg]
      split_ifs with h h' h'
      · rfl
      · obtain ⟨z, x, y, h0, heq⟩ := h
        exact h' ⟨z, y, x, by aesop, by rw [← heq]; ring⟩
      · obtain ⟨z, x, y, h0, heq⟩ := h'
        exact h ⟨z, y, x, by aesop, by rw [← heq]; ring⟩
      · rfl

/-
# Basic properties of the Hilbert symbol
-/

/- split into when b is and is not a square-/

/- The Hilbert symbol of a and b (both nonzero) equals 1 if and only if a is a norm from the
  quadratic algebra `QuadraticAlgebra k b 0`. -/
theorem eq_one_iff (ha : a ≠ 0) (hb : b ≠ 0) (hc : ¬IsSquare b) :
    hilbertSym a b = 1 ↔ ∃ t : QuadraticAlgebra k b 0, a = QuadraticAlgebra.norm t := by
  rw [hilbertSym, if_neg (by simp [ha, hb])]
  refine ⟨fun hhilb ↦ ?_, fun hnorm ↦ ?_⟩
  · simp only [ne_eq, Prod.mk.injEq, not_and, Int.reduceNeg, ite_eq_left_iff, not_exists,
      reduceCtorEq, imp_false, not_forall, not_not] at hhilb
    obtain ⟨z, x, y, hnonzero, heq⟩ := hhilb
    use (QuadraticAlgebra.mk (z/x) (y/x))
    symm
    rw [sub_eq_zero] at heq
    have hx : x ≠ 0 := by
      simp only [ne_eq]
      contrapose heq
      rw [heq]
      ring_nf
      contrapose hc
      unfold IsSquare
      use z/y
      field_simp
      rw [hc]
      field_simp
      rw [div_self]
      simp only [ne_eq]
      aesop
    calc
      QuadraticAlgebra.norm { re := z / x, im := y / x }
      =  z / x * (z / x) - b * (y / x) * (y / x)  := by
        simp only [QuadraticAlgebra.norm, zero_mul, add_zero, MonoidHom.coe_mk, OneHom.coe_mk]
      _ = z^2/x^2 - b * (y^2/x^2) := by field_simp
      _ = (z^2-b*y^2)/x^2 := by ring
      _ = a := by
        rw [← heq, sub_sub_cancel]
        field_simp
  · rw [if_pos]
    obtain ⟨⟨p, q⟩, hnorm'⟩ := hnorm
    use p, 1, q, by aesop
    simp only [QuadraticAlgebra.norm_def, zero_mul, add_zero] at hnorm'
    rw [hnorm']
    ring

/-- The Hilbert symbol of a and b (both nonzero) equals 1 if b is a square. -/
@[simp]
theorem right_square_eq_one (ha : a ≠ 0) (hb : b ≠ 0) : hilbertSym a (b ^ 2) = 1 := by
  rw [hilbertSym, if_neg (by aesop), if_pos]
  use b, 0, 1
  aesop


/-- The Hilbert symbol of a and -a, with a nonzero, equals 1. -/
@[simp]
theorem right_neg_self_eq_one (ha : a ≠ 0) : hilbertSym a (-a) = 1 := by
  rw [hilbertSym, if_neg (by simp [ha]), if_pos]
  use 0, 1, 1
  aesop

/-- The Hilbert symbol of a and 1-a, with a different from 0 and 1, equals 1. -/
@[simp]
theorem right_one_minus_self_eq_one (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    hilbertSym a (1 - a) = 1 := by
  rw [hilbertSym, if_neg (by simp [ha0, sub_ne_zero.mpr ha1.symm]), if_pos]
  use 1, 1, 1
  aesop

-- adding 2 lemmas to help with right_mul_eq_of_eq_one.
theorem eq_one_or_neg_one (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b = 1 ∨ hilbertSym a b = -1 := by
  unfold hilbertSym
  split_ifs with h1 h2
  repeat aesop

theorem eq_neg_one_iff_not_one (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b = -1 ↔ ¬hilbertSym a b = 1 := by
  constructor
  · intro h
    rw [h]
    simp only [Int.reduceNeg, reduceCtorEq, not_false_eq_true]
  · intro h
    have: hilbertSym a b = 1 ∨ hilbertSym a b = -1 := eq_one_or_neg_one ha hb
    aesop

/-- If the Hilbert symbol of a and b equals 1, then the Hilbert symbol of a and b * b' equals the
Hilbert symbol of a and b'. -/
@[simp]
theorem right_mul_eq_of_eq_one (hab : hilbertSym a b = 1) :
    hilbertSym a (b * b') = hilbertSym a b' := by
  by_cases hb' : (b' = 0)
  · aesop
  · have habnzero : a ≠ 0 ∧ b ≠ 0 := by
      unfold hilbertSym at hab
      aesop
    rw [comm]
    nth_rw 2 [comm]
    rw [comm] at hab
    obtain ⟨ hanzero, hbnzero ⟩ := habnzero
    by_cases ha: IsSquare a
    · obtain ⟨ sqrta, sqrtadef⟩ := ha
      rw [sqrtadef, ← pow_two, right_square_eq_one, right_square_eq_one]
      repeat
      · aesop
    · rw [eq_one_iff hbnzero hanzero ha] at hab
      obtain ⟨ t, ht⟩ := hab
      by_cases hbb'zero : b*b' = 0
      · aesop
      · by_cases hb'a : hilbertSym b' a = 1
        · have hexist : ∃ t : QuadraticAlgebra k a 0, b' = QuadraticAlgebra.norm t := by
            rw [← eq_one_iff]
            · exact hb'a
            · exact hb'
            · exact hanzero
            · exact ha
          obtain ⟨ t', ht'⟩ := hexist
          have hnorm : (b*b') = QuadraticAlgebra.norm (t*t') := by
            simp only [map_mul, ht, ht']
          rw [hb'a, eq_one_iff]
          · use (t*t')
          · simp [hbb'zero]
          · exact hanzero
          · exact ha
        · have hnexist : ¬∃ t : QuadraticAlgebra k a 0, b' = QuadraticAlgebra.norm t := by
            rw [← eq_one_iff]
            · exact hb'a
            · exact hb'
            · exact hanzero
            · exact ha
          have hb'aone : hilbertSym b' a = - 1 := by
            rw [eq_neg_one_iff_not_one]
            · exact hb'a
            · aesop
            · exact hanzero
          rw [hb'aone, eq_neg_one_iff_not_one]
          · have: hilbertSym a b = 1 ∨ hilbertSym a b = -1 := by
              apply eq_one_or_neg_one hanzero hbnzero
            rw [eq_one_iff]
            · contrapose hnexist
              obtain ⟨ tt', tt'norm⟩ := hnexist
              use tt'*(1/t)
              simp only [map_mul, ← tt'norm]
              field_simp
              have Hab : Fact (∀(r : k), r^2 ≠ a + 0 * r) := by
                rw [fact_iff]
                intro r
                aesop
              rw [ht, ← map_mul]
              have htnzero: t≠ 0 := by
                contrapose ht
                rw [ht]
                aesop
              have tinv: t*(1/t)=1 := by
                rw [mul_one_div_cancel htnzero]
              rw [tinv]
              exact Eq.symm QuadraticAlgebra.norm_one
            · aesop
            · exact hanzero
            · exact ha
          · aesop
          · exact hanzero

/-- The Hilbert symbol of a and -a*b, equals the Hilbert symbol of a and b. -/
@[simp]
theorem right_neg_mul : hilbertSym a (- (a * b)) = hilbertSym a b := by
  by_cases hzero : a = 0
  · simp only [hzero, zero_mul, neg_zero]
    unfold hilbertSym
    aesop
  · have hnega : hilbertSym a (-a) = 1 := by
      apply right_neg_self_eq_one
      simp only [ne_eq]
      exact hzero
    rw [← neg_mul]
    exact right_mul_eq_of_eq_one b hnega

/-- If a is different from 1, then the Hilbert symbol of a and (1-a)*b equals the Hilbert symbol of
a and b. -/
@[simp]
theorem right_minus_self_mul (ha : a ≠ 1) :
    hilbertSym a ((1 - a) * b) = hilbertSym a b := by
  by_cases hzero : a = 0 <;> aesop

section Bilin

variable (k) in
/-- We say that `HasBilinHilbertSym k` if the Hilbert symbol on `k` is bilinear, i.e., if
  `hilbertSym (a * a') b = hilbertSym a b * hilbertSym a' b` for all `a, a', b` in `k`.
  Note that, by the commutativity property of the Hilbert symbol, this also implies
  `hilbertSym a (b * b') = hilbertSym a b * hilbertSym a b'` for all `a, b, b'` in k. -/
class HasBilinHilbertSym : Prop where
  mul_left_eq {a a' b : k} : hilbertSym (a * a') b = hilbertSym a b * hilbertSym a' b

lemma HasBilinHilbertSym.mul_right_eq [HasBilinHilbertSym k] :
    hilbertSym a (b * b') = hilbertSym a b * hilbertSym a b' := by
  rw [comm, mul_left_eq, comm, comm (b := b')]

end Bilin

section Bilin

variable (k) in
/-- We say that `HasBilinHilbertSym k` if the Hilbert symbol on `k` is bilinear, i.e., if
  `hilbertSym (a * a') b = hilbertSym a b * hilbertSym a' b` for all `a, a', b` in `k`.
  Note that, by the commutativity property of the Hilbert symbol, this also implies
  `hilbertSym a (b * b') = hilbertSym a b * hilbertSym a b'` for all `a, b, b'` in k. -/
class HasBilinHilbertSym : Prop where
  mul_left_eq {a a' b : k} : hilbertSym (a * a') b = hilbertSym a b * hilbertSym a' b

lemma HasBilinHilbertSym.mul_right_eq [HasBilinHilbertSym k] :
    hilbertSym a (b * b') = hilbertSym a b * hilbertSym a b' := by
  rw [comm, mul_left_eq, comm, comm (b := b')]

end Bilin

end Field

/-
## Local properties: computation of the Hilbert symbol in the real and p-adic cases
-/

/-- If k = ℝ, and a and b are nonzero, then the Hilbert symbol equals 1 if and only if either a or
b is positive. -/
theorem real_eq {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b = if 0 < a ∨ 0 < b then 1 else -1 := by
  split_ifs with h
  · wlog ha_pos : 0 < a with h1
    · rw [comm, h1 hb ha (by tauto) (by tauto)]
    simp only [hilbertSym, ha, hb, or_self, reduceIte, ne_eq, Prod.mk.injEq, not_and,
      Int.reduceNeg, ite_eq_left_iff, not_exists, reduceCtorEq, imp_false, not_forall,
      Decidable.not_not]
    exact ⟨Real.sqrt a, 1, 0, by simp, by simp [Real.sq_sqrt (by linarith)]⟩
  · simp only [not_or, not_lt] at h
    simp only [hilbertSym, ha, hb, or_self, ↓reduceIte, ne_eq, Prod.mk.injEq, not_and, sub_sub,
      Int.reduceNeg, ite_eq_right_iff, reduceCtorEq, imp_false, not_exists,
      sub_eq_add_neg _ ( _ + _)]
    intro z x y h0
    have : 0 ≤ z ^ 2 := by positivity
    have {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hadd : r + s = 0) : r = 0 ∧ s = 0 :=
      (add_eq_zero_iff_of_nonneg hr hs).mp hadd
    have : 0 ≤ -a * x^2 := by positivity [Left.nonneg_neg_iff.mpr h.1]
    have : 0 ≤ -b * y^2 := by positivity [Left.nonneg_neg_iff.mpr h.2]
    grind

instance _root_.Real.instHasBilinHilbertSym : HasBilinHilbertSym ℝ where
  mul_left_eq {a a' b} := by
    by_cases h0 : a = 0 ∨ a' = 0 ∨ b = 0
    · rcases h0 with h0 | h0 | h0 <;> simp [hilbertSym, h0]
    · simp  only [not_or] at h0
      obtain ⟨ha, ha', hb⟩ := h0
      rw [real_eq ha hb, real_eq ha' hb, real_eq (by positivity) hb]
      rcases lt_or_gt_of_ne (Ne.symm ha) with ha | ha
      · simp [ha]
      · by_cases hb0 : 0 < b
        · simp [hb0]
        · simp [not_lt.mpr ha.le, hb0]
          by_cases ha'0 : 0 < a'
          · simp [ha'0, ha.le]
          · simp [ha'0, mul_pos_of_neg_of_neg ha (lt_of_le_of_ne (not_lt.mp ha'0) ha')]

end Real

section Padic

variable {p : ℕ} [hp : Fact (Nat.Prime p)] {a b a' b' : (ℚ_[p])}

open Padic PadicInt
section odd

variable {p : ℕ} [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) {x y : (ℚ_[p])} (hx : x ≠ 0) (hy : y ≠ 0)

/-- Main theorem for odd p, case v(x)=0, v(y)=0. -/
lemma padic_odd_case00 (hx0 : x.valuation = 0) (hy0 : y.valuation = 0) :
    (hilbertSym x y : ℚ) =
      Int.negOnePow (valuation (x : ℚ_[p]) * valuation (y : ℚ_[p]) * epsilon (p2 hp2)) *
      (PadicInt.legendreSym (unitPart (Units.mk0 x hx) : ℤ_[p])) ^ (valuation (y : ℚ_[p])) *
      (PadicInt.legendreSym (unitPart (Units.mk0 y hy) : ℤ_[p])) ^ (valuation (x : ℚ_[p]))  := by
  sorry

/-- Main theorem for odd p, case v(x)=1, v(y)=0. -/
lemma padic_odd_case10 (hx1 : valuation (x : ℚ_[p]) = 1) (hy0 : valuation (y : ℚ_[p]) = 0) :
    (hilbertSym x y : ℚ) =
      Int.negOnePow (valuation (x : ℚ_[p]) * valuation (y : ℚ_[p]) * epsilon (p2 hp2)) *
      (PadicInt.legendreSym (unitPart (Units.mk0 x hx) : ℤ_[p])) ^ (valuation (y : ℚ_[p])) *
      (PadicInt.legendreSym (unitPart (Units.mk0 y hy) : ℤ_[p])) ^ (valuation (x : ℚ_[p]))  := by
  sorry

/-- Main theorem for odd p, case v(x)=1, v(y)=1. -/
lemma padic_odd_case11 (hx1 : valuation (x : ℚ_[p]) = 1) (hy1 : valuation (y : ℚ_[p]) = 1) :
    (hilbertSym x y : ℚ) =
    Int.negOnePow (valuation (x : ℚ_[p]) * valuation (y : ℚ_[p]) * epsilon (p2 hp2)) *
      (PadicInt.legendreSym (unitPart (Units.mk0 x hx) : ℤ_[p])) ^ (valuation (y : ℚ_[p])) *
      (PadicInt.legendreSym (unitPart (Units.mk0 y hy) : ℤ_[p])) ^ (valuation (x : ℚ_[p]))  := by
  sorry

/-- If p is an odd prime and x, y are nonzero in ℚ_[p], then the Hilbert symbol of x and y equals
`(-1) ^ v(x) * v(y) * ε(p) ` times the product of the Legendre symbol of the unit part of x to v(y)
times the Legendre symbol of the unit part of y to v(x). -/
theorem padic_odd_eq :
    (hilbertSym x y : ℚ) =
      Int.negOnePow (valuation (x : ℚ_[p]) * valuation (y : ℚ_[p]) * epsilon (p2 hp2)) *
      (PadicInt.legendreSym (unitPart (Units.mk0 x hx) : ℤ_[p])) ^ (valuation (y : ℚ_[p])) *
      (PadicInt.legendreSym (unitPart (Units.mk0 y hy)  : ℤ_[p])) ^ (valuation (x : ℚ_[p])) := by
  sorry

end odd

section two

variable {x y : (ℚ_[2])} (hx : x ≠ 0) (hy : y ≠ 0)

/-- Main theorem for p=2, case v(x)=0, v(y)=0. -/
lemma two_adic_case00 (hx0 : valuation (x : ℚ_[2]) = 0) (hy0 : valuation (y : ℚ_[2]) = 0) :
    hilbertSym x y = Int.negOnePow (epsilon (unitPart (Units.mk0 x hx)) *
      epsilon (unitPart (Units.mk0 y hy)) + valuation (x : ℚ_[2]) *
      omega (unitPart (Units.mk0 y hy)) + valuation (y : ℚ_[2]) *
      omega (unitPart (Units.mk0 x hx))) := by
  sorry

/-- Main theorem for p=2, case v(x)=1, v(y)=0. -/
lemma two_adic_case10 (hx1 : valuation (x : ℚ_[2]) = 1) (hy0 : valuation (y : ℚ_[2]) = 0) :
    hilbertSym x y = Int.negOnePow (epsilon (unitPart (Units.mk0 x hx)) *
      epsilon (unitPart (Units.mk0 y hy)) + valuation (x : ℚ_[2]) *
      omega (unitPart (Units.mk0 y hy)) + valuation (y : ℚ_[2]) *
      omega (unitPart (Units.mk0 x hx))) := by
  sorry

/-- Main theorem for p=2, case v(x)=1, v(y)=1. -/
lemma two_adic_case11 (hx1 : valuation (x : ℚ_[2]) = 1) (hy1 : valuation (y : ℚ_[2]) = 1) :
    hilbertSym x y = Int.negOnePow (epsilon (unitPart (Units.mk0 x hx)) *
      epsilon (unitPart (Units.mk0 y hy)) + valuation (x : ℚ_[2]) *
      omega (unitPart (Units.mk0 y hy)) + valuation (y : ℚ_[2]) *
      omega (unitPart (Units.mk0 x hx))) := by
  sorry

open PadicInt

/-- If x, y are nonzero in ℚ_[2], then the Hilbert symbol of x and y equals
`(-1) ^ (ε(u_x)ε(u_y) + v(x)ω(u_y) + v(y)ω(u_x))`, where u_x, u_y are the unit parts of x, y
respectively. -/
theorem two_adic_eq :
    hilbertSym x y = Int.negOnePow (PadicInt.epsilon (unitPart (Units.mk0 x hx)) *
      epsilon (unitPart (Units.mk0 y hy)) + valuation (x : ℚ_[2]) *
      omega (unitPart (Units.mk0 y hy)) + valuation (y : ℚ_[2]) *
      omega (unitPart (Units.mk0 x hx))) := by
  sorry

end two

instance _root_.Padic.instHasBilinHilbertSym : HasBilinHilbertSym ℚ_[p] where
  mul_left_eq {a a' b} := by
    sorry

end Padic

/-
# Global properties of the Hilbert symbol
-/
open Nat

/-- For `a, b : ℚ`, and for a prime `p : ℕ`, `atP a b p` denotes the Hilbert symbol of `a` and `b`
computed in `ℚ_[p]`. -/
noncomputable abbrev atP (a b : ℚ) (p : ℕ) [hp : Fact (Nat.Prime p)] : ℤ :=
  hilbertSym (a : ℚ_[p]) (b : ℚ_[p])

/-- For `a, b : ℚ`, `atInfty a b` the Hilbert symbol of `a` and `b` computed in `ℝ`. -/
noncomputable abbrev atInfty (a b : ℚ) : ℤ := hilbertSym (a : ℝ) (b : ℝ)

/-- The instance that provides the fact that the nth prime is prime. -/
scoped instance fact_prime (p : Nat.Primes) : Fact (Nat.Prime p) := fact_iff.mpr p.2

/-- valuation is `0' at `p' when `x' is `-1' or a prime `≠ p' -/
lemma padicValRat_special_eq_zero {p : ℕ} [Fact (Nat.Prime p)]
    {x : ℚ} (hx : x = -1 ∨ ∃ r : ℕ, Nat.Prime r ∧ x = r ∧ p ≠ r) :
    padicValRat p x = 0 := by
  rcases hx with rfl | ⟨r, hr, rfl, hpr⟩
  · simp only [padicValRat.neg, padicValRat.one]
  · have hfactr : Fact (Nat.Prime r) := ⟨hr⟩
    rw [← padicValRat_of_nat]
    norm_cast
    exact padicValNat_primes hpr

/-- `x ≠ 0' in `ℚ_[p]' when `x' is `-1' or a prime -/
lemma special_ne_zero {p : ℕ} [Fact (Nat.Prime p)]
    {x : ℚ} (hx : x = -1 ∨ ∃ r : ℕ, Nat.Prime r ∧ x = r) :
    (x : ℚ_[p]) ≠ 0 := by
  rcases hx with rfl | ⟨r, hr, rfl⟩
  · simp only [Rat.cast_neg, Rat.cast_one, ne_eq, neg_eq_zero, one_ne_zero, not_false_eq_true]
  · simp only [ne_eq, Rat.cast_eq_zero]
    exact_mod_cast hr.ne_zero

/-- the actual Hilbert symbol computation, once both valuations vanish. -/
lemma hilbertSym_special_eq_one {p : ℕ} [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    {x y : ℚ} (hx : (x : ℚ_[p]) ≠ 0) (hy : (y : ℚ_[p]) ≠ 0)
    (hvx : padicValRat p x = 0) (hvy : padicValRat p y = 0) :
    atP x y p = 1 := by
  have hval_cast_x : valuation (x : ℚ_[p]) = 0 := by
    rw [Padic.valuation_ratCast, hvx]
  have hval_cast_y : valuation (y : ℚ_[p]) = 0 := by
    rw [Padic.valuation_ratCast, hvy]
  have castkey : (hilbertSym (x : ℚ_[p]) (y : ℚ_[p]) : ℚ) = 1 := by
    rw [padic_odd_eq hp2 hx hy, hval_cast_x, hval_cast_y]
    simp only [mul_zero, mul_ite, val_mkUnits, mul_one, ite_self,
      Int.negOnePow_zero, Units.val_one, Int.cast_one, zpow_zero]
  exact_mod_cast castkey

/-- `atP x 1 p = 1', needed for the n = 1 base case -/
lemma hilbertSym_one_right {p : ℕ} [Fact (Nat.Prime p)]
    {x : ℚ} (hx : (x : ℚ_[p]) ≠ 0) :
    atP x 1 p = 1 := by
  unfold atP
  change hilbertSym (x : ℚ_[p]) (1 : ℚ_[p]) = 1
  unfold hilbertSym
  rw [if_neg (not_or.mpr ⟨hx, by norm_num⟩), if_pos ⟨1, 0, 1, by simp, by ring⟩]

/-- For all but finitely many primes `p`, the Hilbert symbol of `a` and `b` at `p` is `1`. -/
theorem almost_all_one (a b : ℚˣ) :
    ∀ᶠ (p : Nat.Primes) in Filter.cofinite, atP a b p = 1 := by
  suffices hreduction : ∀ c d : ℚˣ, (c = -1 ∨ (∃ r : ℕ, Nat.Prime r ∧ (c : ℚ) = r)) →
    (d = -1 ∨ (∃ q : ℕ, Nat.Prime q ∧ (d : ℚ) = q)) →
    (∀ᶠ (p : Nat.Primes) in Filter.cofinite, atP c d p = 1) by
      · have one_reduced_general : ∀ (c₀ : ℚˣ),
          (∀ d : ℚˣ, (d = -1 ∨ ∃ q, Nat.Prime q ∧ (↑d : ℚ) = ↑q) →
          ∀ᶠ p : Nat.Primes in Filter.cofinite, atP ↑c₀ ↑d ↑p = 1) →
          ∀ (b' : ℚˣ), ∀ᶠ p : Nat.Primes in Filter.cofinite, atP ↑c₀  ↑b' ↑p = 1 := by
          intro c₀ hbase b'
          set N := (b' : ℚ).num with hN; set D := (b' : ℚ).den with hD
          have hDnonzero : D ≠ 0 := (b':ℚ).den_ne_zero
          have hNnonzero : N ≠ 0 := by
            exact Rat.num_ne_zero.mpr (Units.ne_zero b')
          have hND_nonzero : N * D ≠ 0 :=
            mul_ne_zero hNnonzero (by exact_mod_cast (b':ℚ).den_ne_zero)
          have hclearden : ∀ q, [Fact (Nat.Prime q)] → atP c₀ b' q = atP c₀ ((N*D : ℤ):ℚ) q := by
            intro q hq
            have hbq : (b' : ℚ) = (N : ℚ) / (D : ℚ) := by
              rw [hN, hD]; exact (Rat.num_div_den _).symm
            unfold atP
            simp only [Int.cast_mul, Int.cast_natCast, Rat.cast_mul,
              Rat.cast_intCast, Rat.cast_natCast]
            calc
              hilbertSym ((c₀ : ℚ) : ℚ_[q]) ((b' : ℚ) : ℚ_[q]) =
              hilbertSym  ((c₀ : ℚ) : ℚ_[q]) (((N/D):ℚ) : ℚ_[q]) := by
                simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
                rw [hbq]
                simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
              _ = hilbertSym ((c₀ : ℚ) : ℚ_[q]) ((((N/D)*D^2):ℚ) : ℚ_[q]) := by
                have h := mul_square_eq (a := (↑↑c₀ : ℚ_[q])) (a' := 1) (b := (↑N/↑D : ℚ_[q]))
                  (b' := (D : ℚ_[q])) one_ne_zero (Nat.cast_ne_zero.mpr hDnonzero)
                simp only [one_pow, mul_one] at h
                simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_mul,
                  Rat.cast_pow]
                exact h.symm
              _ = hilbertSym ((c₀ : ℚ) : ℚ_[q]) ((N*D : ℚ) : ℚ_[q]) := by
                congr 1; push_cast; field_simp
          simp only [hclearden]
          have hsign : ((Int.sign (N * D) : ℤ) : ℚ)*(((N * D).natAbs : ℕ) : ℚ)
            = ((N*D : ℤ) : ℚ) := by
            rw [← Int.cast_natCast (R := ℚ), Int.natCast_natAbs]
            exact_mod_cast Int.sign_mul_natAbs (N * D)
          norm_cast; rw [← hsign]
          have hpeelsign: ∀ᶠ q : Nat.Primes in Filter.cofinite,
            atP c₀ ((Int.sign (N*D) : ℤ): ℚ) q = 1 := by
            rcases Int.sign_trichotomy (N*D) with htrich1 | htrich2 | htrich3
            · rw [htrich1]
              refine Filter.Eventually.of_forall (fun q => ?_)
              apply hilbertSym_one_right; aesop
            · exact absurd (Int.sign_eq_zero_iff_zero.mp htrich2) hND_nonzero
            · rw [htrich3]
              have hcast : ((-1 : ℤ) : ℚ) = ((-1 : ℚˣ) : ℚ) := by simp
              simp only [hcast]; exact hbase (-1) (Or.inl rfl)
          have nat_one_reduced: ∀ n : ℕ, n ≠ 0 →
            ∀ᶠ p : Nat.Primes in Filter.cofinite, atP c₀ (n : ℚ) p = 1 := by
            intro n hn
            induction n using UniqueFactorizationMonoid.induction_on_prime with
            | h₁ => exact absurd rfl hn
            | h₂ x hx =>
              obtain rfl : x = 1 := Nat.isUnit_iff.mp hx
              rw [Nat.cast_one]
              refine Filter.Eventually.of_forall (fun q => ?_)
              have hqprime : Fact (Nat.Prime (q : ℕ)) := ⟨q.2⟩
              exact hilbertSym_one_right (by exact_mod_cast Units.ne_zero c₀)
            | h₃ m p' hm1 hp' hm2 =>
              have hcombo := hm2 hm1
              have hBase : ∀ᶠ q : Nat.Primes in Filter.cofinite, atP c₀ (p' : ℚ) q = 1 :=
                hbase (Units.mk0 (p' : ℚ) (by exact_mod_cast hp'.ne_zero))
                      (Or.inr ⟨p', Nat.prime_iff.mpr hp', by simp⟩)
              rw [mul_comm p' m]; push_cast
              filter_upwards [Filter.eventually_and.mpr ⟨hcombo, hBase⟩] with q ⟨hq1, hq2⟩
              change atP c₀ ((m : ℚ) * (p' : ℚ)) q = 1; unfold atP
              have hcast : (((m : ℚ) * (p' : ℚ) : ℚ) : ℚ_[q]) = (m : ℚ_[q]) * (p' : ℚ_[q]) := by
                push_cast; ring
              rw [hcast]
              unfold atP at hq1 hq2
              rw [right_mul_eq_of_eq_one]
              · exact hq2
              · exact hq1
          have h_nat : ∀ᶠ p : Nat.Primes in Filter.cofinite,
            atP c₀ ((N*D).natAbs : ℚ) p = 1 :=
            nat_one_reduced (N*D).natAbs (Int.natAbs_ne_zero.mpr hND_nonzero)
          filter_upwards [hpeelsign, h_nat] with p hsignND hnatND
          have hpprime: Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
          have hpeelsign2 : (((N*D).sign * (N*D).natAbs : ℚ) : ℚ_[(p : ℕ)])
            = ((N*D).sign : ℚ_[(p : ℕ)]) * ((N*D).natAbs : ℚ_[(p : ℕ)]) := by
            push_cast; ring
          unfold atP
          rw [hpeelsign2, right_mul_eq_of_eq_one]
          · exact hnatND
          · exact hsignND
        have atP_comm : ∀ (x y : ℚ) (p : ℕ) [Fact (Nat.Prime p)], atP x y p = atP y x p := by
          intro x y p hp; unfold atP; exact comm
        have hbase_b : ∀ d : ℚˣ, (d = -1 ∨ ∃ q, Nat.Prime q ∧ (↑d : ℚ) = ↑q) →
            ∀ᶠ p : Nat.Primes in Filter.cofinite, atP ↑b ↑d ↑p = 1 := by
          intro d hd
          have hd_base : ∀ e : ℚˣ, (e = -1 ∨ ∃ q, Nat.Prime q ∧ (↑e : ℚ) = ↑q) →
              ∀ᶠ (p : Primes) in Filter.cofinite, atP ↑d ↑e ↑p = 1 := by
              intro e he
              exact hreduction d e hd he
          have h := one_reduced_general d hd_base b
          filter_upwards [h] with p hp
          rw [atP_comm]; exact hp
        have h := one_reduced_general b hbase_b a
        filter_upwards [h] with p hp
        rw [atP_comm]; exact hp
  · simp only [Filter.eventually_cofinite]
    rintro c d (hc | ⟨r, hr, hcr⟩) (hd | ⟨q, hq, hdq⟩)
    · rw [hc, hd]
      apply Set.Finite.subset (Set.finite_singleton ⟨2, Nat.prime_two⟩)
      intro ⟨p, hp⟩ hexception
      simp only [Set.mem_setOf_eq] at hexception
      simp only [Set.mem_singleton_iff]
      by_contra hnot
      have hp2 : p ≠ 2 := by aesop
      have hfact : Fact (Nat.Prime p) := ⟨hp⟩
      apply hexception (hilbertSym_special_eq_one hp2
        (special_ne_zero (Or.inl rfl)) (special_ne_zero (Or.inl rfl))
        (padicValRat_special_eq_zero (Or.inl rfl)) (padicValRat_special_eq_zero (Or.inl rfl)))
    · have hfactq : Fact (Nat.Prime q) := ⟨hq⟩
      rw [hc]
      refine Set.Finite.subset (Set.toFinite
        ({⟨2, Nat.prime_two⟩, ⟨q, hq⟩} : Set Nat.Primes)) ?_
      intro ⟨p, hp⟩ hexception
      simp only [Set.mem_setOf_eq] at hexception
      by_contra hnot
      have hpq : p ≠ q := fun h => hnot (by subst h; simp)
      have hp2 : p ≠ 2 := by aesop
      have hfact : Fact (Nat.Prime p) := ⟨hp⟩
      exact hexception (hilbertSym_special_eq_one hp2
        (special_ne_zero (Or.inl rfl)) (special_ne_zero (Or.inr ⟨q, hq, hdq⟩))
        (padicValRat_special_eq_zero (Or.inl rfl))
        (padicValRat_special_eq_zero (Or.inr ⟨q, hq, hdq, hpq⟩)))
    · have hfactr : Fact (Nat.Prime r) := ⟨hr⟩
      rw [hd]
      refine Set.Finite.subset (Set.toFinite
        ({⟨2, Nat.prime_two⟩, ⟨r, hr⟩} : Set Nat.Primes)) ?_
      intro ⟨p, hp⟩ hexception
      simp only [Set.mem_setOf_eq] at hexception
      by_contra hnot
      have hpr : p ≠ r := fun h => hnot (by subst h; simp)
      have hp2 : p ≠ 2 := by aesop
      have hfact : Fact (Nat.Prime p) := ⟨hp⟩
      exact hexception (hilbertSym_special_eq_one hp2
        (special_ne_zero (Or.inr ⟨r, hr, hcr⟩)) (special_ne_zero (Or.inl rfl))
        (padicValRat_special_eq_zero (Or.inr ⟨r, hr, hcr, hpr⟩))
        (padicValRat_special_eq_zero (Or.inl rfl)))
    · have hfactq : Fact (Nat.Prime q) := ⟨hq⟩
      have hfactr : Fact (Nat.Prime r) := ⟨hr⟩
      refine Set.Finite.subset (Set.toFinite
        ({⟨2, Nat.prime_two⟩, ⟨q, hq⟩, ⟨r, hr⟩} : Set Nat.Primes)) ?_
      intro ⟨p, hp⟩ hexception
      simp only [Set.mem_setOf_eq] at hexception
      by_contra hnot
      have hpq : p ≠ q := fun h => hnot (by subst h; grind)
      have hpr : p ≠ r := fun h => hnot (by subst h; grind)
      have hp2 : p ≠ 2 := by aesop
      have hfact : Fact (Nat.Prime p) := ⟨hp⟩
      exact hexception (hilbertSym_special_eq_one hp2
        (special_ne_zero (Or.inr ⟨r, hr, hcr⟩)) (special_ne_zero (Or.inr ⟨q, hq, hdq⟩))
        (padicValRat_special_eq_zero (Or.inr ⟨r, hr, hcr, hpr⟩))
        (padicValRat_special_eq_zero (Or.inr ⟨q, hq, hdq, hpq⟩)))

/-- Right-multiplicativity over ℚ_p, nonzero arguments. -/
lemma hilbertSym_padic_mul_right {p : ℕ} [hp: Fact (Nat.Prime p)]
    {a b b' : ℚ_[p]} (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hilbertSym a (b * b') = hilbertSym a b * hilbertSym a b' := by
  rcases eq_or_ne p 2 with h2 | hodd
  · subst h2
    sorry
  · have castkey: ((hilbertSym a (b * b') : ℤ) : ℚ)
         = ((hilbertSym a b * hilbertSym a b' : ℤ) : ℚ) := by
      push_cast
      rw [padic_odd_eq hodd ha (mul_ne_zero hb hb'),
          padic_odd_eq hodd ha hb, padic_odd_eq hodd ha hb']
      --   valuation_mul, unitPart_mul, legendreSym mult, pow_add, Int.negOnePow_add
      simp only [mul_ite, val_mkUnits, mul_zero, mul_one, Int.coe_negOnePow, Units.mk0_mul]
      sorry
    exact_mod_cast castkey

/-- Right-multiplicativity over ℝ, nonzero arguments. -/
lemma hilbertSym_real_mul_right {a b b' : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hilbertSym a (b * b') = hilbertSym a b * hilbertSym a b' := by
  -- for nonzero reals hilbertSym a b = -1 ↔ a < 0 ∧ b < 0, else 1;
  -- sign case-split on a, b, b'
  sorry

/-- Right-multiplicativity for atP over ℚ_p. -/
lemma atP_mul_right (a b b' : ℚˣ) {p : ℕ} [hp : Fact (Nat.Prime p)] :
    atP a (↑(b * b')) p = atP a b p * atP a b' p := by
  unfold atP
  push_cast
  exact hilbertSym_padic_mul_right
    (by exact_mod_cast a.ne_zero) (by exact_mod_cast b.ne_zero)
    (by exact_mod_cast b'.ne_zero)

/-- Right-multiplicativity for atP over ℝ. -/
lemma atInfty_mul_right (a b b' : ℚˣ) :
    atInfty a (↑(b * b')) = atInfty a b * atInfty a b' := by
  unfold atInfty
  push_cast
  exact hilbertSym_real_mul_right
    (by exact_mod_cast a.ne_zero) (by exact_mod_cast b.ne_zero)
    (by exact_mod_cast b'.ne_zero)

/-- The product of the Hilbert symbols at all places equals 1. -/
theorem prod_eq_one (a b : ℚˣ) :
    atInfty a b * ∏ᶠ (p : Nat.Primes), atP a b p = 1 := by
  suffices hreduction : ∀ c d : ℚˣ, (c = -1 ∨ (∃ r : ℕ, Nat.Prime r ∧ (c : ℚ) = r)) →
    (d = -1 ∨ (∃ q : ℕ, Nat.Prime q ∧ (d : ℚ) = q)) →
    (atInfty c d * ∏ᶠ (p : Nat.Primes), atP c d p = 1) by
    · sorry
  · rintro c d (hc | ⟨r, hr, hcr⟩) (hd | ⟨q, hq, hdq⟩)
    · rw [hc,hd]
      simp only [Units.val_neg, Units.val_one]
      unfold atInfty
      simp only [Rat.cast_neg, Rat.cast_one]
      unfold hilbertSym
      simp only [neg_eq_zero, one_ne_zero, or_self, ↓reduceIte, ne_eq, Prod.mk.injEq, not_and,
        neg_mul, one_mul, sub_neg_eq_add, Int.reduceNeg, ite_mul]
      sorry
    · have hfactq : Fact (Nat.Prime q) := ⟨hq⟩
      rw [hc]
      simp only [Units.val_neg, Units.val_one]
      unfold atInfty
      simp only [Rat.cast_neg, Rat.cast_one]
      sorry
    · -- this should just be from symmetry
      have hfactr : Fact (Nat.Prime r) := ⟨hr⟩
      rw [hd]
      simp only [Units.val_neg, Units.val_one]
      unfold atInfty
      simp only [Rat.cast_neg, Rat.cast_one]
      sorry
    · -- this is the only case that needs quadratic reciprocity
      have hfactq : Fact (Nat.Prime q) := ⟨hq⟩
      have hfactr : Fact (Nat.Prime r) := ⟨hr⟩
      unfold atInfty
      sorry

end hilbertSym
