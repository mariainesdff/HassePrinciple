/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.Padics.Lemmas
public import HassePrinciple.Padics.Legendre
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.LSeries.PrimesInAP

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

variable {k : Type*} [Field k] {a b a' b' : k}

lemma eq_one_or_neg_one_of_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b = 1 ∨ hilbertSym a b = -1 := by
  simp only [hilbertSym, ha, hb, false_or, if_false]
  split_ifs <;> tauto

/-- If `a` and `b` are nonzero, then `hilbertSym a b` is nonzero. -/
lemma ne_zero_of_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : hilbertSym a b ≠ 0 := by
  simp [hilbertSym, ha, hb]
  split_ifs <;> simp

/-- If `a` and `b` are multiplied by a square, the Hilbert symbol is unchanged. -/
lemma mul_square_eq (ha' : a' ≠ 0) (hb' : b' ≠ 0) :
    hilbertSym (a * a' ^ 2) (b * b' ^ 2) = hilbertSym a b := by
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

/-- Special case of `mul_square_eq`. -/
@[simp]
lemma mul_left_square_eq (ha' : a' ≠ 0) :
    hilbertSym (a * a' ^ 2) b = hilbertSym a b := by
  nth_rw 1 [← mul_one b]
  rw [← one_pow 2, mul_square_eq ha' one_ne_zero]

/-- Special case of `mul_square_eq`. -/
@[simp]
lemma mul_right_square_eq (hb' : b' ≠ 0) :
    hilbertSym a (b * b' ^ 2) = hilbertSym a b := by
  nth_rw 1 [← mul_one a]
  rw [← one_pow 2, mul_square_eq one_ne_zero hb']

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

/-- The Hilbert symbol of a and b (both nonzero) equals 1 if and only if a is a norm from the
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
      contrapose heq
      contrapose hc
      use z / y
      grind
    calc QuadraticAlgebra.norm { re := z / x, im := y / x }
      _ = z / x * (z / x) - b * (y / x) * (y / x) := by simp [QuadraticAlgebra.norm]
      _ = (z ^ 2 - b * y ^ 2) / x ^ 2 := by ring
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

/-- If both a and b are nonzero, the Hilbert symbol of a and b must be either 1 or -1. -/
theorem eq_one_or_neg_one (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b = 1 ∨ hilbertSym a b = -1 := by
  rw [hilbertSym]
  split_ifs <;> aesop

/-- If both a and b are nonzero, the Hilbert symbol of a and b is -1 if and only if it is not 1. -/
theorem eq_neg_one_iff_not_one (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b = -1 ↔ ¬hilbertSym a b = 1 := by
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  have := eq_one_or_neg_one ha hb
  aesop

/-- If the Hilbert symbol of a and b equals 1, then the Hilbert symbol of a and b * b' equals the
Hilbert symbol of a and b'. -/
@[simp]
theorem right_mul_eq_of_eq_one (hab : hilbertSym a b = 1) :
    hilbertSym a (b * b') = hilbertSym a b' := by
  by_cases hb' : b' = 0
  · aesop
  · have ⟨hanzero, hbnzero⟩ : a ≠ 0 ∧ b ≠ 0 := by
      rw [hilbertSym] at hab
      aesop
    by_cases ha : IsSquare a
    · obtain ⟨sqrta, sqrtadef⟩ := ha
      simp [sqrtadef, ← pow_two, comm]
      aesop
    · have Hab : Fact (∀ r : k, r ^ 2 ≠ a + 0 * r) := by
        rw [fact_iff]
        intro r
        simp only [zero_mul, add_zero, ne_eq]
        contrapose ha
        use r
        grind
      rw [comm, eq_one_iff hbnzero hanzero ha] at hab
      obtain ⟨t, ht⟩ := hab
      rw [hilbertSym, hilbertSym]
      split_ifs <;> try grind
      · have ⟨tt', htt'⟩ : ∃ tt' : QuadraticAlgebra k a 0, b * b' = QuadraticAlgebra.norm tt' := by
          rw [← eq_one_iff, hilbertSym]
          split_ifs <;> try grind
          all_goals aesop
        have : ∃ t' : QuadraticAlgebra k a 0, b' = QuadraticAlgebra.norm t' := by
          use tt' * (1 / t)
          simp [map_mul, ← htt', ht]
          field_simp
          rw [← map_mul]
          grind
        rw [← eq_one_iff hb' hanzero ha, hilbertSym, if_neg (by aesop)] at this
        grind
      · have ⟨t', ht'⟩ : ∃ t' : QuadraticAlgebra k a 0, b' = QuadraticAlgebra.norm t' := by
          rw [← eq_one_iff, hilbertSym]
          split_ifs <;> try grind
          all_goals aesop
        have : ∃ tt' : QuadraticAlgebra k a 0, b * b' = QuadraticAlgebra.norm tt' := by
          use t * t'
          simp [map_mul, ht, ht']
        rw [← eq_one_iff (by aesop) hanzero ha, hilbertSym, if_neg (by aesop)] at this
        simp only [ite_eq_left_iff] at this
        grind

/-- The Hilbert symbol of a and -a*b, equals the Hilbert symbol of a and b. -/
@[simp]
theorem right_neg_mul : hilbertSym a (- (a * b)) = hilbertSym a b := by
  by_cases hzero : a = 0
  · simp [hzero, hilbertSym]
  · rw [← neg_mul]
    exact right_mul_eq_of_eq_one (right_neg_self_eq_one hzero)

@[simp]
theorem left_neg_mul : hilbertSym (- (a * b)) b = hilbertSym a b := by
  rw [comm, mul_comm a, right_neg_mul, comm]

/-- If a is different from 1, then the Hilbert symbol of a and (1-a)*b equals the Hilbert symbol of
a and b. -/
@[simp]
theorem right_minus_self_mul (ha : a ≠ 1) :
    hilbertSym a ((1 - a) * b) = hilbertSym a b := by
  by_cases hzero : a = 0 <;> aesop

/-- Hilbert symbol with 1 is 1. Needed for the n = 1 base case in Hilbert reciprocity -/
lemma one_right (ha : a ≠ 0) : hilbertSym a 1 = 1 := by
  rw [← one_pow 2, right_square_eq_one ha one_ne_zero]

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

section Real

variable {a b a' b' : ℝ}

/-- If k = ℝ, and a and b are nonzero, then the Hilbert symbol equals 1 if and only if either a or
b is positive. -/
theorem real_eq (ha : a ≠ 0) (hb : b ≠ 0) :
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

variable (hp2 : p ≠ 2) (ha : a ≠ 0) (hb : b ≠ 0)

/-- Main theorem for odd p, case v(a)=0, v(b)=0. -/
lemma padic_odd_case00 (ha0 : a.valuation = 0) (hb0 : b.valuation = 0) :
    (hilbertSym a b : ℚ) =
      Int.negOnePow (valuation (a : ℚ_[p]) * valuation (b : ℚ_[p]) * epsilon (p2 hp2)) *
      (legendreSym (unitPart (Units.mk0 a ha) : ℤ_[p])) ^ valuation (b : ℚ_[p]) *
      (legendreSym (unitPart (Units.mk0 b hb) : ℤ_[p])) ^ valuation (a : ℚ_[p])  := by
  sorry

/-- Main theorem for odd p, case v(a)=1, v(b)=0. -/
lemma padic_odd_case10 (ha1 : valuation (a : ℚ_[p]) = 1) (hb0 : valuation (b : ℚ_[p]) = 0) :
    (hilbertSym a b : ℚ) =
      Int.negOnePow (valuation (a : ℚ_[p]) * valuation (b : ℚ_[p]) * epsilon (p2 hp2)) *
      (legendreSym (unitPart (Units.mk0 a ha) : ℤ_[p])) ^ (valuation (b : ℚ_[p])) *
      (legendreSym (unitPart (Units.mk0 b hb) : ℤ_[p])) ^ valuation (a : ℚ_[p]) := by
  sorry

/-- Main theorem for odd p, case v(a)=1, v(b)=1. -/
lemma padic_odd_case11 (ha1 : valuation (a : ℚ_[p]) = 1) (hb1 : valuation (b : ℚ_[p]) = 1) :
    (hilbertSym a b : ℚ) =
    Int.negOnePow (valuation (a : ℚ_[p]) * valuation (b : ℚ_[p]) * epsilon (p2 hp2)) *
      (legendreSym (unitPart (Units.mk0 a ha) : ℤ_[p])) ^ (valuation (b : ℚ_[p])) *
      (legendreSym (unitPart (Units.mk0 b hb) : ℤ_[p])) ^ valuation (a : ℚ_[p]) := by
  sorry

/-- If p is an odd prime and a, b are nonzero in ℚ_[p], then the Hilbert symbol (a, b)ₚ equals
`(-1) ^ v(a) * v(b) * ε(p) ` times the product of the Legendre symbol of the unit part of a to v(b)
times the Legendre symbol of the unit part of b to v(a). -/
theorem padic_odd_eq :
    (hilbertSym a b : ℚ) =
      Int.negOnePow (valuation (a : ℚ_[p]) * valuation (b : ℚ_[p]) * epsilon (p2 hp2)) *
      (legendreSym (unitPart (Units.mk0 a ha) : ℤ_[p])) ^ (valuation (b : ℚ_[p])) *
      (legendreSym (unitPart (Units.mk0 b hb)  : ℤ_[p])) ^ valuation (a : ℚ_[p]):= by
  sorry

end odd

section two

variable {a b : (ℚ_[2])} (ha : a ≠ 0) (hb : b ≠ 0)

/-- Main theorem for p=2, case v(a)=0, v(b)=0. -/
lemma two_adic_case00 (ha0 : valuation (a : ℚ_[2]) = 0) (hb0 : valuation (b : ℚ_[2]) = 0) :
    hilbertSym a b = Int.negOnePow (epsilon (unitPart (Units.mk0 a ha)) *
      epsilon (unitPart (Units.mk0 b hb)) + valuation (a : ℚ_[2]) *
      omega (unitPart (Units.mk0 b hb)) + valuation (b : ℚ_[2]) *
      omega (unitPart (Units.mk0 a ha))) := by
  sorry

/-- Main theorem for p=2, case v(a)=1, v(b)=0. -/
lemma two_adic_case10 (ha1 : valuation (a : ℚ_[2]) = 1) (hb0 : valuation (b : ℚ_[2]) = 0) :
    hilbertSym a b = Int.negOnePow (epsilon (unitPart (Units.mk0 a ha)) *
      epsilon (unitPart (Units.mk0 b hb)) + valuation (a : ℚ_[2]) *
      omega (unitPart (Units.mk0 b hb)) + valuation (b : ℚ_[2]) *
      omega (unitPart (Units.mk0 a ha))) := by
  sorry

/-- Main theorem for p=2, case v(a)=1, v(b)=1. -/
lemma two_adic_case11 (ha1 : valuation (a : ℚ_[2]) = 1) (hb1 : valuation (b : ℚ_[2]) = 1) :
    hilbertSym a b = Int.negOnePow (epsilon (unitPart (Units.mk0 a ha)) *
      epsilon (unitPart (Units.mk0 b hb)) + valuation (a : ℚ_[2]) *
      omega (unitPart (Units.mk0 b hb)) + valuation (b : ℚ_[2]) *
      omega (unitPart (Units.mk0 a ha))) := by
  sorry

/-- If a, b are nonzero in ℚ_[2], then the Hilbert symbol (a, b)₂ equals
`(-1) ^ (ε(u_a)ε(u_b) + v(a)ω(u_b) + v(b)ω(u_a))`, where u_a, u_b are the unit parts of a, b
respectively. -/
theorem two_adic_eq :
    hilbertSym a b = Int.negOnePow (PadicInt.epsilon (unitPart (Units.mk0 a ha)) *
      epsilon (unitPart (Units.mk0 b hb)) + valuation (a : ℚ_[2]) *
      omega (unitPart (Units.mk0 b hb)) + valuation (b : ℚ_[2]) *
      omega (unitPart (Units.mk0 a ha))) := by
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

/-- The instance that provides the fact that the nth prime is prime. -/
scoped instance fact_prime (p : Nat.Primes) : Fact (Nat.Prime p) := fact_iff.mpr p.2

/-- valuation is `0' at `p' when `x' is `-1' or a prime `≠ p' -/
lemma Padic.valuation_eq_zero_of_neg_one_or_prime {p : ℕ} [Fact (Nat.Prime p)]
    {x : ℚ} (hx : x = -1 ∨ ∃ r : ℕ, Nat.Prime r ∧ x = r ∧ p ≠ r) :
    (x : ℚ_[p]).valuation = 0 := by
  rw [Padic.valuation_ratCast]
  rcases hx with rfl | ⟨r, hr, rfl, hpr⟩
  · simp
  · have : Fact (Nat.Prime r) := ⟨hr⟩
    simp [padicValNat_primes hpr]

abbrev IsNegOneOrPrime (a : ℚ) : Prop := a = -1 ∨ ∃ r : ℕ, r.Prime ∧ (a : ℚ) = r

/-- `x ≠ 0' in `ℚ_[p]' when `x' is `-1' or a prime -/
lemma IsNegOneOrPrime.valuation_ne_zero {p : ℕ} [Fact (Nat.Prime p)]
    {x : ℚ} (hx : IsNegOneOrPrime x) :
    (x : ℚ_[p]) ≠ 0 := by
  rcases hx with rfl | ⟨r, hr, rfl⟩
  · simp
  · simp [hr.ne_zero]

/-- the actual Hilbert symbol computation, once both valuations vanish. -/
lemma eq_one_of_valuation_zero {p : ℕ} [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    {a b : ℚ} (ha : (a : ℚ_[p]) ≠ 0) (hb : (b : ℚ_[p]) ≠ 0)
    (hva : (a : ℚ_[p]).valuation = 0) (hvb : (b : ℚ_[p]).valuation = 0) :
    hilbertSym (a : ℚ_[p]) b = 1 := by
  simp [← Rat.intCast_eq_one_iff, padic_odd_eq hp2 ha hb, hva, hvb]

/-- The Hilbert symbol of (numerator of a)*(denominator of a) and b is that of a and b. -/
theorem num_mul_den (K : Type*) [Field K] [CharZero K] (a b : ℚˣ) :
    hilbertSym (((a.1.num * a.1.den : ℤ) : ℚ) : K) b = hilbertSym (a : K) b := by
  set N := (a : ℚ).num with hN
  set D := (a : ℚ).den with hD
  calc
    _ = hilbertSym ((((N / D) * D ^ 2) : ℚ) : K) b := by
      congr 1; push_cast; field_simp
    _ = hilbertSym (((N / D) : ℚ) : K) b := by
      have h := mul_square_eq (b := (b : K)) (a' := D) (a := (↑N/↑D : K))
        (Nat.cast_ne_zero.mpr (a : ℚ).den_ne_zero) one_ne_zero
      simp only [one_pow, mul_one] at h
      simp [h]
    _ = hilbertSym (a : K) b := by rw [← Rat.num_div_den a]

open Int
open Filter

/-- Let a and b be rational units. Suppose given d either -1 or prime, the Hilbert symbol of a and d
 is 1 for all but finitely many primes. Then, for all but finitely many primes, the Hilbert symbol
 of a and (numerator of b)*(denominator of b) is 1. -/
theorem sign_mul_num_den {a : ℚˣ}
    (ha : ∀ (d : ℚˣ), (IsNegOneOrPrime d) →
      ∀ᶠ (p : Primes) in cofinite, hilbertSym (a : ℚ_[p]) d = 1) (b : ℚˣ) :
    ∀ᶠ (q : Primes) in cofinite,
      hilbertSym (a : ℚ_[q]) ((sign (b.1.num * b.1.den : ℤ) : ℤ) : ℚ) = 1 := by
  rcases sign_trichotomy (b.1.num * b.1.den) with h1 | h0 | hneg1
  · simp only [h1, Int.cast_one, Rat.cast_one]
    exact Eventually.of_forall (fun q ↦ one_right (by simp))
  · exact absurd (sign_eq_zero_iff_zero.mp h0) (by simp [(b : ℚ).den_ne_zero])
  · simpa [hneg1] using ha (-1) (Or.inl rfl)

/-- Let a be a rational unit and b ∈ ℕ be nonzero. Suppose given d either -1 or prime,
 the Hilbert symbol of a and d is 1 for all but finitely many primes. Then, for all but finitely
 many primes, the Hilbert symbol of a and b is 1. -/
theorem natCast {a : ℚˣ}
    (ha : ∀ (d : ℚˣ), (IsNegOneOrPrime d) → ∀ᶠ (p : Primes) in cofinite,
    hilbertSym (a : ℚ_[p]) d = 1) {b : ℕ} (hb : b ≠ 0) : ∀ᶠ (p : Primes) in cofinite,
    hilbertSym (a : ℚ_[p]) b = 1 := by
  induction b using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => tauto
  | h₂ x hx =>
    obtain rfl : x = 1 := Nat.isUnit_iff.mp hx
    refine Eventually.of_forall (fun q ↦ ?_)
    have : Fact (Nat.Prime (q : ℕ)) := ⟨q.2⟩
    exact one_right (by simp [a.ne_zero])
  | h₃ m p' hm1 hp' hm2 =>
    have hBase : ∀ᶠ q : Nat.Primes in cofinite,
        hilbertSym (a : ℚ_[q]) p' = 1 :=
      ha (Units.mk0 (p' : ℚ) (by exact_mod_cast hp'.ne_zero))
            (Or.inr ⟨p', Nat.prime_iff.mpr hp', by simp⟩)
    filter_upwards [eventually_and.mpr ⟨hm2 hm1, hBase⟩] with q ⟨hq1, hq2⟩
    simp [right_mul_eq_of_eq_one hq2, hq1]

namespace eventually_one

open Nat

/-- For all but finitely many primes, the Hilbert symbol of -1 and -1 is 1. -/
theorem of_neg_one_of_neg_one :
    ∀ᶠ (p : Primes) in cofinite, hilbertSym ((-1 : ℚ) : ℚ_[p]) ((-1 : ℚ)) = 1 := by
  apply (Set.finite_singleton ⟨2, prime_two⟩).subset
  intro ⟨p, hp⟩ hne
  by_contra hcon
  have hp2 : p ≠ 2 := by aesop
  have hfact : Fact (Nat.Prime p) := ⟨hp⟩
  exact hne (eq_one_of_valuation_zero hp2
    (IsNegOneOrPrime.valuation_ne_zero (Or.inl rfl))
    (IsNegOneOrPrime.valuation_ne_zero (Or.inl rfl))
    (Padic.valuation_eq_zero_of_neg_one_or_prime (Or.inl rfl))
    (Padic.valuation_eq_zero_of_neg_one_or_prime (Or.inl rfl)))

/-- Fix b a prime. For all but finitely many primes, the Hilbert symbol of -1 and b is 1. -/
theorem of_neg_one_of_prime (b : ℕ) [hb : Fact (Nat.Prime b)] :
    ∀ᶠ (p : Primes) in cofinite, hilbertSym ((-1 : ℚ) : ℚ_[p]) (b : ℚ) = 1 := by
  refine (Set.toFinite ({⟨2, prime_two⟩, ⟨b, hb.out⟩} : Set Primes)).subset ?_
  intro ⟨p, hp⟩ hne
  by_contra hcon
  have hpr : p ≠ b := fun h ↦ hcon (by subst h; simp)
  have hp2 : p ≠ 2 := by aesop
  have hfact : Fact (Nat.Prime p) := ⟨hp⟩
  exact hne (eq_one_of_valuation_zero hp2
    (IsNegOneOrPrime.valuation_ne_zero (Or.inl rfl))
    (IsNegOneOrPrime.valuation_ne_zero (Or.inr ⟨b, hb.out, rfl⟩))
    (Padic.valuation_eq_zero_of_neg_one_or_prime (Or.inl rfl))
    (Padic.valuation_eq_zero_of_neg_one_or_prime (Or.inr ⟨b, hb.out, rfl, hpr⟩)))

/-- Given primes a and b, for all but finitely many primes, the Hilbert symbol of a and b is 1. -/
theorem of_prime_of_prime (a b : ℕ) [ha : Fact (Nat.Prime a)]
    [hb : Fact (Nat.Prime b)] :
    ∀ᶠ (p : Primes) in cofinite, hilbertSym ((a : ℚ) : ℚ_[p]) (b : ℚ) = 1 := by
  refine (Set.toFinite ({⟨2, prime_two⟩, ⟨a, ha.out⟩, ⟨b, hb.out⟩} : Set Primes)).subset  ?_
  intro ⟨p, hp⟩ hne
  by_contra hcon
  have hpa : p ≠ a := fun h => hcon (by subst h; grind)
  have hpb : p ≠ b := fun h => hcon (by subst h; grind)
  have hp2 : p ≠ 2 := by aesop
  have hfact : Fact (Nat.Prime p) := ⟨hp⟩
  exact hne (eq_one_of_valuation_zero hp2
    (IsNegOneOrPrime.valuation_ne_zero (Or.inr ⟨a, ha.out, rfl⟩))
    (IsNegOneOrPrime.valuation_ne_zero (Or.inr ⟨b, hb.out, rfl⟩))
    (Padic.valuation_eq_zero_of_neg_one_or_prime (Or.inr ⟨a, ha.out, rfl, hpa⟩))
    (Padic.valuation_eq_zero_of_neg_one_or_prime (Or.inr ⟨b, hb.out, rfl, hpb⟩)))

/-- Suppose a and b are each either -1 or prime. Then for all but finitely many primes,
the Hilbert symbol of a and b is 1. -/
theorem of_IsNegOneOrPrime {a b : ℚˣ} (ha : IsNegOneOrPrime a)
(hb : IsNegOneOrPrime b) : ∀ᶠ (p : Primes) in cofinite,
hilbertSym (a : ℚ_[p]) b = 1 := by
  rcases ha with ha | ⟨r, hr, ha⟩ <;> rcases hb with hb | ⟨q, hq, hb⟩
  · simpa [ha, hb] using of_neg_one_of_neg_one
  · simpa [ha, hb] using of_neg_one_of_prime q (hb := ⟨hq⟩)
  · simpa [ha, hb, comm] using @of_neg_one_of_prime r ⟨hr⟩
  · simpa [ha, hb] using @of_prime_of_prime r q ⟨hr⟩ ⟨hq⟩

/-- Let a and b be rational units. Suppose given d either -1 or prime,
 the Hilbert symbol of a and d is 1 for all but finitely many primes. Then, for all but finitely
 many primes, the Hilbert symbol of b and a is 1. -/
theorem left {a : ℚˣ}
    (ha : ∀ (d : ℚˣ), (IsNegOneOrPrime d) →
      ∀ᶠ (p : Primes) in cofinite, hilbertSym (a : ℚ_[p]) d = 1) (b : ℚˣ) :
    ∀ᶠ (p : Primes) in cofinite, hilbertSym (b : ℚ_[p]) (a : ℚ_[p]) = 1 := by
  set N := (b : ℚ).num with hN
  set D := (b : ℚ).den with hD
  have hND_nonzero : N * D ≠ 0 := mul_ne_zero (Rat.num_ne_zero.mpr b.ne_zero)
    (ofNat_ne_zero.mpr (b : ℚ).den_ne_zero)
  simp only [← num_mul_den]
  have h_nat : ∀ᶠ p : Primes in cofinite,
      hilbertSym (a : ℚ_[p]) ((N * D).natAbs : ℚ) = 1 :=
    natCast ha (natAbs_ne_zero.mpr hND_nonzero)
  filter_upwards [sign_mul_num_den ha b, h_nat] with p hsignND hnatND
  have hpprime: Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
  have hsplitQ : ((N * D : ℤ) : ℚ) = ((sign (N*D) : ℤ) : ℚ) * ((N * D).natAbs : ℚ) := by
    rw [← cast_natCast (R := ℚ), ← Int.cast_mul, sign_mul_natAbs]
  rw [hsplitQ, Rat.cast_mul, comm, right_mul_eq_of_eq_one hsignND, hnatND]


/-- For all but finitely many primes `p`, the Hilbert symbol of `a` and `b` at `p` is `1`. -/
theorem almost_all_one (a b : ℚˣ) :
    ∀ᶠ (p : Primes) in cofinite, hilbertSym (a : ℚ_[p]) b = 1 := by
  suffices hreduction : ∀ c d : ℚˣ, (IsNegOneOrPrime c) → (IsNegOneOrPrime d) →
      (∀ᶠ (p : Primes) in cofinite, hilbertSym (c : ℚ_[p]) d = 1) by
    have one_reduced_general {c₀ : ℚˣ}
        (hc : ∀ d : ℚˣ, (IsNegOneOrPrime d) → ∀ᶠ p : Primes in cofinite,
        hilbertSym (↑c₀ : ℚ_[p]) ↑d = 1) (b' : ℚˣ) : ∀ᶠ p : Primes in cofinite,
        hilbertSym (b' : ℚ_[p]) c₀ = 1 := left hc b'
    have hbase_b (d : ℚˣ) (hd: IsNegOneOrPrime d) :
        ∀ᶠ p : Primes in cofinite, hilbertSym (↑b : ℚ_[p]) ↑d = 1 := by
      exact left (fun _ he ↦ hreduction _ _ hd he) b
    exact one_reduced_general hbase_b a
  · apply of_IsNegOneOrPrime

end eventually_one

/-- Right-multiplicativity over ℚ_p, nonzero arguments. -/
lemma hilbertSym_padic_mul_right {p : ℕ} [hp : Fact (Nat.Prime p)]
    {a b b' : ℚ_[p]} (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hilbertSym a (b * b') = hilbertSym a b * hilbertSym a b' := by
  sorry

/-- Right-multiplicativity over ℝ, nonzero arguments. -/
lemma hilbertSym_real_mul_right {a b b' : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hilbertSym a (b * b') = hilbertSym a b * hilbertSym a b' := by
  -- for nonzero reals hilbertSym a b = -1 ↔ a < 0 ∧ b < 0, else 1;
  -- sign case-split on a, b, b'
  sorry

/-- The product of the Hilbert symbols at all places equals 1. -/
theorem prod_eq_one (a b : ℚˣ) :
    (∏ᶠ (p : Primes), hilbertSym (a : ℚ_[p]) b) * hilbertSym (a : ℝ) b = 1 := by
  -- part 1 apply almost_all_one to confirm there is a finite set where symbol is -1
  -- feed almost_all_one into finprod_mul_distrib
  -- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Finprod.html#finprod_mul_distrib
  -- part 2: simplify to the four cases again
  -- part 3: Tackle each case
  -- part 3a: If a=b=-1, then the only times the symbol is -1 is at infinity and 2.
  -- Since this is even, the product is 1.
  -- part 3b: If a=-1, b=l odd prime, then symbol at 2 and l are both (-1)^e(l) and all others are 1
  -- here e(l) is the class modulo 2 of (u-1)/2 where u is viewed as a 2-adic unit
  -- case 3b': If a=-1, b=2 then the symbol is always 1 by two_adic_eq.
  -- part 3c: Symmetric argument to 3b for a=l prime, b=-1
  -- part 3d: need more cases! If one of them is 2, we have a different argument
  -- at 2: use two_adic_eq and at k: use padic_odd_eq
  -- part 3d': If a and b are different primes j and k both not 2, use QR argument.
  -- part 3d'': If a and b are the same prime, (j,j)=(-1,j) always (use right_neg_self_eq_one).
  -- Then we're in 3c.
   sorry

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.html
-- for 3b and 3c: theorem legendreSym.at_neg_one{p : ℕ} [Fact (Nat.Prime p)] (hp : p ≠ 2) :
-- legendreSym p (-1) = ZMod.χ₄ ↑p
-- for 3d: legendreSym.at_two{p : ℕ} [Fact (Nat.Prime p)] (hp : p ≠ 2) :
-- legendreSym p 2 = ZMod.χ₈ ↑p
-- for 3d' legendreSym.quadratic_reciprocity{p q : ℕ} [Fact (Nat.Prime p)] [Fact (Nat.Prime q)]
-- (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
-- legendreSym q ↑p * legendreSym p ↑q = (-1) ^ (p / 2 * (q / 2))

end hilbertSym
