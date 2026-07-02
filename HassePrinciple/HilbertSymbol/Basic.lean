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

variable {k : Type*} [Field k] {a b : k} (a' b' : k)

lemma eq_one_or_neg_one_of_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b = 1 ∨ hilbertSym a b = -1 := by
  simp only [hilbertSym, ha, hb, false_or, if_false]
  split_ifs <;> tauto

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
    exact right_mul_eq_of_eq_one b (right_neg_self_eq_one hzero)

/-- If a is different from 1, then the Hilbert symbol of a and (1-a)*b equals the Hilbert symbol of
a and b. -/
@[simp]
theorem right_minus_self_mul (ha : a ≠ 1) :
    hilbertSym a ((1 - a) * b) = hilbertSym a b := by
  by_cases hzero : a = 0 <;> aesop

end Field

/-
## Local properties: computation of the Hilbert symbol in the real and p-adic cases
-/

/-- If k = ℝ, and a and b are nonzero, then the Hilbert symbol equals 1 if and only if either a or
b is positive. -/
theorem real_eq {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b = if 0 < a ∨ 0 < b then 1 else -1 := by
  sorry

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

-- do we need the bilinear form property? (see Theorem 2 and Cor.)
/-
# Global properties of the Hilbert symbol
-/
open Nat

/-- The instance that provides the fact that the nth prime is prime. -/
scoped instance fact_prime (p : Nat.Primes) : Fact (Nat.Prime p) := fact_iff.mpr p.2

/-- For all but finitely many primes `p`, the Hilbert symbol of `a` and `b` at `p` is `1`. -/
theorem almost_all_one (a b : ℚˣ) :
    ∀ᶠ (p : Nat.Primes) in Filter.cofinite, hilbertSym (a : ℚ_[p]) b = 1 := by
  sorry

/-- The product of the Hilbert symbols at all places equals 1. -/
theorem prod_eq_one (a b : ℚˣ) :
    (∏ᶠ (p : Nat.Primes), hilbertSym (a : ℚ_[p]) b) * hilbertSym (a : ℝ) b = 1 := by
  sorry

end hilbertSym
