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
  by_cases hzero : a = 0
  · aesop
  · have hone : hilbertSym a (1-a) = 1 := by
      apply right_one_minus_self_eq_one hzero
      exact ha
    apply right_mul_eq_of_eq_one
    exact hone

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

/-- For `a, b : ℚ`, and for a prime `p : ℕ`, `atP a b p` denotes the Hilbert symbol of `a` and `b`
computed in `ℚ_[p]`. -/
noncomputable abbrev atP (a b : ℚ) (p : ℕ) [hp : Fact (Nat.Prime p)] : ℤ :=
  hilbertSym (a : ℚ_[p]) (b : ℚ_[p])

/-- For `a, b : ℚ`, `atInfty a b` the Hilbert symbol of `a` and `b` computed in `ℝ`. -/
noncomputable abbrev atInfty (a b : ℚ) : ℤ := hilbertSym (a : ℝ) (b : ℝ)

/-- The instance that provides the fact that the nth prime is prime. -/
scoped instance fact_prime (p : Nat.Primes) : Fact (Nat.Prime p) := fact_iff.mpr p.2

/-- For all but finitely many primes `p`, the Hilbert symbol of `a` and `b` at `p` is `1`. -/
theorem almost_all_one (a b : ℚˣ) :
    ∀ᶠ (p : Nat.Primes) in Filter.cofinite, atP a b p = 1 := by
  suffices hyeah : ∀ c d : ℚˣ, (c = -1 ∨ (∃ r : ℕ, Nat.Prime r ∧ (c : ℚ) = r)) →
    (d = -1 ∨ (∃ q : ℕ, Nat.Prime q ∧ (d : ℚ) = q)) →
    (∀ᶠ (p : Nat.Primes) in Filter.cofinite, atP c d p = 1) by
    · have nat_one_reduced (c₀ : ℚˣ) (hc₀ : c₀ = -1 ∨ ∃ r, Nat.Prime r ∧ (c₀:ℚ) = r) :
      ∀ n : ℕ, n ≠ 0 → ∀ᶠ p : Nat.Primes in Filter.cofinite, atP c₀ (n:ℚ) p = 1 := by
        intro n hn
        induction n using UniqueFactorizationMonoid.induction_on_prime with
        | h₁ => exact absurd rfl hn
        | h₂ x hx =>
          obtain rfl : x = 1 := Nat.isUnit_iff.mp hx
          rw [Filter.eventually_cofinite]
          --apply real_eq
          sorry
        | h₃ m p hm1 hp hm2 =>
          apply hm2 at hm1
          sorry
      have one_reduced_general (c₀ : ℚˣ) (hc₀ : c₀ = -1 ∨ ∃ r, Nat.Prime r ∧ (c₀:ℚ) = r) (b : ℚˣ) :
        ∀ᶠ p : Nat.Primes in Filter.cofinite, atP c₀ b p = 1 := by
        have hden := nat_one_reduced c₀ hc₀ (b:ℚ).den
        have hnum := nat_one_reduced c₀ hc₀ (b:ℚ).num.natAbs
  -- fold in sign via hc₀'s -1 branch / hyeah applied to c₀, -1
  -- then b = (sign * natAbs num) * den⁻¹ as rationals; assemble
  -- reduce to case of integers first? can just multiply by sqre denom and it won't change
  -- this will avoid dealing with the denominators
        sorry
      sorry
  · simp only [Filter.eventually_cofinite]
    rintro c d (hc | ⟨r, hr, hcr⟩) (hd | ⟨q, hq, hdq⟩)
    · rw [hc,hd]
      unfold atP
      simp only [Units.val_neg, Units.val_one, Rat.cast_neg, Rat.cast_one]
      apply Set.Finite.subset (Set.finite_singleton ⟨2, by decide⟩)
      intro ⟨p, hp⟩ hexception
      simp only [Set.mem_setOf_eq] at hexception
      simp only [Set.mem_singleton_iff]
      by_contra hnot
      have hp2 : p ≠ 2 := by aesop
      have hfact : Fact (Nat.Prime p) := ⟨hp⟩
      have hx : ((-1 : ℚ) : ℚ_[p]) ≠ 0 := by simp only [Rat.cast_neg, Rat.cast_one, ne_eq,
        neg_eq_zero, one_ne_zero, not_false_eq_true]
      have hy : ((-1 : ℚ) : ℚ_[p]) ≠ 0 := by simp only [Rat.cast_neg, Rat.cast_one, ne_eq,
        neg_eq_zero, one_ne_zero, not_false_eq_true]
      apply hexception
      have padicoddeq := padic_odd_eq hp2 hx hy
      have hval : valuation ((-1 : ℚ) : ℚ_[p]) = 0 := by
        rw [Padic.valuation_ratCast]
        simp only [padicValRat.neg, padicValRat.one]
      have castkey : (hilbertSym ((-1 : ℚ) : ℚ_[p]) ((-1 : ℚ) : ℚ_[p]) : ℚ) = 1 := by
        rw [padicoddeq, hval]
        simp only [mul_zero, mul_ite, val_mkUnits, mul_one, ite_self, Int.negOnePow_zero,
          Units.val_one, Int.cast_one, Rat.cast_neg, Rat.cast_one, zpow_zero]
      exact_mod_cast castkey
    · have hfactq : Fact (Nat.Prime q) := ⟨hq⟩
      rw [hc]
      unfold atP
      simp only [Units.val_neg, Units.val_one, Rat.cast_neg, Rat.cast_one]
      refine Set.Finite.subset (Set.toFinite
        ({⟨2, Nat.prime_two⟩, ⟨q, hq⟩} : Set Nat.Primes)) ?_
      intro ⟨p,hp⟩ hexception
      simp only [Set.mem_setOf_eq] at hexception
      by_contra hnot
      have hpq : p ≠ q := by
          intro h
          apply hnot
          subst h
          simp
      apply hexception
      have hp2 : p ≠ 2 := by aesop
      have hfact : Fact (Nat.Prime p) := ⟨hp⟩
      have hx : ((-1 : ℚ) : ℚ_[p]) ≠ 0 := by simp only [Rat.cast_neg, Rat.cast_one, ne_eq,
        neg_eq_zero, one_ne_zero, not_false_eq_true]
      have hy : ((d : ℚ) : ℚ_[p]) ≠ 0 := by simp only [ne_eq, Rat.cast_eq_zero, Units.ne_zero,
        not_false_eq_true]
      have padicoddeq := padic_odd_eq hp2 hx hy
      have hval : valuation ((-1 : ℚ) : ℚ_[p]) = 0 := by
        rw [Padic.valuation_ratCast]
        simp only [padicValRat.neg, padicValRat.one]
      have castkey : (hilbertSym ((-1 : ℚ) : ℚ_[p]) ((d : ℚ) : ℚ_[p]) : ℚ) = 1 := by
        rw [padicoddeq, hval]
        simp only [valuation_ratCast, zero_mul, mul_ite, val_mkUnits, mul_zero, mul_one, ite_self,
          Int.negOnePow_zero, Units.val_one, Int.cast_one, Rat.cast_neg, Rat.cast_one, one_mul,
          zpow_zero]
        have zeroval: padicValRat p ↑d = 0 := by
            rw [hdq, ← padicValRat_of_nat]
            norm_cast
            exact padicValNat_primes hpq
        rw [zeroval, zpow_zero]
      exact_mod_cast castkey
    · -- this should just be from symmetry
      sorry
    · have hfactq : Fact (Nat.Prime q) := ⟨hq⟩
      have hfactr : Fact (Nat.Prime r) := ⟨hr⟩
      unfold atP
      refine Set.Finite.subset (Set.toFinite
        ({⟨2, Nat.prime_two⟩, ⟨q, hq⟩, ⟨r, hr⟩} : Set Nat.Primes)) ?_
      intro ⟨p,hp⟩ hexception
      simp only [Set.mem_setOf_eq] at hexception
      by_contra hnot
      have hpq : p ≠ q := by
        intro h
        apply hnot
        subst h
        grind
      have hpr : p ≠ r := by
        intro h
        apply hnot
        subst h
        grind
      apply hexception
      have hp2 : p ≠ 2 := by aesop
      have hfact : Fact (Nat.Prime p) := ⟨hp⟩
      have hx : ((c : ℚ) : ℚ_[p]) ≠ 0 := by simp only [ne_eq, Rat.cast_eq_zero,
        Units.ne_zero, not_false_eq_true]
      have hy : ((d : ℚ) : ℚ_[p]) ≠ 0 := by simp only [ne_eq, Rat.cast_eq_zero, Units.ne_zero,
          not_false_eq_true]
      have padicoddeq := padic_odd_eq hp2 hx hy
      have castkey : (hilbertSym ((c : ℚ) : ℚ_[p]) ((d : ℚ) : ℚ_[p]) : ℚ) = 1 := by
        rw [padicoddeq]
        simp only [valuation_ratCast, mul_ite, val_mkUnits, mul_zero, mul_one, Int.coe_negOnePow]
        have zerovala: padicValRat p ↑c = 0 := by
          rw [hcr, ← padicValRat_of_nat]
          norm_cast
          exact padicValNat_primes hpr
        have zerovalb: padicValRat p ↑d = 0 := by
          rw [hdq, ← padicValRat_of_nat]
          norm_cast
          exact padicValNat_primes hpq
        rw [zerovala, zerovalb]
        simp only [mul_zero, ite_self, Int.natAbs_zero, pow_zero, zpow_zero, mul_one]
      exact_mod_cast castkey

/-- The product of the Hilbert symbols at all places equals 1. -/
theorem prod_eq_one (a b : ℚˣ) :
    atInfty a b * ∏ᶠ (p : Nat.Primes), atP a b p = 1 := by
  suffices hyeah : ∀ c d : ℚˣ, (c = -1 ∨ (∃ r : ℕ, Nat.Prime r ∧ (c : ℚ) = r)) →
    (d = -1 ∨ (∃ q : ℕ, Nat.Prime q ∧ (d : ℚ) = q)) →
    (atInfty c d * ∏ᶠ (p : Nat.Primes), atP c d p = 1) by
    · sorry
  · rintro c d (hc | ⟨r, hr, hcr⟩) (hd | ⟨q, hq, hdq⟩)
    · rw [hc,hd]
      simp only [Units.val_neg, Units.val_one]
      sorry
    · sorry
    · -- this should just be from symmetry
      sorry
    · -- this is the only case that needs quadratic reciprocity
      sorry

end hilbertSym
