/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández, Chi-Yun Hsu
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import HassePrinciple.ForMathlib.Data.Nat.Factorization.Defs

/-! # `p`-adic valuation of the numerator and denominator of a rational number -/

@[expose] public section

namespace Rat

/-- The numerator or denominator of a rational number has zero `p`-adic valuation. -/
lemma num_or_den_zero_padicVal (a : ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    padicValInt p a.num = 0 ∨ padicValNat p a.den = 0 := by
  by_contra! h
  apply not_not.mpr a.reduced
  have h1 : p ∣ a.num.natAbs := not_not.mp (mt padicValNat.eq_zero_of_not_dvd h.1)
  have h2 : p ∣ a.den := not_not.mp (mt padicValNat.eq_zero_of_not_dvd h.2)
  exact (Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt Fact.out) h1 h2)

/-- The numerator and denominator of a rational number with even `p`-adic valuation
also have even `p`-adic valuation. -/
lemma num_den_even_padicVal_of_even_padicVal {a : ℚ} {p : ℕ} [Fact (Nat.Prime p)]
    (h : Even (padicValRat p a)) : Even (padicValInt p a.num) ∧ Even (padicValNat p a.den) := by
  rcases num_or_den_zero_padicVal a p with (h0 | h0) <;>
  simpa [h0, padicValRat_def] using h

/-- A nonnegative rational number with even `p`-adic valuation for all `p` is a square. -/
lemma isSquare_of_even_factorization {a : ℚ} (hR : 0 ≤ a)
    (hf : ∀ (p : ℕ) [Fact (Nat.Prime p)], Even (padicValRat p a)) : IsSquare a :=
  isSquare_iff.mpr
  ⟨Int.isSquare_of_nonneg_of_even_factorization (num_nonneg.mpr hR)
    (fun p _ ↦ by simpa [Nat.factorization_def _ Fact.out, padicValInt] using
    (num_den_even_padicVal_of_even_padicVal (hf p)).1),
  Nat.isSquare_of_even_factorization
    (fun p _ ↦ by simpa [Nat.factorization_def _ Fact.out] using
    (num_den_even_padicVal_of_even_padicVal (hf p)).2)⟩

end Rat
