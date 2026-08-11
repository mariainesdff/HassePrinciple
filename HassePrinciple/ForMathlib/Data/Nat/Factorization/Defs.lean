/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández, Chi-Yun Hsu
-/
module

public import Mathlib.Data.Nat.Factorization.Defs

/-! # Criterion for a natural number or integer being a square through even factorization -/

@[expose] public section

namespace Nat

/-- A natural number with even `p`-adic valuation for all `p` is a square. -/
lemma isSquare_of_even_factorization {n : ℕ}
    (h : ∀ (p : ℕ) [Fact (Prime p)], Even (n.factorization p)) : IsSquare n := by
  by_cases h0 : n = 0
  · simp [h0]
  refine ⟨n.factorization.prod fun a b ↦ a ^ (b / 2), ?_⟩
  rw [← pow_two, ← powMonoidHom_apply, map_finsuppProd]
  nth_rw 1 [← prod_factorization_pow_eq_self h0]
  refine Finsupp.prod_congr fun p hp ↦ ?_
  letI : Fact (Prime p) := ⟨prime_of_mem_primeFactors hp⟩
  rw [powMonoidHom_apply, ← pow_mul, div_two_mul_two_of_even (h p)]

end Nat

namespace Int

/-- A nonnegative integer with even `p`-adic valuation for all `p` is a square. -/
lemma isSquare_of_nonneg_of_even_factorization {n : ℤ} (h0 : 0 ≤ n)
    (h : ∀ (p : ℕ) [Fact (Nat.Prime p)], Even (n.natAbs.factorization p)) : IsSquare n := by
  obtain ⟨r, hr⟩ := Nat.isSquare_of_even_factorization h
  exact ⟨r, (by rw [← natAbs_of_nonneg h0, hr, Nat.cast_mul])⟩

end Int
