/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.HilbertSymbol.Basic
public import HassePrinciple.NumberTheory.ApproximationTheorem
public import HassePrinciple.Padics.Lemmas

/-!
# Existence theorem
-/
@[expose] public section


namespace hilbertSym

/-- The necessary conditions in the Existence Theorem are necessary -/
private lemma necessary_cond
    {I : Type*} [Finite I] (a : I → ℚˣ) {ep : I → Nat.Primes → ℤ} {ereal : I → ℤ}
    (_ : ∀ i : I, ∀ p : Nat.Primes, ep i p = 1 ∨ ep i p = -1)
    (_ : ∀ i : I, ereal i = 1 ∨ ereal i = -1) (x : ℚˣ)
    (h : ∀ i : I, (∀ p : Nat.Primes, atP x (a i) p = ep i p) ∧ atInfty x (a i) = ereal i) :
      (∀ i : I, ∀ᶠ (p : Nat.Primes) in Filter.cofinite, ep i p = 1) ∧
      (∀ i : I, (∏ᶠ (p : Nat.Primes), ep i p) * ereal i = 1) ∧
      ((∀ (p : Nat.Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) ∧
      ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i := by
  refine ⟨fun i ↦ (by simp_rw [Filter.eventually_cofinite, ← h i]; exact almost_all_one x (a i)),
    fun i ↦ (by simp_rw [← h i]; rw [mul_comm]; exact prod_eq_one x (a i)),
    fun p ↦ (by use x; simp [h]), (by use x; simp [h])⟩



/-- Given a finite set of rational numbers `{a_i}_{i ∈ I}` and numbers `e_{i,v} ∈ {± 1}`,
there exists a rational number `x` such that the Hilbert symbols `(x,a_i)_v` at each place `v`
is equal to `e_{i,v}` if and only if
1) for all `i`, almost all `e_{i,v}` are 1
2) for all `i`, the product of all `e_{i,v}` is 1
3) for each place `v`, there is some `x_v ∈ Q_v` with `(x,a_i)_v = e_{i,v}`. -/
theorem exists_rat_with_finite_prescribed_hilbertSym
    {I : Type*} [Finite I] (a : I → ℚˣ) {ep : I → Nat.Primes → ℤ} {ereal : I → ℤ}
    (hep1 : ∀ i : I, ∀ p : Nat.Primes, ep i p = 1 ∨ ep i p = -1)
    (hereal : ∀ i : I, ereal i = 1 ∨ ereal i = -1) :
    (∃ x : ℚˣ, ∀ i : I, (∀ p : Nat.Primes, atP x (a i) p = ep i p) ∧ atInfty x (a i) = ereal i) ↔
      (∀ i : I, ∀ᶠ (p : Nat.Primes) in Filter.cofinite, ep i p = 1) ∧
      (∀ i : I, (∏ᶠ (p : Nat.Primes), ep i p) * ereal i = 1) ∧
      ((∀ (p : Nat.Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) ∧
      ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i := by
  refine ⟨fun ⟨x,h⟩ ↦ (by apply necessary_cond <;> assumption), fun ⟨h1,h2,h3⟩ ↦ ?_⟩
  · sorry


theorem exists_rat_with_prescribed_hilbertSym (a : ℚˣ) {ep : Nat.Primes → ℤ} {ereal : ℤ}
    (hep : ∀ p : Nat.Primes, ep p = 1 ∨ ep p = -1) (hereal : ereal  = 1 ∨ ereal = -1) :
    (∃ x : ℚˣ, (∀ p : Nat.Primes, atP x a p = ep p) ∧ atInfty x a = ereal) ↔
      (∀ᶠ (p : Nat.Primes) in Filter.cofinite, ep p = 1) ∧
      ((∏ᶠ (p : Nat.Primes), ep p) * ereal = 1) ∧
      (∀ (p : Nat.Primes), ∃ xp : ℚ_[p], hilbertSym xp a = ep p) ∧
      ∃ xr : ℝ, hilbertSym xr a = ereal := by
  convert exists_rat_with_finite_prescribed_hilbertSym (I := Unit) (a := fun _ ↦ a)
    (ep := fun _ ↦ ep) (ereal := fun _ ↦ ereal) (by simp [hep]) (by simp [hereal]) <;> simp




end hilbertSym
