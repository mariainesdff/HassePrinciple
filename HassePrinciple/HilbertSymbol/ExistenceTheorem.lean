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
private lemma necessary_cond {I : Type*} [Finite I] (a : I → ℚˣ) (efin : I × Nat.Primes → ℤ)
    (einf : I → ℤ) (_ : ∀ i : I, ∀ p : Nat.Primes, efin (i, p) = 1 ∨ efin (i, p) = -1)
    (_ : ∀ i : I, einf i = 1 ∨ einf i = -1) (x : ℚˣ)
      (h : ∀ i : I, (∀ p : Nat.Primes, efin (i, p) = atP x (a i) p) ∧
        einf i = atInfty x (a i)) :
        (∀ i : I, (∀ᶠ (p : Nat.Primes) in Filter.cofinite, efin (i, p) = 1)) ∧
          (∀ i : I, (einf i * ∏ᶠ (p : Nat.Primes), efin (i, p) = 1)) ∧
          ((∀ (p : Nat.Primes), ∃ xp : ℚ_[p], ∀ i : I, efin (i, p) = hilbertSym xp (a i)) ∧
            ∃ xr : ℝ, ∀ i : I, einf i = hilbertSym xr (a i)) := by
  refine ⟨fun i ↦ (by simp_rw [Filter.eventually_cofinite, h i]; exact almost_all_one x (a i)),
    fun i ↦ (by simp_rw [h i]; exact prod_eq_one x (a i)),
    fun p ↦ (by use x; simp [h]), (by use x; simp [h])⟩




/-- Given a finite set of rational numbers `{a_i}_{i ∈ I}` and numbers `e_{i,v} ∈ {± 1}`,
there exists a rational number `x` such that the Hilbert symbols `(x,a_i)_v` at each place `v`
is equal to `e_{i,v}` if and only if
1) for all `i`, almost all `e_{i,v}` are 1
2) for all `i`, the product of all `e_{i,v}` is 1
3) for each place `v`, there is some `x_v ∈ Q_v` with `(x,a_i)_v = e_{i,v}`. -/
theorem exists_rat_with_prescribed_hilbert_symbols_at_finitely_many_places
    {I : Type*} [Finite I] (a : I → ℚˣ) (efin : I × Nat.Primes → ℤ) (einf : I → ℤ)
    (hefinpm1 : ∀ i : I, ∀ p : Nat.Primes, efin (i, p) = 1 ∨ efin (i, p) = -1)
    (heinfpm1 : ∀ i : I, einf i = 1 ∨ einf i = -1) :
      (∃ x : ℚˣ, ∀ i : I, (∀ p : Nat.Primes, efin (i, p) = atP x (a i) p) ∧
        einf i = atInfty x (a i)) ↔
        (∀ i : I, (∀ᶠ (p : Nat.Primes) in Filter.cofinite, efin (i, p) = 1)) ∧
          (∀ i : I, (einf i * ∏ᶠ (p : Nat.Primes), efin (i, p) = 1)) ∧
          ((∀ (p : Nat.Primes), ∃ xp : ℚ_[p], ∀ i : I, efin (i, p) = hilbertSym xp (a i)) ∧
            ∃ xr : ℝ, ∀ i : I, einf i = hilbertSym xr (a i)) := by
  refine ⟨fun ⟨x,h⟩ ↦ (by apply necessary_cond <;> assumption), fun ⟨h1,h2,h3⟩ ↦ ?_⟩
  · -- TODO: Update Blueprint. BEWARE: Compared to Serre and the blueprint, 2 and infinity are not dealt with here.
    have : Fintype I := Fintype.ofFinite I

    let S := Finset.univ.biUnion (fun i ↦ (Int.natAbs (a i).val.num * (a i).val.den).primeFactors)

    let T := ⋃ i : I, {p : Nat.Primes | efin (i, p) = -1}

--TODO Fix this
    have Tfin : T.Finite := by
      apply Set.finite_iUnion
      intro i
      specialize h1 i
      simp only [Filter.eventually_cofinite] at h1
      have (x : Nat.Primes) : ¬efin (i, x) = 1 ↔ efin (i, x) = -1 := by
        specialize hefinpm1 i x
        lia
      simp_rw [this] at h1
      exact h1
    have T' := Set.Finite.toFinset Tfin
    have T'' : Set ℕ := {(t : ℕ) | t : T'}
    have Tfin'' : T''.Finite := by sorry
    let T''' := Set.Finite.toFinset Tfin''



    let A := ∏ᶠ t : T', (t : ℕ)
    have A_ne_zero : A ≠ 0 := by sorry
    let m := 8 * ∏ᶠ s : S, (s : ℕ)
    have m_ne_zero : m ≠ 0 := by
      apply Nat.mul_ne_zero (by lia)
      apply finprod_ne_zero
      intro s
      sorry
    by_cases coprime_a_m : A.Coprime m ∧ ∀ i : I, einf i = 1
    · have ex_q : ∃ q, Nat.Prime q ∧ q ≡ A [MOD m] := by
        have := Set.Infinite.nonempty (Nat.infinite_setOf_prime_and_modEq m_ne_zero coprime_a_m.1)
        exact (Set.mem_image (fun x ↦ x % m) Irreducible (A % m)).mp this
      let q := Classical.choose ex_q
      have q_prime := (Classical.choose_spec ex_q).1
      have q_Dirichlet := (Classical.choose_spec ex_q).2
      have : IsUnit (A * q : ℚ) := by
        apply IsUnit.mul
        · simp [A_ne_zero]
        · have : q ≠ 0 := by
            apply Nat.Prime.ne_zero q_prime
          simp [this]
      let x := this.unit'
      use x
      intro i
      constructor
      · intro p
        by_cases hp_S : p.val ∣ Int.natAbs (a i).val.num * (a i).val.den
        · have eqAq : A * q ≡ A ^ 2 [MOD m] := by
            rw [pow_two]
            apply Nat.ModEq.mul (rfl) q_Dirichlet
          have sq_mod_8 : A * q ≡ A ^ 2 [MOD 8] := by
            exact Nat.ModEq.of_mul_right (∏ᶠ (s : ↥S), ↑s) eqAq
          have := Polynomial.squares_in_Z2 (A * q) A
          have sq_mod_p : A * q ≡ A ^ 2 [MOD p] := by
            have := Nat.ModEq.of_mul_left 8 eqAq
            sorry
          sorry
        · sorry
      · sorry
    · sorry
end hilbertSym
