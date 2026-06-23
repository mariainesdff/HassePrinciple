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
  · -- TODO: Update Blueprint. BEWARE: Compared to Serre and the blueprint, 2 and infinity are not dealt with here.
    have : Fintype I := Fintype.ofFinite I
    --define S to be the (fnite!) set of primes that divide either the numerator or the denominator
    --of some (a i). N.B. In Serre, S contains also 2 and ∞.
    let S := Finset.univ.biUnion (fun i ↦ (Int.natAbs (a i).val.num * (a i).val.den).primeFactors)
    --define T to be the (finite!) set of primes such that at least one of the e_{i,v} is -1.
    let T' := ⋃ i : I, {p : Nat.Primes | ep i p = -1}
    let f := fun (t' : T') ↦ (t' : ℕ)
    let T'' := Set.range f
    have : T''.Finite := by
      refine (Set.finite_range_iff ?_).mpr ?_
      · intro t1 t2 ht
        unfold f at ht
        ext
        exact_mod_cast ht
      · apply Set.finite_iUnion
        intro i
        specialize h1 i
        simp only [Filter.eventually_cofinite] at h1
        have (x : Nat.Primes) : ¬ep i x = 1 ↔ ep i x = -1 := by
          specialize hep1 i x
          lia
        simp_rw [this] at h1
        exact h1
    let T := Set.Finite.toFinset this


    let A := ∏ t : T, (t : ℕ)
    have A_ne_zero : A ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      aesop
    let M := 8 * ∏ s : S, (s : ℕ)
    have M_ne_zero : M ≠ 0 := by
      apply Nat.mul_ne_zero (by lia)
      rw [Finset.prod_ne_zero_iff]
      aesop


    by_cases disjoint_ST : Disjoint S T ∧ 2 ∉ T ∧ ∀ i : I, ereal i = 1
    · have coprime_AM : A.Coprime M := by
        rw [← Nat.disjoint_primeFactors A_ne_zero M_ne_zero]
        have Afac : A.primeFactors = T := by
          --rw [Nat.primeFactors_prod ?_]
          sorry




        have Mfac : M.primeFactors = S ∪ {2} := by sorry
        simp [Afac, Mfac, disjoint_ST, disjoint_comm]



        -- rw [Nat.coprime_prod_left_iff]
        -- intro t ht
        -- refine Nat.coprime_mul_iff_right.mpr ⟨?_,?_⟩
        -- · rw [(by omega: 8 = 2^3)]
        --   refine Nat.Prime.coprime_pow_of_not_dvd Nat.prime_two ?_


        --   sorry
        -- · sorry



      sorry
    · sorry
    #exit
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
