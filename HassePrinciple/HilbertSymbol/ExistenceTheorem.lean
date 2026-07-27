/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.HilbertSymbol.Basic
public import HassePrinciple.ForMathlib.Algebra.Ring.Int.Parity

/-!
# Existence theorem
-/
@[expose] public section

namespace hilbertSym

open Filter Finset Nat Units

section Integer

variable {I : Type*} {a : I → ℤ} (ha : ∀ i, a i ≠ 0) {ep : I → Primes → ℤ}
  (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
  {ereal : I → ℤ} (hereal : ∀ i : I, ereal i = 1 ∨ ereal i = -1)
  -- h1, h2, h3 are assumed in the hard direction of the existence theorem.
  (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
  (h2 : ∀ i : I, (∏ᶠ (p : Primes), ep i p) * ereal i = 1)
  (h3 : ((∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) ∧
    ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i)

include ha in
/-- The necessary conditions in the Existence Theorem are indeed necessary. -/
private lemma necessary_cond (x : ℚˣ)
    (h : ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) :
    (∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) ∧
    (∀ i : I, (∏ᶠ p : Primes, ep i p) * ereal i = 1) ∧
    (∀ p : Primes, ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p) ∧
    ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i :=
  ⟨fun i ↦ by
    simp only [← h i, eventually_cofinite]; exact almost_all_one x (mk0 (a i) (by simp [ha])),
    fun i ↦ by simp only [← h i]; exact prod_eq_one x (mk0 (a i) (by simp [ha])),
    fun p ↦ ⟨x, by simp [h]⟩, x, by simp [h]⟩

include hep in
/-- From ep i p = 1 or -1, we deduce that ep i p = -1 iff not ep i p = 1. -/
private lemma ep_eq_neg_one_iff_not_one {i : I} {p : Primes} :
    ep i p = -1 ↔ ¬ep i p = 1 :=
  ⟨fun h ↦ by simp [h], fun h ↦ (hep i p).resolve_left h⟩

include ha hep h1 h2 in
/-- Using the product formula for the Hilbert symbol and for ep i, if we show that
hilbertSym x (a i) = ep i p for all but one p, we are done. -/
lemma all_but_one_places_suffice (q : Primes) (x : ℚˣ)
    (h4 : ∀ i : I, (∀ p : Primes, p ≠ q → hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) :
    ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i := by
  let afun : I → ℚˣ := fun i ↦ mk0 (a i) (by simp [ha])
  refine fun i ↦ ⟨fun p ↦ ?_, by simp [h4]⟩
  --The nontrivial case is when p=q.
  by_cases hpq : p = q
  · have hprod' : ∏ᶠ (p' : Primes) (_ : p' ≠ q), hilbertSym (x : ℚ_[p']) (a i) =
        ∏ᶠ (p' : Primes) (_ : p' ≠  q), ep i p' := by
      congr! with p' h
      rw [(h4 i).1 p' h]
    have hprod : ∏ᶠ (p : Primes), hilbertSym (x : ℚ_[p]) (a i) = ∏ᶠ (p : Primes), ep i p := by
      rw [← mul_left_inj' (by grind : ereal i ≠ 0)]
      nth_rw 1 [← (h4 i).2, h2 i]
      exact prod_eq_one x (afun i)
    rw [← mul_finprod_cond_ne q (_),
      ← mul_finprod_cond_ne q (h1 i), hprod', mul_eq_mul_right_iff, ← hpq] at hprod
    · apply hprod.resolve_right
      rw [finprod_cond_ne _ _ (h1 i), ← ne_eq, prod_ne_zero_iff]
      grind
    · exact almost_all_one x (afun i)
  · exact (h4 i).1 p hpq

variable [Finite I]

variable (a) in
/-- Define S to be the (finite!) set of primes that divide either the numerator or the denominator
of some (a i). N.B. In Serre, S contains also ∞. -/
noncomputable def S : Finset Primes :=
  have : Fintype I := by exact Fintype.ofFinite I
  (univ.biUnion (fun i ↦ (a i).natAbs.primeFactors) ∪ {2}).preimage Subtype.val
    Subtype.val_injective.injOn

include hep h1 in
lemma Tfin : (⋃ i : I, {p : Primes | ep i p = -1}).Finite := by
  refine (Set.finite_iUnion fun i ↦ ?_)
  simp only [eventually_cofinite, ← ep_eq_neg_one_iff_not_one hep, Int.reduceNeg] at h1
  exact h1 i

/-- Define T to be the (finite!) set of primes such that at least one of the e_{i,v} is -1. -/
noncomputable def T : Finset Primes := (Tfin hep h1).toFinset

private lemma ep_eq_one_of_not_mem_T {p : Primes} (hpT : p ∉ T hep h1) (i : I) : ep i p = 1 := by
  simp only [T, Int.reduceNeg, ep_eq_neg_one_iff_not_one hep, Set.Finite.mem_toFinset,
    Set.mem_iUnion, Set.mem_setOf_eq, not_exists, Decidable.not_not] at hpT
  exact hpT i

private lemma ep_eq_one_iff_not_mem_T (p : Primes) : p ∉ T hep h1 ↔ ∀ i : I, ep i p = 1 :=
  ⟨fun h i ↦ ep_eq_one_of_not_mem_T hep h1 h i, fun h ↦ by simp [T]; grind⟩

variable (disjoint_ST : Disjoint (S a) (T hep h1))

include disjoint_ST in
private lemma ep_eq_one_of_mem_S_disjoint {p : Primes} (hpS : p ∈ S a) (i : I) : ep i p = 1 := by
  exact ep_eq_one_of_not_mem_T hep h1 (disjoint_left.mp disjoint_ST hpS) i

include ha in
private lemma is_unit_ai_of_p_notMem_S {p : Primes} (hpS : p ∉ S a) (i : I) :
    padicValInt p (a i) = 0 := by
  simp only [S, union_singleton, mem_preimage, mem_insert, mem_biUnion, mem_univ, mem_primeFactors,
    p.2, ne_eq, Int.natAbs_eq_zero, true_and, not_or, not_exists, not_and, Decidable.not_not, ha,
    imp_false, ← Int.natCast_dvd] at hpS
  simp [ha, hpS]

private noncomputable abbrev A : ℕ := ∏ t ∈ T hep h1, (t : ℕ)

private lemma A_ne_zero : A hep h1 ≠ 0 := by simp [prod_ne_zero_iff, A, NeZero.out]

private lemma A_pos : 0 < A hep h1 := by simp [A, pos_of_neZero]

variable (a) in
private noncomputable abbrev M := 4 * ∏ s ∈ S a, (s : ℕ)

private lemma M_ne_zero : M a ≠ 0 := mul_ne_zero (by omega) (by simp [prod_ne_zero_iff, NeZero.out])

include disjoint_ST in
/-- The definition of q when S and T are disjoint using Dirichlet. -/
private lemma q_existence :
    ∃ q : ℕ, Nat.Prime q ∧ q ≡ ∏ t ∈ T hep h1, (t : ℕ) [MOD 4 * ∏ s ∈ S a, (s : ℕ)] := by
  let A := hilbertSym.A hep h1
  let M := hilbertSym.M a
  have coprime_AM : A.Coprime M := by
    rw [coprime_prod_left_iff]
    refine fun t ht ↦ Coprime.mul_right ?_ ?_
    · have h2 : (⟨2, prime_two⟩ : Primes) = (2 : ℕ) := rfl
      rw [(by omega : 4 = 2 ^ 2), coprime_pow_right_iff (by omega), coprime_two_right]
      apply Prime.odd_of_ne_two t.2
      rw [← h2, ne_eq, Primes.coe_nat_inj, eq_comm]
      exact (disjoint_iff_ne.mp disjoint_ST) ⟨2,prime_two⟩ (by simp [hilbertSym.S]) t ht
    · rw [coprime_prod_right_iff]
      intro s hs
      simp [coprime_primes t.2 s.2, Primes.coe_nat_inj, (disjoint_ST.forall_ne_finset hs ht).symm]
  --We can apply Dirichlet's lemma.
  exact (infinite_setOf_prime_and_modEq M_ne_zero coprime_AM).nonempty

include disjoint_ST in
/-- Definition of q. -/
private noncomputable abbrev q : ℕ := (q_existence hep h1 disjoint_ST).choose

include disjoint_ST in
private lemma q_prime : Nat.Prime (q hep h1 disjoint_ST) :=
  (q_existence hep h1 disjoint_ST).choose_spec.1

include disjoint_ST in
private lemma q_cong :
    q hep h1 disjoint_ST ≡ ∏ t ∈ T hep h1, (t : ℕ) [MOD 4 * ∏ s ∈ S a, (s : ℕ)] :=
  (q_existence hep h1 disjoint_ST).choose_spec.2

include disjoint_ST in
private noncomputable def x := mk0 ((A hep h1) * (q hep h1 disjoint_ST) : ℚ) (by
  simp only [ne_eq, _root_.mul_eq_zero, cast_eq_zero, not_or]
  exact ⟨A_ne_zero hep h1, (q_prime hep h1 disjoint_ST).ne_zero⟩)

include disjoint_ST in
private lemma x_pos : 0 < (x hep h1 disjoint_ST).val := by
  simp only [x, val_mk0, ← cast_mul, cast_pos,
  mul_pos (A_pos hep h1) (q_prime hep h1 disjoint_ST).pos]

include disjoint_ST in
private lemma p_mem_S_not_dvd_x {p : Primes} (hpS : p ∈ S a) (hpq : p ≠ q hep h1 disjoint_ST) :
    ¬ (p : ℤ_[p]) ∣ (A hep h1) * (q hep h1 disjoint_ST) := by
  set A := hilbertSym.A hep h1
  set q := hilbertSym.q hep h1 disjoint_ST
  refine Prime.not_dvd_mul PadicInt.prime_p ?_ ?_
  · simp only [cast_prod, A, Prime.dvd_finsetProd_iff PadicInt.prime_p, not_exists, not_and]
    intro t ht
    rw [← PadicInt.norm_lt_one_iff_dvd, PadicInt.norm_natCast_lt_one_iff,
      Nat.prime_dvd_prime_iff_eq p.2 t.2, Primes.coe_nat_inj]
    exact (disjoint_iff_ne.mp disjoint_ST) p hpS t ht
  · rwa [← PadicInt.norm_lt_one_iff_dvd, PadicInt.norm_natCast_lt_one_iff,
      Nat.prime_dvd_prime_iff_eq p.2 (q_prime hep h1 disjoint_ST)]

include disjoint_ST in
private lemma isSquare_x {p : Primes} (hpS : p ∈ S a) (hpq : p ≠ q hep h1 disjoint_ST) :
    IsSquare ((A hep h1) * (q hep h1 disjoint_ST) : ℤ_[p]) := by
  set A := hilbertSym.A hep h1
  set q := hilbertSym.q hep h1 disjoint_ST
  have q_cong := hilbertSym.q_cong hep h1 disjoint_ST
  have not_dvd := p_mem_S_not_dvd_x hep h1 disjoint_ST hpS hpq
  by_cases hp2 : p = ⟨2, prime_two⟩
  · rw [hp2] at not_dvd ⊢
    apply PadicInt.isSquare_of_zmodPow not_dvd
    have : (q : ZMod 8) = A := by
      apply ModEq.of_dvd at q_cong
      · rwa [← ZMod.natCast_eq_natCast_iff] at q_cong
      · simp only [(by omega : 8 = 4 * 2)]
        rw [mul_dvd_mul_iff_left (by omega)]
        exact dvd_prod_of_mem Subtype.val (by simp [S, hilbertSym.S] : ⟨2, prime_two⟩ ∈ S a)
    simp [q, A, this]
  · apply PadicInt.isSquare_of_zmod (by rw [← Primes.coe_nat_inj] at hp2; exact hp2) not_dvd
    have : (q : ZMod p) = A := by
      apply ModEq.of_dvd at q_cong
      · rwa [← ZMod.natCast_eq_natCast_iff] at q_cong
      · exact Nat.dvd_mul_left_of_dvd (dvd_prod_of_mem Subtype.val hpS) 4
    simp [q, A, this]

include disjoint_ST in
private lemma isSquare_x_of_p_mem_S {p : Primes} (hpS : p ∈ S a)
    (hpq : p ≠ q hep h1 disjoint_ST) :  IsSquare (x hep h1 disjoint_ST : ℚ_[p]) := by
  have ⟨b, hb⟩ :=  (isSquare_iff_exists_mul_self _).mp (isSquare_x hep h1 disjoint_ST hpS hpq)
  use b
  simp only [x, cast_prod, mk0_mul, val_mul, val_mk0, Rat.cast_mul, Rat.cast_prod,
    Rat.cast_natCast, ← PadicInt.coe_mul, ← hb]
  simp [← PadicInt.algebraMap_apply]

include disjoint_ST in
private lemma padicValRat_x_eq_one_of_p_mem_T (p : Primes)
    (pneq : p ≠ q hep h1 disjoint_ST) (hpT : p ∈ T hep h1) :
      padicValRat p (x hep h1 disjoint_ST).val = 1 := by
  have q_prime := hilbertSym.q_prime hep h1 disjoint_ST
  have : Fact (Nat.Prime (q hep h1 disjoint_ST)) := ⟨q_prime⟩
  have hTp : T hep h1 = (T hep h1 \ {p}) ∪ {p} := by
    rw [union_singleton, insert_sdiff_self_of_mem hpT]
  simp only [x, cast_prod, mk0_mul, val_mul, val_mk0]
  rw [padicValRat.mul (by exact_mod_cast A_ne_zero hep h1) (by simp [q_prime.ne_zero]),
    padicValRat.of_nat]
  simp only [ne_eq, pneq, not_false_eq_true, padicValNat_primes, CharP.cast_eq_zero, add_zero]
  rw [← cast_prod, hTp, prod_union (by simp), prod_singleton, padicValRat.of_nat,
    padicValNat.mul ?_ (by simp [p.2.ne_zero]), padicValNat_self, cast_add, cast_one, add_eq_right]
  · rw [Int.natCast_eq_zero, padicValNat.eq_zero_iff]
    apply Or.inr (Or.inr ((prime_iff.mp p.2).not_dvd_finsetProd fun t ↦ ?_))
    simp [ne_comm, prime_dvd_prime_iff_eq p.2 t.2, Primes.coe_nat_inj]
  · have := A_ne_zero hep h1
    rw [hilbertSym.A, hTp, prod_union sdiff_disjoint, mul_ne_zero_iff] at this
    exact this.1

include disjoint_ST in
private lemma padicValRat_x_eq_zero_of_p_notMem_T {p : Primes} (pneq : p ≠ q hep h1 disjoint_ST)
      (hpT : p ∉ T hep h1) : padicValRat p (x hep h1 disjoint_ST).val = 0 := by
  have q_prime := hilbertSym.q_prime hep h1 disjoint_ST
  have : Fact (Nat.Prime (q hep h1 disjoint_ST)) := ⟨q_prime⟩
  simp only [x, cast_prod, mk0_mul, val_mul, val_mk0]
  rw [padicValRat.mul (by exact_mod_cast A_ne_zero hep h1) (by simp [q_prime.ne_zero])]
  simp only [← cast_prod, padicValRat.of_nat, ne_eq, pneq, not_false_eq_true, padicValNat_primes,
    CharP.cast_eq_zero, add_zero, Int.natCast_eq_zero, padicValNat.eq_zero_iff]
  apply Or.inr (Or.inr ((prime_iff.mp p.2).not_dvd_finsetProd ?_))
  intro t ht
  rw [prime_dvd_prime_iff_eq p.2 t.2, Primes.coe_nat_inj, ← ne_eq]
  aesop

include ha h2 h3 disjoint_ST in
/-- We first prove the Existence Theorem when S and T are disjoint. -/
private lemma existence_disjoint [Nonempty I] (infty_not_mem_T : ∀ i : I, ereal i = 1) :
    (∃ x : ℚˣ, ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) := by
  let q := hilbertSym.q hep h1 disjoint_ST
  have q_prime := hilbertSym.q_prime hep h1 disjoint_ST
  have : Fact (Nat.Prime q) := ⟨q_prime⟩
  let x := x hep h1 disjoint_ST
  use x
  --We apply lemma all_but_one_places_suffice to avoid dealing with q. Then we consider separately
  --the cases of p ∈ S, p ∈ T, p ∉ S ∪ T.
  apply all_but_one_places_suffice ha hep h1 h2 ⟨q, q_prime⟩ x
  refine fun i ↦ ⟨fun p pneq ↦ ?_,
    (by rw [real_eq (by simp) (by simp [ha]), infty_not_mem_T]; simp [x, x_pos hep h1 disjoint_ST])⟩
  have hpq : p.1 ≠ q := by simp only [ne_eq, ← Primes.coe_nat_inj] at pneq; exact pneq
  by_cases hpS : p ∈ S a
  · --case p ∈ S: LHR = 1 because x is a square, RHS = 1 because p ∉ T.
    have ⟨sqrt_x, hx⟩ := isSquare_x_of_p_mem_S hep h1 disjoint_ST hpS hpq
    simp only [x, hx, ← pow_two, comm, ep_eq_one_of_mem_S_disjoint hep h1 disjoint_ST hpS i]
    rw [right_square_eq_one (by simp [ha])
      (by rw [← pow_ne_zero_iff two_ne_zero, pow_two, ← hx]; simp)]
  · --case p ∉ S: (x, a_i)ₚ = (legendreSym p a_i) ^ val_p(x).
    have hp2 : p.1 ≠ 2 := by
      rw [ne_eq, Primes.coe_nat_inj p ⟨2, prime_two⟩]
      exact fun h2 ↦ by simp [h2, S, hilbertSym.S] at hpS
    rw [← Int.cast_inj (α := ℚ), padic_odd_eq hp2 (by simp only [ne_eq, Rat.cast_eq_zero,
      ne_zero, not_false_eq_true]) (by simp only [ne_eq, Int.cast_eq_zero, ha, not_false_eq_true])]
    by_cases hpT : p ∈ T hep h1
      --case p ∈ T: val_p(x) = 1.
    · have val_x : padicValRat p x.val = 1 :=
        padicValRat_x_eq_one_of_p_mem_T hep h1 disjoint_ST p hpq hpT
      --we extract xp from h3 and use it.
      obtain ⟨xp, hxp⟩ := h3.1 p
      have val_xp : Odd xp.valuation := by
        simp only [hilbertSym.T, Int.reduceNeg, Set.Finite.mem_toFinset, Set.mem_iUnion,
          Set.mem_setOf_eq, T] at hpT
        obtain ⟨j, hej⟩ := hpT
        specialize hxp j
        rw [← Int.cast_inj (α := ℚ), hej,
          padic_odd_eq hp2 (fun xp0 ↦ by simp [hilbertSym, xp0] at hxp) (by simp [ha])] at hxp
        simp only [Padic.valuation_intCast, is_unit_ai_of_p_notMem_S ha hpS, CharP.cast_eq_zero,
          mul_zero, mul_ite, PadicInt.val_mkUnits, mul_one, ite_self, Int.negOnePow_zero,
          val_one, Int.cast_one, zpow_zero, one_mul, Int.reduceNeg, Int.cast_neg,
          zpow_eq_neg_one_iff₀] at hxp
        exact hxp.2
      simp only [Padic.valuation_ratCast, val_x, Padic.valuation_intCast,
        is_unit_ai_of_p_notMem_S ha hpS, CharP.cast_eq_zero, mul_zero, mul_ite,
        PadicInt.val_mkUnits, mul_one, ite_self, Int.negOnePow_zero, val_one, Int.cast_one,
        zpow_zero, zpow_one, one_mul, ← hxp, Int.cast_inj]
      rw [← Int.cast_inj (α := ℚ), padic_odd_eq hp2 (fun xp0 ↦ by aesop) (by simp [ha])]
      simp only [Padic.valuation_intCast, is_unit_ai_of_p_notMem_S ha hpS, CharP.cast_eq_zero,
        mul_zero, mul_ite, PadicInt.val_mkUnits, mul_one, ite_self, Int.negOnePow_zero,
        val_one, Int.cast_one, zpow_zero, one_mul]
      rw [zpow_odd_one_or_neg_one_eq_self val_xp]
      simp only [Int.cast_inj, ← Int.cast_one (R := ℚ), ← Int.cast_neg]
      exact PadicInt.legendreSym.eq_one_or_neg_one (by simp)
    · --case p ∉ T: val_p(x) = 0, so LHR = 1 = RHS.
      have val_x : padicValRat p x.val = 0 :=
        padicValRat_x_eq_zero_of_p_notMem_T hep h1 disjoint_ST hpq hpT
      simp only [hilbertSym.T, Int.reduceNeg, ep_eq_neg_one_iff_not_one hep, Set.mem_iUnion,
        Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_exists, Decidable.not_not, T] at hpT
      simpa [val_x, is_unit_ai_of_p_notMem_S ha hpS,] using (Int.cast_inj.mpr (hpT i).symm)

include ha hep hereal in
/-- Given a finite set of rational numbers `{a_i}_{i ∈ I}` and numbers `e_{i,v} ∈ {± 1}`,
there exists a rational number `x` such that the Hilbert symbols `(x,a_i)_v` at each place `v`
is equal to `e_{i,v}` if and only if
1) for all `i`, almost all `e_{i,v}` are 1
2) for all `i`, the product of all `e_{i,v}` is 1
3) for each place `v`, there is some `x_v ∈ Q_v` with `(x_v,a_i)_v = e_{i,v}`. -/
theorem exists_rat_with_finite_prescribed_hilbertSym_of_int [Nonempty I] :
    (∃ x : ℚˣ, ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) ↔
      (∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) ∧
      (∀ i : I, (∏ᶠ (p : Primes), ep i p) * ereal i = 1) ∧
      ((∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) ∧
      ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i := by sorry

end Integer

theorem exists_rat_with_finite_prescribed_hilbertSym
    {I : Type*} [Finite I] [Nonempty I] (a : I → ℚˣ) {ep : I → Primes → ℤ} {ereal : I → ℤ}
    (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
    (hereal : ∀ i : I, ereal i = 1 ∨ ereal i = -1) :
    (∃ x : ℚˣ, ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧
      hilbertSym (x : ℝ) (a i) = ereal i) ↔
      (∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) ∧
      (∀ i : I, (∏ᶠ (p : Primes), ep i p) * ereal i = 1) ∧
      ((∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) ∧
      ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i := by
  have Ifin : Fintype I := Fintype.ofFinite I
  let d := ∏ i, (a i).1.den
  have hd : d ≠ 0 := by simp [d, Finset.prod_ne_zero_iff]
  have heq (i : I) : ((a i).1 * d ^ 2).den = 1 := by
    classical
    simp only [cast_prod, d]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton i _ (by simp)]
    simp only [mul_pow, pow_two ((a i).1.den : ℚ), ← mul_assoc, Rat.mul_den_eq_num]
    norm_cast
  simp_rw [Rat.den_eq_one_iff] at heq
  set b : I → ℤ := fun i ↦ ((a i).1 * d ^ 2).num with hb
  have hb0 (i : I) : ((a i).1 * d ^ 2).num ≠ 0 := by simp [hd]
  have hp (p : Primes) (i : I) (x : ℚ_[p]) : hilbertSym x (a i) = hilbertSym x (b i : ℚ) := by
    rw [hb, heq, Rat.cast_mul, Rat.cast_pow, hilbertSym.mul_right_square_eq (by simp [hd])]
  have hr (i : I) (x : ℝ) : hilbertSym x (a i) = hilbertSym x (b i : ℚ) := by
    rw [hb, heq, Rat.cast_mul, Rat.cast_pow, hilbertSym.mul_right_square_eq (by simp [hd])]
  simp_rw [hp, hr]
  exact exists_rat_with_finite_prescribed_hilbertSym_of_int hb0 hep hereal


theorem exists_rat_with_two_prescribed_hilbertSym (a b : ℚˣ) {ep ep' : Primes → ℤ} {er er' : ℤ}
    (hep : ∀ p : Primes, ep p = 1 ∨ ep p = -1) (hep' : ∀ p : Primes, ep' p = 1 ∨ ep' p = -1)
    (her : er  = 1 ∨ er = -1) (her' : er'  = 1 ∨ er' = -1) :
    (∃ x : ℚˣ, (∀ p : Primes, hilbertSym (x : ℚ_[p]) a = ep p ∧
      hilbertSym (x : ℚ_[p]) b = ep' p) ∧ hilbertSym (x : ℝ) a = er ∧ hilbertSym (x : ℝ) b = er') ↔
      ((∀ᶠ (p : Primes) in cofinite, ep p = 1) ∧
      (∀ᶠ (p : Primes) in cofinite, ep' p = 1)) ∧
     (((∏ᶠ (p : Primes), ep p) * er = 1) ∧ ((∏ᶠ (p : Primes), ep' p) * er' = 1)) ∧
      (∀ (p : Primes), ∃ xp : ℚ_[p], hilbertSym xp a = ep p ∧ hilbertSym xp b = ep' p) ∧
      ∃ xr : ℝ, hilbertSym xr a = er ∧ hilbertSym xr b = er':= by
  convert exists_rat_with_finite_prescribed_hilbertSym (I := Fin 2) (a := ![a, b])
    (ep := ![ep, ep']) (ereal := ![er, er']) (by simp [hep, hep']) (by simp [her, her']) <;>
  aesop

end hilbertSym
