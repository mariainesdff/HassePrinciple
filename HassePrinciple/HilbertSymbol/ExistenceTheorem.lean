/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.ForMathlib.Algebra.Ring.Int.Parity
public import HassePrinciple.HilbertSymbol.Basic
public import HassePrinciple.NumberTheory.ApproximationTheorem
public import HassePrinciple.Padics.Squares
public import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Existence theorem
-/
@[expose] public section

namespace hilbertSym

open Filter Finset Nat Units Function hilbertSym.HasBilinHilbertSym

section Integer

variable {I : Type*} {a : I → ℤ} (ha : ∀ i, a i ≠ 0) {ereal : I → ℤ}
  (hereal : ∀ i : I, ereal i = 1 ∨ ereal i = -1) {ep : I → Primes → ℤ}
  (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
  -- halmost_all_one, hprod_eq_one, hexists_in_completion are assumed in the hard direction
  -- of the existence theorem.
  (halmost_all_one : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
  (hprod_eq_one : ∀ i : I, ereal i * (∏ᶠ (p : Primes), ep i p) = 1)
  (hexists_in_completion : (∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i) ∧
    (∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p))

include ha in
/-- The necessary conditions in the Existence Theorem are indeed necessary. -/
private lemma necessary_cond (x : ℚˣ)
    (h : ∀ i : I, hilbertSym (x : ℝ) (a i) = ereal i ∧
      (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p)) :
    (∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) ∧
    (∀ i : I, ereal i * (∏ᶠ p : Primes, ep i p) = 1) ∧
    (∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i) ∧
    (∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p) :=
  ⟨fun i ↦ by
    simp only [← h i, eventually_cofinite]
    exact almost_all_one x (mk0 (a i) (by simp [ha])),
    fun i ↦ by simp only [← h i]; exact prod_eq_one x (mk0 (a i) (by simp [ha])),
    ⟨x, fun i ↦ by simp only [← h i]⟩, fun p ↦ ⟨x, by simp [h]⟩⟩

include hep in
/-- From ep i p = 1 or -1, we deduce that ep i p = -1 iff not ep i p = 1. -/
private lemma ep_eq_neg_one_iff_not_one {i : I} {p : Primes} :
    ep i p = -1 ↔ ¬ep i p = 1 :=
  ⟨fun h ↦ by simp [h], fun h ↦ (hep i p).resolve_left h⟩

include ha hep halmost_all_one hprod_eq_one in
/-- Using the product formula for the Hilbert symbol and for ep i, if we show that
hilbertSym x (a i) = ep i p for all but one p, we are done. -/
lemma all_but_one_places_suffice (q : Primes) (x : ℚˣ)
    (hall_but_q : ∀ i : I, hilbertSym (x : ℝ) (a i) = ereal i ∧
      (∀ p : Primes, p ≠ q → hilbertSym (x : ℚ_[p]) (a i) = ep i p)) :
    ∀ i : I, hilbertSym (x : ℝ) (a i) = ereal i ∧
      (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) := by
  let afun : I → ℚˣ := fun i ↦ mk0 (a i) (by simp [ha])
  refine fun i ↦ ⟨by simp [hall_but_q], fun p ↦ ?_⟩
  --The nontrivial case is when p=q.
  by_cases hpq : p = q
  · have hprod' : ∏ᶠ (p' : Primes) (_ : p' ≠ q), hilbertSym (x : ℚ_[p']) (a i) =
        ∏ᶠ (p' : Primes) (_ : p' ≠  q), ep i p' := by
      congr! with p' h
      rw [(hall_but_q i).2 p' h]
    have hprod : ∏ᶠ (p : Primes), hilbertSym (x : ℚ_[p]) (a i) = ∏ᶠ (p : Primes), ep i p := by
      rw [← mul_right_inj' (by grind : ereal i ≠ 0)]
      nth_rw 1 [← (hall_but_q i).1, hprod_eq_one i]
      exact prod_eq_one x (afun i)
    rw [← mul_finprod_cond_ne q (_),
      ← mul_finprod_cond_ne q (halmost_all_one i), hprod', mul_eq_mul_right_iff, ← hpq] at hprod
    · apply hprod.resolve_right
      rw [finprod_cond_ne _ _ (halmost_all_one i), ← ne_eq, prod_ne_zero_iff]
      grind
    · exact almost_all_one x (afun i)
  · exact (hall_but_q i).2 p hpq

section Finite

variable [Finite I]

variable (a) in
/-- Define S to be the (finite!) set of primes that divide either the numerator or the denominator
of some (a i). N.B. In Serre, S contains also ∞. -/
noncomputable def S : Finset Primes :=
  have : Fintype I := by exact Fintype.ofFinite I
  (univ.biUnion (fun i ↦ (a i).natAbs.primeFactors) ∪ {2}).preimage Subtype.val
    Subtype.val_injective.injOn

variable (a) in
private lemma two_in_S : ⟨2, prime_two⟩ ∈ S a := by
  simp only [S]
  exact mem_preimage.mpr (by simp)

include hep halmost_all_one in
lemma Tfin : (⋃ i : I, {p : Primes | ep i p = -1}).Finite := by
  refine (Set.finite_iUnion fun i ↦ ?_)
  simp only [eventually_cofinite, ← ep_eq_neg_one_iff_not_one hep, Int.reduceNeg] at halmost_all_one
  exact halmost_all_one i

/-- Define T to be the (finite!) set of primes such that at least one of the e_{i,v} is -1. -/
noncomputable def T : Finset Primes := (Tfin hep halmost_all_one).toFinset

private lemma ep_eq_one_of_not_mem_T {p : Primes} (hpT : p ∉ T hep halmost_all_one) (i : I) :
    ep i p = 1 := by
  simp only [T, Int.reduceNeg, ep_eq_neg_one_iff_not_one hep, Set.Finite.mem_toFinset,
    Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, Decidable.not_not] at hpT
  exact hpT i

private lemma ep_eq_one_iff_not_mem_T (p : Primes) :
    p ∉ T hep halmost_all_one ↔ ∀ i : I, ep i p = 1 :=
  ⟨fun h i ↦ ep_eq_one_of_not_mem_T hep halmost_all_one h i, fun h ↦ by simp [T]; grind⟩

variable (disjoint_ST : Disjoint (S a) (T hep halmost_all_one))

include disjoint_ST in
private lemma ep_eq_one_of_mem_S_disjoint {p : Primes} (hpS : p ∈ S a) (i : I) : ep i p = 1 := by
  exact ep_eq_one_of_not_mem_T hep halmost_all_one (disjoint_left.mp disjoint_ST hpS) i

include ha in
private lemma is_unit_ai_of_p_notMem_S {p : Primes} (hpS : p ∉ S a) (i : I) :
    padicValInt p (a i) = 0 := by
  have : Fintype I := Fintype.ofFinite I
  have : p.1 ∉ univ.biUnion fun i ↦ (a i).natAbs.primeFactors := by
    revert hpS
    contrapose!
    simp only [S]
    exact fun h ↦ mem_preimage.mpr (mem_union.mpr (by grind))
  simp only [mem_biUnion, mem_univ, mem_primeFactors, p.2, ← Int.natCast_dvd, ne_eq,
    Int.natAbs_eq_zero, ha, not_false_eq_true, and_true, true_and, not_exists] at this
  simp [ha, this]

private noncomputable abbrev A : ℕ := ∏ t ∈ T hep halmost_all_one, (t : ℕ)

private lemma A_ne_zero : A hep halmost_all_one ≠ 0 := by simp [prod_ne_zero_iff, A, NeZero.out]

private lemma A_pos : 0 < A hep halmost_all_one := by simp [A, pos_of_neZero]

variable (a) in
private noncomputable abbrev M := 4 * ∏ s ∈ S a, (s : ℕ)

private lemma M_ne_zero : M a ≠ 0 := mul_ne_zero (by omega) (by simp [prod_ne_zero_iff, NeZero.out])

include disjoint_ST in
/-- The definition of q when S and T are disjoint using Dirichlet. -/
private lemma q_existence : ∃ q : ℕ,
    Nat.Prime q ∧ q ≡ ∏ t ∈ T hep halmost_all_one, (t : ℕ) [MOD 4 * ∏ s ∈ S a, (s : ℕ)] := by
  let A := hilbertSym.A hep halmost_all_one
  let M := hilbertSym.M a
  have coprime_AM : A.Coprime M := by
    rw [coprime_prod_left_iff]
    refine fun t ht ↦ Coprime.mul_right ?_ ?_
    · rw [disjoint_iff_ne] at disjoint_ST
      specialize disjoint_ST ⟨2, prime_two⟩ (two_in_S a) t ht
      rw [(by omega : 4 = 2 ^ 2), coprime_pow_right_iff (by omega), coprime_two_right]
      apply Prime.odd_of_ne_two t.2
      rw [(by rfl : (2 : ℕ) = (⟨2, prime_two⟩ : Primes))]
      simp [Primes.coe_nat_inj t ⟨2, prime_two⟩]
      grind
    · rw [coprime_prod_right_iff]
      intro s hs
      simp [coprime_primes t.2 s.2, Primes.coe_nat_inj, (disjoint_ST.forall_ne_finset hs ht).symm]
  --We can apply Dirichlet's lemma.
  exact (Nat.infinite_setOfPred_prime_and_modEq (a := A) (hilbertSym.M_ne_zero) coprime_AM).nonempty

include disjoint_ST in
/-- Definition of q. -/
private noncomputable abbrev q : ℕ := (q_existence hep halmost_all_one disjoint_ST).choose

include disjoint_ST in
private lemma q_prime : Nat.Prime (q hep halmost_all_one disjoint_ST) :=
  (q_existence hep halmost_all_one disjoint_ST).choose_spec.1

include disjoint_ST in
private lemma q_cong :
    q hep halmost_all_one disjoint_ST ≡
      ∏ t ∈ T hep halmost_all_one, (t : ℕ) [MOD 4 * ∏ s ∈ S a, (s : ℕ)] :=
  (q_existence hep halmost_all_one disjoint_ST).choose_spec.2

include disjoint_ST in
private noncomputable def x :=
    mk0 ((A hep halmost_all_one) * (q hep halmost_all_one disjoint_ST) : ℚ) (by
  simp only [ne_eq, _root_.mul_eq_zero, cast_eq_zero, not_or]
  exact ⟨A_ne_zero hep halmost_all_one, (q_prime hep halmost_all_one disjoint_ST).ne_zero⟩)

include disjoint_ST in
private lemma x_pos : 0 < (x hep halmost_all_one disjoint_ST).val := by
  simp only [x, val_mk0, ← cast_mul, cast_pos,
  mul_pos (A_pos hep halmost_all_one) (q_prime hep halmost_all_one disjoint_ST).pos]

include disjoint_ST in
private lemma p_mem_S_not_dvd_x
    {p : Primes} (hpS : p ∈ S a) (hpq : p ≠ q hep halmost_all_one disjoint_ST) :
    ¬ (p : ℤ_[p]) ∣ (A hep halmost_all_one) * (q hep halmost_all_one disjoint_ST) := by
  set A := hilbertSym.A hep halmost_all_one
  set q := hilbertSym.q hep halmost_all_one disjoint_ST
  refine Prime.not_dvd_mul PadicInt.prime_p ?_ ?_
  · simp only [cast_prod, A, Prime.dvd_finsetProd_iff PadicInt.prime_p, not_exists, not_and]
    intro t ht
    rw [← PadicInt.norm_lt_one_iff_dvd, PadicInt.norm_natCast_lt_one_iff,
      Nat.prime_dvd_prime_iff_eq p.2 t.2, Primes.coe_nat_inj]
    exact (disjoint_iff_ne.mp disjoint_ST) p hpS t ht
  · rwa [← PadicInt.norm_lt_one_iff_dvd, PadicInt.norm_natCast_lt_one_iff,
      Nat.prime_dvd_prime_iff_eq p.2 (q_prime hep halmost_all_one disjoint_ST)]

include disjoint_ST in
private lemma isSquare_x
    {p : Primes} (hpS : p ∈ S a) (hpq : p ≠ q hep halmost_all_one disjoint_ST) :
    IsSquare ((A hep halmost_all_one) * (q hep halmost_all_one disjoint_ST) : ℤ_[p]) := by
  set A := hilbertSym.A hep halmost_all_one
  set q := hilbertSym.q hep halmost_all_one disjoint_ST
  have q_cong := hilbertSym.q_cong hep halmost_all_one disjoint_ST
  have not_dvd := p_mem_S_not_dvd_x hep halmost_all_one disjoint_ST hpS hpq
  by_cases hp2 : p = ⟨2, prime_two⟩
  · rw [hp2] at not_dvd ⊢
    apply PadicInt.isSquare_of_zmodPow not_dvd
    have : (q : ZMod 8) = A := by
      apply ModEq.of_dvd at q_cong
      · rwa [← ZMod.natCast_eq_natCast_iff] at q_cong
      · simp only [(by omega : 8 = 4 * 2)]
        rw [mul_dvd_mul_iff_left (by omega)]
        exact dvd_prod_of_mem Subtype.val (two_in_S a)
    simp [q, A, this]
  · apply PadicInt.isSquare_of_zmod (by rw [ne_eq, Primes.coe_nat_inj p ⟨2, prime_two⟩]; exact hp2)
      not_dvd
    have : (q : ZMod p) = A := by
      apply ModEq.of_dvd at q_cong
      · rwa [← ZMod.natCast_eq_natCast_iff] at q_cong
      · exact Nat.dvd_mul_left_of_dvd (dvd_prod_of_mem Subtype.val hpS) 4
    simp [q, A, this]

include disjoint_ST in
private lemma isSquare_x_of_p_mem_S {p : Primes} (hpS : p ∈ S a)
    (hpq : p ≠ q hep halmost_all_one disjoint_ST) :
      IsSquare (x hep halmost_all_one disjoint_ST : ℚ_[p]) := by
  have ⟨b, hb⟩ :=
    (isSquare_iff_exists_mul_self _).mp (isSquare_x hep halmost_all_one disjoint_ST hpS hpq)
  use b
  simp only [x, cast_prod, mk0_mul, val_mul, val_mk0, Rat.cast_mul, Rat.cast_prod,
    Rat.cast_natCast, ← PadicInt.coe_mul, ← hb]
  simp [← PadicInt.algebraMap_apply]

include disjoint_ST in
private lemma padicValRat_x_eq_one_of_p_mem_T (p : Primes)
    (pneq : p ≠ q hep halmost_all_one disjoint_ST) (hpT : p ∈ T hep halmost_all_one) :
      padicValRat p (x hep halmost_all_one disjoint_ST).val = 1 := by
  have q_prime := hilbertSym.q_prime hep halmost_all_one disjoint_ST
  have : Fact (Nat.Prime (q hep halmost_all_one disjoint_ST)) := ⟨q_prime⟩
  have hTp : T hep halmost_all_one = (T hep halmost_all_one \ {p}) ∪ {p} := by
    rw [union_singleton, insert_sdiff_self_of_mem hpT]
  simp only [x, cast_prod, mk0_mul, val_mul, val_mk0]
  rw [padicValRat.mul (by exact_mod_cast A_ne_zero hep halmost_all_one) (by simp [q_prime.ne_zero]),
    padicValRat.of_nat]
  simp only [ne_eq, pneq, not_false_eq_true, padicValNat_primes, CharP.cast_eq_zero, add_zero]
  rw [← cast_prod, hTp, prod_union (by simp), prod_singleton, padicValRat.of_nat,
    padicValNat.mul ?_ (by simp [p.2.ne_zero]), padicValNat_self, cast_add, cast_one, add_eq_right]
  · rw [Int.natCast_eq_zero, padicValNat.eq_zero_iff]
    apply Or.inr (Or.inr ((prime_iff.mp p.2).not_dvd_finsetProd fun t ↦ ?_))
    simp [ne_comm, prime_dvd_prime_iff_eq p.2 t.2, Primes.coe_nat_inj]
  · have := A_ne_zero hep halmost_all_one
    rw [hilbertSym.A, hTp, prod_union sdiff_disjoint, mul_ne_zero_iff] at this
    exact this.1

include disjoint_ST in
private lemma padicValRat_x_eq_zero_of_p_notMem_T
    {p : Primes} (pneq : p ≠ q hep halmost_all_one disjoint_ST) (hpT : p ∉ T hep halmost_all_one) :
      padicValRat p (x hep halmost_all_one disjoint_ST).val = 0 := by
  have q_prime := hilbertSym.q_prime hep halmost_all_one disjoint_ST
  have : Fact (Nat.Prime (q hep halmost_all_one disjoint_ST)) := ⟨q_prime⟩
  simp only [x, cast_prod, mk0_mul, val_mul, val_mk0]
  rw [padicValRat.mul (by exact_mod_cast A_ne_zero hep halmost_all_one) (by simp [q_prime.ne_zero])]
  simp only [← cast_prod, padicValRat.of_nat, ne_eq, pneq, not_false_eq_true, padicValNat_primes,
    CharP.cast_eq_zero, add_zero, Int.natCast_eq_zero, padicValNat.eq_zero_iff]
  apply Or.inr (Or.inr ((prime_iff.mp p.2).not_dvd_finsetProd ?_))
  intro t ht
  rw [prime_dvd_prime_iff_eq p.2 t.2, Primes.coe_nat_inj, ← ne_eq]
  aesop

include ha hprod_eq_one hexists_in_completion disjoint_ST in
/-- We first prove the Existence Theorem when S and T are disjoint. -/
private lemma existence_disjoint (infty_not_mem_T : ∀ i : I, ereal i = 1) :
    ∃ x : ℚˣ, ∀ i : I, (hilbertSym (x : ℝ) (a i) = ereal i) ∧
      (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) := by
  let q := hilbertSym.q hep halmost_all_one disjoint_ST
  have q_prime := hilbertSym.q_prime hep halmost_all_one disjoint_ST
  have : Fact (Nat.Prime q) := ⟨q_prime⟩
  let x := x hep halmost_all_one disjoint_ST
  use x
  --We apply lemma all_but_one_places_suffice to avoid dealing with q. Then we consider separately
  --the cases of p ∈ S, p ∈ T, p ∉ S ∪ T.
  apply all_but_one_places_suffice ha hep halmost_all_one hprod_eq_one ⟨q, q_prime⟩ x
  refine fun i ↦
    ⟨(by rw [real_eq (by simp) (by simp [ha]), infty_not_mem_T]
         simp [x, x_pos hep halmost_all_one disjoint_ST]), fun p pneq ↦ ?_,⟩
  have hpq : p.1 ≠ q := by simpa [ne_eq, Primes.coe_nat_inj p ⟨q, q_prime⟩]
  by_cases hpS : p ∈ S a
  · --case p ∈ S: LHR = 1 because x is a square, RHS = 1 because p ∉ T.
    have ⟨sqrt_x, hx⟩ := isSquare_x_of_p_mem_S hep halmost_all_one disjoint_ST hpS hpq
    simp only [x, hx, ← pow_two, comm,
      ep_eq_one_of_mem_S_disjoint hep halmost_all_one disjoint_ST hpS i]
    rw [right_square_eq_one (by simp [ha])
      (by rw [← pow_ne_zero_iff two_ne_zero, pow_two, ← hx]; simp)]
  · --case p ∉ S: (x, a_i)ₚ = (legendreSym p a_i) ^ val_p(x).
    have hp2 : p.1 ≠ 2 := by
      rw [ne_eq, Primes.coe_nat_inj p ⟨2, prime_two⟩]
      have := two_in_S a
      grind
    rw [← Int.cast_inj (α := ℚ), padic_odd_eq hp2 (by simp only [ne_eq, Rat.cast_eq_zero,
      ne_zero, not_false_eq_true]) (by simp only [ne_eq, Int.cast_eq_zero, ha, not_false_eq_true])]
    by_cases hpT : p ∈ T hep halmost_all_one
      --case p ∈ T: val_p(x) = 1.
    · have val_x : padicValRat p x.val = 1 :=
        padicValRat_x_eq_one_of_p_mem_T hep halmost_all_one disjoint_ST p hpq hpT
      --we extract xp from hexists_in_completion and use it.
      obtain ⟨xp, hxp⟩ := hexists_in_completion.2 p
      have val_xp : Odd xp.valuation := by
        simp only [hilbertSym.T, Int.reduceNeg, Set.Finite.mem_toFinset, Set.mem_iUnion,
          Set.mem_ofPred_eq, T] at hpT
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
        padicValRat_x_eq_zero_of_p_notMem_T hep halmost_all_one disjoint_ST hpq hpT
      simp only [hilbertSym.T, Int.reduceNeg, ep_eq_neg_one_iff_not_one hep, Set.mem_iUnion,
        Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_exists, Decidable.not_not, T] at hpT
      simpa [val_x, is_unit_ai_of_p_notMem_S ha hpS,] using (Int.cast_inj.mpr (hpT i).symm)

end Finite

private noncomputable abbrev xp := fun (p : Primes) ↦ (hexists_in_completion.2 p).choose

private lemma xp_eq (p : Primes) :
    ∀ (i : I), hilbertSym (xp hexists_in_completion p) (a i) = ep i p :=
  (hexists_in_completion.2 p).choose_spec

include hep in
private lemma xp_ne_zero [Nonempty I] (p : Primes) : xp hexists_in_completion p ≠ 0 := by
  intro hp
  have := xp_eq hexists_in_completion p
  simp [hilbertSym, hp] at this
  have := hep (Classical.arbitrary I) p
  grind

private noncomputable abbrev xr := hexists_in_completion.1.choose

private lemma xr_eq : ∀ (i : I), hilbertSym (xr hexists_in_completion) (a i) = ereal i :=
  hexists_in_completion.1.choose_spec

include hereal in
private lemma xr_ne_zero [Nonempty I] : xr hexists_in_completion ≠ 0 := by
    intro hr
    have := xr_eq hexists_in_completion
    simp only [hilbertSym, hr, Int.cast_eq_zero, true_or, ↓reduceIte] at this
    let i : I := Classical.arbitrary I
    have h := hereal i
    simp only [← this] at h
    grind

-- merged to mathlib
variable {α : Type*} [Monoid α]

/-- If `a` is a unit, then it is a square if and only if its underlying element in the monoid is a
square. -/
@[to_additive (attr := simp) /-- If `a` is an additive unit, then it is even if and only if its
underlying element in the additive monoid is even. -/]
lemma Units.isSquare_coe_iff {a : αˣ} : IsSquare (a : α) ↔ IsSquare a :=
  ⟨fun ⟨b, hb⟩ ↦ ⟨(isUnit_mul_self_iff.mp <| hb ▸ a.isUnit).unit, Units.ext hb⟩,
    fun ⟨b, hb⟩ ↦ ⟨b.val, by simp [hb]⟩⟩

open ContinuousMulEquiv Topology

@[simps! apply symm_apply]
private noncomputable def F (S' : Finset Nat.Primes) :
    (ℝ × ((p : S') → ℚ_[p]))ˣ ≃ₜ* ℝˣ × ((p : S') → ℚ_[p]ˣ) where
  __ := (MulEquiv.prodUnits (M := ℝ) (N := (p : S') → ℚ_[p])).trans
    ((MulEquiv.refl ℝˣ).prodCongr MulEquiv.piUnits)
  continuous_toFun :=
    (continuous_prodMk.mpr ⟨continuous_fst, (map_continuous piUnits).comp continuous_snd⟩).comp
      ((Units.continuous_map continuous_fst).prodMk (Units.continuous_map continuous_snd))
  continuous_invFun := by
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe,
      MulEquiv.coe_toEquiv_symm]
    exact (Equiv.continuous_symm_iff _).mpr
      ((IsOpenMap.id.prodMap (piUnits (M := fun p : S' ↦ ℚ_[p])).isOpenMap).comp
        (ContinuousMulEquiv.prodUnits ℝ ((p : S') → ℚ_[p])).isOpenMap)

variable [Finite I]

include hereal hep in
/-- The following lemma uses the Approximation Theorem to show that there exists a rational number
x' such that x'/xp is a square in ℚ_[p] for all p ∈ S and x'/xr is a square in ℝ. -/
private lemma square_approx [Nonempty I] :
    ∃ x' : ℚˣ, IsSquare (x' / xr hexists_in_completion) ∧
     (∀ p : Primes, p ∈ S a → IsSquare (x' / (xp hexists_in_completion p) : ℚ_[p])) := by
  set xp := xp hexists_in_completion
  have xp_eq := xp_eq hexists_in_completion
  have xp_ne_zero := xp_ne_zero hep hexists_in_completion
  set xr := xr hexists_in_completion
  have xr_eq := xr_eq hexists_in_completion
  have xr_ne_zero := xr_ne_zero hereal hexists_in_completion
  --The rationals are dense in the product of the reals and the p-adics for p ∈ S, so
  --every nonempty open set contains a rational number.
  have approx := dense_iff_inter_open.mp (Rat.approximation_units (S a))
  --Define the open nonempty set U of points (x, (y_p)_{p ∈ S}) such that x/xr is a square in ℝˣ
  --and y_p/xp is a square in ℚ_[p]ˣ for all p in S.
  set U : Set ((ℝ × ((p : S a) → ℚ_[p]))ˣ) := (F (S a))⁻¹'
    ({x : ℝˣ | 0 < x.val / xr} ×ˢ Set.univ.pi fun (p : S a) ↦ {x : ℚ_[p]ˣ | IsSquare (x / xp p)})
  have hUopen : IsOpen U := by
    refine IsOpen.preimage (map_continuous (F (S a))) (isOpen_prod_iff.mpr
      fun sr sp hs ↦ ⟨{x | 0 < ↑x / xr}, Set.univ.pi fun p ↦ {x | IsSquare (↑x / xp ↑p)},
        isOpen_lt continuous_const (continuous_val.mul_const xr⁻¹),
        isOpen_set_pi Set.finite_univ fun p _ ↦ ?_, by simp_all⟩)
    have hp : xp p ≠ 0 := xp_ne_zero p
    rw [← (Homeomorph.smulConst (Units.mk0 (xp p) (xp_ne_zero p))).isOpen_preimage ]
    simp only [Set.preimage_ofPred_eq, Homeomorph.smulConst_apply, _root_.smul_eq_mul, val_mul,
      val_mk0, ne_eq, hp, not_false_eq_true, mul_div_cancel_right₀, Units.isSquare_coe_iff]
    exact (Padic.unitSquares p).isOpen
  have hUnonempty : U.Nonempty :=
    ⟨(F (S a)).symm (Units.mk0 xr xr_ne_zero, fun p : S a ↦ Units.mk0 (xp p) (xp_ne_zero p)),
      by aesop⟩
  --Any rational point in U satisfies the desired properties.
  obtain ⟨z, hz, x', rfl⟩ := approx U hUopen hUnonempty
  use x'
  simp only [eq_ratCast, Set.mem_preimage, F_apply, MulEquiv.prodCongr, MulEquiv.toEquiv_eq_coe,
    MulEquiv.prodUnits, val_inv_eq_inv_val, MulEquiv.coe_mk, Equiv.coe_fn_mk, MonoidHom.prod_apply,
    Equiv.prodCongr_apply, EquivLike.coe_coe, MulEquiv.coe_refl, Prod.map_apply, id_eq,
    Set.mem_prod, Set.mem_ofPred_eq, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk,
    MonoidHom.coe_fst, Set.mem_pi, Set.mem_univ, MulEquiv.val_piUnits_apply, MonoidHom.coe_snd,
    forall_const, Subtype.forall, U] at hz
  exact ⟨by simp [Real.isSquare_iff, hz.1.le], hz.2⟩

include ha hereal hep in
/-- Given a finite set of rational numbers `{a_i}_{i ∈ I}` and numbers `e_{i,v} ∈ {± 1}`,
there exists a rational number `x` such that the Hilbert symbols `(x,a_i)_v` at each place `v`
is equal to `e_{i,v}` if and only if
1) for all `i`, almost all `e_{i,v}` are 1
2) for all `i`, the product of all `e_{i,v}` is 1
3) for each place `v`, there is some `x_v ∈ Q_v` with `(x_v,a_i)_v = e_{i,v}`. -/
theorem exists_rat_with_finite_prescribed_hilbertSym_of_int [Nonempty I] :
    (∃ x : ℚˣ, ∀ i : I, (hilbertSym (x : ℝ) (a i) = ereal i) ∧
    (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p)) ↔
    (∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) ∧
      (∀ i : I, ereal i * (∏ᶠ (p : Primes), ep i p) = 1) ∧
      (∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i) ∧
      ((∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) := by
  refine ⟨fun ⟨x, h⟩ ↦ necessary_cond ha _ h,
    fun ⟨halmost_all_one, hprod_eq_one, hexists_in_completion⟩ ↦ ?_⟩
  by_cases disjoint_ST : Disjoint (S a) (T hep halmost_all_one) ∧ ∀ i : I, ereal i = 1
  · exact existence_disjoint ha hep halmost_all_one hprod_eq_one hexists_in_completion
      disjoint_ST.1 disjoint_ST.2
  · set xp := xp hexists_in_completion
    set xr := xr hexists_in_completion
    obtain ⟨x', hxreal, hxp⟩ := square_approx hereal hep hexists_in_completion
    have haaox' (i : I) := almost_all_one x' (Units.mk0 (a i) (by simp [ha]))
    have hpeox' (i : I) :
        hilbertSym (x' : ℝ) (a i) * (∏ᶠ (p : Primes), hilbertSym (x' : ℚ_[p]) (a i)) = 1 :=
      prod_eq_one x' (Units.mk0 (a i) (by simp [ha]))
    have agree_on_S (i : I) (p : Primes) (hpS : p ∈ (S a)) :
        hilbertSym (x' : ℚ_[p]) (a i) = ep i p := by
      have : hilbertSym (x' : ℚ_[p]) (a i) = hilbertSym (xp p) (a i) := by
        obtain ⟨c, hc⟩ : ∃ c, x' = xp p * c ^ 2 := by
          obtain ⟨c', hc'⟩ := hxp p hpS
          use c'
          rw [pow_two, ← hc', mul_div_assoc', mul_div_cancel_left₀ _
            (xp_ne_zero hep hexists_in_completion p)]
        rw [hc, mul_left_square_eq (by aesop)]
      rw [this, xp_eq]
    have agree_on_infty (i : I) : hilbertSym (x' : ℝ) (a i) = ereal i := by
      have : hilbertSym (x' : ℝ) (a i) = hilbertSym (xr) (a i) := by
        have ⟨c, hc⟩ : ∃ c, x' = xr * c ^ 2 := by
          obtain ⟨c', hc'⟩ := hxreal
          use c'
          rw [pow_two, ← hc', mul_div_assoc', mul_div_cancel_left₀ _
            (xr_ne_zero hereal hexists_in_completion)]
        rw [hc, mul_left_square_eq (by aesop)]
      rw [this, xr_eq]
    set etar : I → ℤ := fun i ↦ (ereal i) * hilbertSym (x' : ℝ) (a i)
    set etap : I → Primes → ℤ := fun i p ↦ (ep i p) * hilbertSym (x' : ℚ_[p]) (a i)
    have hetap1 (i : I) (p : Primes) : etap i p = 1 ∨ etap i p = -1 := by
      have := eq_one_or_neg_one_of_ne_zero (by simp : (x'.1 : ℚ_[p]) ≠ 0)
        (by simp [ha] : ((a i) : ℚ_[p]) ≠ 0)
      grind
    have heta1 (i : I) : ∀ᶠ p : Primes in cofinite, etap i p = 1 := by
      let F := {p : Primes | ¬hilbertSym (x' : ℚ_[p]) (a i) = 1} ∪ {p | ¬ep i p = 1}
      have finiteF : F.Finite := by
        simp only [Set.finite_union, F]
        exact ⟨haaox' i, halmost_all_one i⟩
      exact Set.Finite.subset finiteF (fun p ↦ by grind)
    have heta2 (i : I) : etar i * (∏ᶠ (p : Primes), etap i p) = 1 := by
      simp only [etap, etar]
      rw [finprod_mul_distrib (halmost_all_one i)]
      · calc _
        _ = (ereal i * (∏ᶠ (p : Primes), ep i p)) * (hilbertSym (x' : ℝ) (a i) *
          (∏ᶠ (p : Primes), hilbertSym (x' : ℚ_[p]) (a i))) := by ring
        _ = 1 * 1 := by rw [hprod_eq_one i, hpeox' i]
      · exact haaox' i
    have heta3 : (∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = etar i) ∧
        (∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = etap i p) :=
      ⟨⟨x' * hexists_in_completion.1.choose, (by simp [etar, mul_left_eq]; grind)⟩,
        fun p ↦ ⟨x' * xp p, fun i ↦ (by simp [xp, mul_left_eq, xp_eq, etap]; ring)⟩⟩
    have etadisj : Disjoint (S a) (T hetap1 heta1) := by
      suffices ∀ i : I, ∀ p ∈ S a, etap i p = 1 by
        exact Finset.disjoint_left.mpr fun p hpS ↦
          (ep_eq_one_iff_not_mem_T _ _ _).mpr fun i ↦ this i p hpS
      intro i p hpS
      simp [etap, agree_on_S i p hpS, mul_self_eq_one_iff.mpr (hep i p)]
    have etainfT (i : I) : etar i = 1 := by
      simp [etar, agree_on_infty, mul_self_eq_one_iff.mpr (hereal i)]
    have ⟨xeta, hxeta⟩ := existence_disjoint ha hetap1 heta1 heta2 heta3 etadisj
      etainfT
    exact ⟨xeta * x', fun i ↦ ⟨by simp [hxeta i, etainfT i, agree_on_infty i],
      fun p ↦ by simp [mul_left_eq, hxeta i, etap]; grind⟩⟩

end Integer

theorem exists_rat_with_finite_prescribed_hilbertSym
    {I : Type*} [Finite I] [Nonempty I] (a : I → ℚˣ) {ereal : I → ℤ} {ep : I → Primes → ℤ}
    (hereal : ∀ i : I, ereal i = 1 ∨ ereal i = -1)
    (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1) :
    (∃ x : ℚˣ, ∀ i : I, hilbertSym (x : ℝ) (a i) = ereal i ∧
      (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p)) ↔
      (∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) ∧
      (∀ i : I, ereal i * (∏ᶠ (p : Primes), ep i p) = 1) ∧
      ((∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i) ∧
      (∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) := by
  simp_rw [← num_mul_den_right]
  exact exists_rat_with_finite_prescribed_hilbertSym_of_int
    (a := fun i ↦ ((a i).1.num * (a i).1.den : ℤ)) (fun _ ↦ by aesop) hereal hep

theorem exists_rat_with_two_prescribed_hilbertSym (a b : ℚˣ) {er er' : ℤ} {ep ep' : Primes → ℤ}
    (her : er = 1 ∨ er = -1) (her' : er' = 1 ∨ er' = -1)
    (hep : ∀ p : Primes, ep p = 1 ∨ ep p = -1) (hep' : ∀ p : Primes, ep' p = 1 ∨ ep' p = -1) :
    (∃ x : ℚˣ, hilbertSym (x : ℝ) a = er ∧ hilbertSym (x : ℝ) b = er' ∧
      (∀ p : Primes, hilbertSym (x : ℚ_[p]) a = ep p ∧ hilbertSym (x : ℚ_[p]) b = ep' p)) ↔
      ((∀ᶠ (p : Primes) in cofinite, ep p = 1) ∧
      (∀ᶠ (p : Primes) in cofinite, ep' p = 1)) ∧
     ((er * (∏ᶠ (p : Primes), ep p) = 1) ∧ (er' * (∏ᶠ (p : Primes), ep' p) = 1)) ∧
      (∃ xr : ℝ, hilbertSym xr a = er ∧ hilbertSym xr b = er') ∧
      (∀ (p : Primes), ∃ xp : ℚ_[p], hilbertSym xp a = ep p ∧ hilbertSym xp b = ep' p) := by
  convert exists_rat_with_finite_prescribed_hilbertSym (I := Fin 2) (a := ![a, b])
    (ep := ![ep, ep']) (ereal := ![er, er']) (by simp [her, her']) (by simp [hep, hep']) <;>
  aesop

end hilbertSym
