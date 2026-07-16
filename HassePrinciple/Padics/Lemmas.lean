/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.Algebra.Polynomial.Basic

/-! # Auxiliary result about padic numbers. -/

@[expose] public section

/-- An indexed family `f : σ → M` of elements is called primitive if at least one of the
  elements in the image is a unit. -/
def Function.IsPrimitive {M σ : Type*} [Monoid M] (f : σ → M) : Prop :=
   ∃ (s : σ), IsUnit (f s)

namespace Padic

variable {p : ℕ} [Fact (Nat.Prime p)] (x : ℚ_[p]ˣ)

/-- Given a nonzero padic number `x`, the norm of `x` times `p` raised to the negative of its
valuation equals one. -/
lemma norm_mul_pow_neg_valuation_eq_one : ‖(x : ℚ_[p]) * p ^ (- valuation x.val)‖ = 1 := by
  simp [norm_eq_zpow_neg_valuation, inv_mul_cancel₀ (zpow_ne_zero _ NeZero.out)]

/-- Given a nonzero padic number `x`, the unit part of `x` is defined as the element `u` in `ℤ_[p]ˣ`
such that `u = x(p^{-v(x)})` -/
noncomputable def unitPart : ℤ_[p]ˣ :=
  PadicInt.mkUnits (norm_mul_pow_neg_valuation_eq_one x)

/-- The p-adic valuation of a p-adic unit in `Z_[p]` is 0 -/
lemma valuation_units (a : ℤ_[p]ˣ) : (a : ℤ_[p]).valuation = 0 := by
  have h₁ : ‖(a : ℤ_[p])‖ = 1 := PadicInt.norm_units a
  rw [PadicInt.norm_eq_zpow_neg_valuation (Units.ne_zero a), zpow_eq_one_iff_right₀
    (Nat.cast_nonneg' p) (by exact_mod_cast (Nat.Prime.ne_one Fact.out))] at h₁
  simpa only [neg_eq_zero, Int.natCast_eq_zero] using h₁


/-- The map that sends a padic integer to its unit part in ℤ_[p]ˣ is the natural inclusion. -/
lemma map_unitPart (a : ℤ_[p]ˣ) :
    unitPart (Units.map (algebraMap ℤ_[p] ℚ_[p]) a) = a := by
  ext
  simp [unitPart, valuation_units a]

/-- For an odd prime `p` different from 2, the element `p` in ℤ_[2]ˣ is defined. -/
noncomputable abbrev p2 (hp : p ≠ 2) : ℤ_[2]ˣ :=
  PadicInt.mkUnits (Padic.norm_natCast_eq_one_iff.mpr
    ((Nat.coprime_primes Nat.prime_two Fact.out).mpr hp.symm))

-- List.max [‖x‖, ‖y‖, ‖z‖]

/-- If `p` is a prime, `x, y, z in ℚ_[p]` satisfy `z ^ 2 - p * x ^ 2 - v * y ^ 2`, with `v` nonzero,
and not all of `x, y, z` are zero, then there exists a nontrivial solution to the same equation with
`z', y',` and `x'` in `ℤ_[p]`, and at least one is a unit -/
lemma exists_padicInt_sol {v : ℚ_[p]ˣ} {x y z : ℚ_[p]}
    (hnontriv : (x, y, z) ≠ (0, 0, 0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) :
    ∃ z' y' x' : ℤ_[p],
      (z' : ℚ_[p]) ^ 2 - p * (x' : ℚ_[p]) ^ 2 - v * (y' : ℚ_[p]) ^ 2 = 0
      ∧ (IsUnit z' ∨ IsUnit y' ∨ IsUnit x') := by
      set min := List.min [x.valuation, y.valuation, z.valuation] (by simp)
      let x' := x * p ^ (-min)
      let y' := y * p ^ (-min)
      let z' := z * p ^ (-min)
      have hx'_int : ‖x'‖ ≤ 1 := by
        unfold x'
        simp only [zpow_neg, norm_mul, norm_inv, norm_p_zpow, inv_inv]
        by_cases (x = 0)
        · have hx : ‖x‖ = 0 := by (expose_names; exact norm_eq_zero.mpr h)
          simp [hx, zero_mul, zero_le_one]
        · expose_names
          have h₁ : x ≠ 0 := h
          simp only [norm_eq_zpow_neg_valuation h₁]
          rw [mul_comm,← zpow_add₀ (by exact_mod_cast (Nat.Prime.ne_zero Fact.out))]
          have hexpneg : min + -x.valuation ≤ 0 := by
            simp [min, List.min]
          have hp_ge_one : 1 ≤ (p : ℝ) := by exact_mod_cast (Nat.Prime.one_le Fact.out)
          apply zpow_le_one_of_nonpos₀ (hp_ge_one) (hexpneg)
      have hy'_int : ‖y'‖ ≤ 1 := by
        unfold y'
        simp only [zpow_neg, norm_mul, norm_inv, norm_p_zpow, inv_inv]
        by_cases (y = 0)
        · have hy : ‖y‖ = 0 := by (expose_names; exact norm_eq_zero.mpr h)
          simp [hy, zero_mul, zero_le_one]
        · expose_names
          have h₁ : y ≠ 0 := h
          simp only [norm_eq_zpow_neg_valuation h₁]
          rw [mul_comm,← zpow_add₀ (by exact_mod_cast (Nat.Prime.ne_zero Fact.out))]
          have hexpneg : min + -y.valuation ≤ 0 := by
            simp [min, List.min]
          have hp_ge_one : 1 ≤ (p : ℝ) := by exact_mod_cast (Nat.Prime.one_le Fact.out)
          apply zpow_le_one_of_nonpos₀ (hp_ge_one) (hexpneg)
      have hz'_int : ‖z'‖ ≤ 1 := by
        unfold z'
        simp only [zpow_neg, norm_mul, norm_inv, norm_p_zpow, inv_inv]
        by_cases (z = 0)
        · have hz : ‖z‖ = 0 := by (expose_names; exact norm_eq_zero.mpr h)
          simp [hz, zero_mul, zero_le_one]
        · expose_names
          have h₁ : z ≠ 0 := h
          simp only [norm_eq_zpow_neg_valuation h₁]
          rw [mul_comm,← zpow_add₀ (by exact_mod_cast (Nat.Prime.ne_zero Fact.out))]
          have hexpneg : min + -z.valuation ≤ 0 := by
            simp [min, List.min]
          have hp_ge_one : 1 ≤ (p : ℝ) := by exact_mod_cast (Nat.Prime.one_le Fact.out)
          apply zpow_le_one_of_nonpos₀ (hp_ge_one) (hexpneg)
      let z' : ℤ_[p] := ⟨z', hz'_int⟩
      let y' : ℤ_[p] := ⟨y', hy'_int⟩
      let x' : ℤ_[p] := ⟨x',hx'_int⟩
      have hnewsol : ((z' : ℚ_[p])^2 - p * (x' : ℚ_[p])^2
       - v * (y' : ℚ_[p])^2 = 0) := by
        unfold x' y' z'
        grind
      have h_or_is_unit : (IsUnit z' ∨ IsUnit y' ∨ IsUnit x') := by
        have min_is_mem : (min = x.valuation ∨ min = y.valuation ∨ min = z.valuation) := by
          simpa [min] using List.min_mem (l := [x.valuation, y.valuation, z.valuation]) (by simp)
        by_cases (min = x.valuation)
        · have hx'_unit : ‖x'‖ = 1 := by
            unfold x'
            simp only [PadicInt.norm_eq_padic_norm]
            expose_names
            unfold x'_1
            rw [h]
            sorry
          right
          right
          exact PadicInt.isUnit_iff.mpr hx'_unit
        · by_cases (min = y.valuation)
          · have hy'_unit : ‖y'‖ = 1 := by
              sorry
            right
            left
            exact PadicInt.isUnit_iff.mpr hy'_unit
          · have hzmin : (min = z.valuation) := by
              by_contra
              expose_names
              have hnotmineq : ¬(min = x.valuation ∨ min = y.valuation ∨ min = z.valuation) := by
                simp only [h, h_1, false_or, ← ne_eq]
                exact this
              contradiction
            have hz'_unit : ‖z'‖ = 1 := by
              sorry
            left
            exact PadicInt.isUnit_iff.mpr hz'_unit
      use z', y', x'

--better name?
/-- If `p` is a prime, `x, y, z in ℚ_[p]` satisfy `z ^ 2 - p * x ^ 2 - v * y ^ 2`, with `v` nonzero,
and not all of `x, y, z` are zero, then there exists a nontrivial solution to the same equation with
`z', y'` units in `ℤ_[p]ˣ` and `x'` in `ℤ_[p]`. -/
lemma exists_nontrivial_zero {v : (ℚ_[p])ˣ} {x y z : ℚ_[p]}
    (hnontriv : (x, y, z) ≠ (0, 0, 0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) :
    ∃ z' y' : ℤ_[p]ˣ, ∃ x' : ℤ_[p],
      (z' : ℚ_[p]) ^ 2 - p * (x' : ℚ_[p]) ^ 2 - v * (y' : ℚ_[p]) ^ 2 = 0 := by
  obtain ⟨z', y', x', hnewsol, hunits⟩ := exists_padicInt_sol hnontriv hsol
  have hvy'_int : ‖v * (y' : ℚ_[p]) ^ 2‖ ≤ 1 := by -- now can take the zmodrepr of v * y'
    rw [sub_eq_zero] at hnewsol
    rw [← hnewsol]
    rw [← PadicInt.mem_subring_iff]
    apply (PadicInt.subring p).sub_mem
    · apply (PadicInt.subring p).pow_mem
      simp only [SetLike.coe_mem]
    · apply (PadicInt.subring p).mul_mem
      · exact natCast_mem (PadicInt.subring p) p
      apply (PadicInt.subring p).pow_mem
      simp only [SetLike.coe_mem]
  let vy' : ℤ_[p] := ⟨v * (y' : ℚ_[p]) ^ 2, hvy'_int⟩
  let eq : ℤ_[p] := z' ^ 2 - p * x' ^ 2 - vy'
  have eq_zero : eq = 0 := by
    unfold eq
    unfold vy'
    exact PadicInt.coe_eq_zero.mp hnewsol
  have hz'_unit : IsUnit z' := by
    by_contra
    rw [PadicInt.not_isUnit_iff, PadicInt.norm_lt_one_iff_dvd] at this
    have hy'_norm_ne_one : ‖y'‖ < 1 := by
      have vy'_sq_eq : (v : ℚ_[p])*(y' : ℚ_[p]) ^ 2 = (z' : ℚ_[p]) ^ 2
      - (p : ℚ_[p]) * (x' : ℚ_[p]) ^ 2 := by
        rw [sub_eq_zero] at hnewsol
        rw [← hnewsol]
      have vy'_sq_norm_ne_one : ‖(v : ℚ_[p])*(y' : ℚ_[p]) ^ 2‖ < 1 := by
        rw [vy'_sq_eq]
        rw [dvd_def] at this
        sorry
      simp only [norm_mul, norm_pow, PadicInt.padic_norm_e_of_padicInt] at vy'_sq_norm_ne_one

      sorry
    have hx'_norm_ne_one : ‖x'‖ < 1 := by
      sorry
    have h_not_units : ¬(IsUnit z' ∨ IsUnit y' ∨ IsUnit x') := by
      simp only [not_or]
      constructor
      · rw [← PadicInt.norm_lt_one_iff_dvd, ← PadicInt.not_isUnit_iff] at this
        exact this
      · constructor
        · rw [← PadicInt.not_isUnit_iff] at hy'_norm_ne_one
          exact hy'_norm_ne_one
        · rw [← PadicInt.not_isUnit_iff] at hx'_norm_ne_one
          exact hx'_norm_ne_one
    contradiction
  have hy'_unit : IsUnit y' := by
    -- pretty much the same as hz'_unit
    sorry
  rw [PadicInt.isUnit_iff] at hz'_unit
  let z'' : ℤ_[p]ˣ := PadicInt.mkUnits hz'_unit
  rw [PadicInt.isUnit_iff] at hy'_unit
  let y'' : ℤ_[p]ˣ := PadicInt.mkUnits hy'_unit
  let x'' : ℤ_[p] := x'
  use z'', y'', x''
  exact hnewsol


lemma common_root_tfae {σ ι : Type*} {f : ι → MvPolynomial σ ℤ_[p]}
    (hf : ∀ i, (f i).IsHomogeneous (f i).totalDegree) :
    List.TFAE [∃ (z : σ → ℚ_[p]), (∃ s, z s ≠ 0)  ∧ (∀ i : ι, (f i).aeval z = 0),
      ∃ (z : σ → ℤ_[p]), z.IsPrimitive ∧ ∀ i : ι, (f i).aeval z = 0,
      ∀ {n : ℕ} (hn : 1 ≤ n),  ∃ (z : σ → ZMod (p ^ n)), z.IsPrimitive ∧
        ∀ i : ι, ((f i).map (PadicInt.toZModPow n)).aeval z = 0] := by
  sorry

end Padic



/-! # Applications and Multivariable Hensel's Lemma. -/

@[expose] public section


namespace Polynomial

/-- An element in ℤ_p (p odd) is a square if its reduction modulo p is a square. -/
lemma squares_in_Zp {p : ℕ} [Fact (Nat.Prime p)] (hodd : p ≠ 2) (m : ℤ_[p]) (n : ℕ)
    (hmod : m.zmodRepr ≡ n ^ 2 [MOD p]) : ∃ x : ℤ_[p], m = x ^ 2 := by
  let F : ℤ_[p][X] := X ^ 2 - C m
  sorry

/-- An element in ℤ_2 is a square if its reduction modulo 8 is a square. -/
lemma squares_in_Z2 (m : ℤ_[2]) (n : ℕ)
    (hmod : m.zmodRepr ≡ n ^ 2 [MOD 8]) : ∃ x : ℤ_[2], m = x^2 := by sorry

end Polynomial


namespace PadicInt

/-! ## Multivariable Hensel's Lemma -/


/-- Serre's generalization of Hensel's lemma to a multivariable polynomial over ℤ_[p]. If a
polynomial f in m variables has a solution a modulo p^n, and a is a zero modulo p^k of one of its
partial derivatives, with 0 < 2k < n, then there exists a solution in ℤ_[p], which is congruent to
a modulo p^{n-k}. -/
theorem multivariable_hensel {p : ℕ} [Fact (Nat.Prime p)] {m : ℕ}
    {f : MvPolynomial (Fin m) ℤ_[p]} {a : Fin m → ℤ_[p]}
    {n k : ℤ} (hk : 0 < 2 * k ∧ 2 * k < n) {j : Fin m}
    (hF : n ≤ valuation (MvPolynomial.aeval a f))
    (hJ : valuation (MvPolynomial.aeval a (MvPolynomial.pderiv j f)) = k) :
      ∃ (z : Fin m → ℤ_[p]), (MvPolynomial.aeval z f = 0) ∧
        ∀ i, n - k ≤ valuation (z i - a i) := by
  sorry

/-- Same theorem, in terms of norms. TODO: Keep one. -/
theorem multivariable_hensel' {p : ℕ} [Fact (Nat.Prime p)] {m : ℕ}
    {f : MvPolynomial (Fin m) ℤ_[p]} {a : Fin m → ℤ_[p]}
    {n k : ℤ} (hk : 0 < 2 * k ∧ 2 * k < n) {j : Fin m}
    (hF : ‖(MvPolynomial.aeval a) f‖ ≤ p ^ (-n))
    (hJ : ‖(MvPolynomial.aeval a) (MvPolynomial.pderiv j f)‖ = p ^ (-k)) :
      ∃ (z : Fin m → ℤ_[p]), (MvPolynomial.aeval z f = 0) ∧ ∀ i, ‖z i - a i‖ < p ^ (-n + k) := by
  sorry

end PadicInt
