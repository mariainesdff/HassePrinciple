/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández, Mallory Dolorfino
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
lemma norm_mul_pow_neg_valuation_eq_one {x : ℚ_[p]} (hx : x ≠ 0) :
    ‖x * p ^ (-x.valuation)‖ = 1 := by
  simp [-zpow_neg, norm_eq_zpow_neg_valuation hx, zpow_neg_mul_zpow_self _ NeZero.out]

/-- Given a nonzero padic number `x`, the unit part of `x` is defined as the element `u` in `ℤ_[p]ˣ`
such that `u = x(p^{-v(x)})` -/
noncomputable def unitPart : ℤ_[p]ˣ :=
  PadicInt.mkUnits (norm_mul_pow_neg_valuation_eq_one (Units.ne_zero x))

/-- The p-adic valuation of a p-adic unit in `Z_[p]` is 0 -/
lemma valuation_units (a : ℤ_[p]ˣ) : (a : ℤ_[p]).valuation = 0 := by
  have h₁ : ‖(a : ℤ_[p])‖ = 1 := PadicInt.norm_units a
  rw [PadicInt.norm_eq_zpow_neg_valuation (Units.ne_zero a), zpow_eq_one_iff_right₀
    (Nat.cast_nonneg' p) (by exact_mod_cast (Nat.Prime.ne_one Fact.out))] at h₁
  simpa only [neg_eq_zero, Int.natCast_eq_zero] using h₁

/-- valuation is `0' at `p' when `x' is `-1' or a prime `≠ p' -/
lemma valuation_eq_zero_of_neg_one_or_prime {p : ℕ} [Fact (Nat.Prime p)]
    {x : ℚ} (hx : x = -1 ∨ ∃ r : ℕ, Nat.Prime r ∧ x = r ∧ p ≠ r) :
    (x : ℚ_[p]).valuation = 0 := by
  rw [valuation_ratCast]
  rcases hx with rfl | ⟨r, hr, rfl, hpr⟩
  · simp
  · have : Fact (Nat.Prime r) := ⟨hr⟩
    simp [padicValNat_primes hpr]

/-- The map that sends a padic integer to its unit part in ℤ_[p]ˣ is the natural inclusion. -/
lemma map_unitPart (a : ℤ_[p]ˣ) :
    unitPart (Units.map (algebraMap ℤ_[p] ℚ_[p]) a) = a := by
  ext
  simp [unitPart, valuation_units a]
  norm_cast

/-- For an odd prime `p` different from 2, the element `p` in ℤ_[2]ˣ is defined. -/
noncomputable abbrev p2 (hp : p ≠ 2) : ℤ_[2]ˣ :=
  PadicInt.mkUnits (Padic.norm_natCast_eq_one_iff.mpr
    ((Nat.coprime_primes Nat.prime_two Fact.out).mpr hp.symm))

/-- helper lemma: if `x,y ∈ ℚ_[p]` and `‖y‖ ≤ ‖x‖,` then `‖y *  p ^ (-x.valuation)‖ ≤ 1` -/
lemma norm_mul_zpow_valuation_le_one_of_norm_le {x y : ℚ_[p]} (hxy : ‖y‖ ≤ ‖x‖) :
    ‖y *  p ^ (-x.valuation)‖ ≤ 1 := by
  by_cases hx0 : x = 0
  · aesop
  simp only [zpow_neg, norm_mul, norm_inv, norm_p_zpow, ← Padic.norm_eq_zpow_neg_valuation hx0]
  rw [mul_inv_le_iff₀ (by simp [hx0])]
  simp [hxy]

open PadicInt in
/-- If `p` is a prime, `x, y, z ∈ ℚ_[p]` satisfy `z ^ 2 - p * x ^ 2 - v * y ^ 2`, with `v in`
`ℤ_[p]ˣ`, and not all of `x, y, z` are zero, then there exists a nontrivial solution to the same
equation with `z', y', x' ∈ ℤ_[p]`, and at least one is a unit -/
lemma exists_padicInt_sol {v : ℤ_[p]ˣ} {x y z : ℚ_[p]}
    (hnontriv : (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) :
    ∃ z' y' x' : ℤ_[p], z' ^ 2 - p * x' ^ 2 - v * y' ^ 2 = 0 ∧
    (IsUnit z' ∨ IsUnit y' ∨ IsUnit x') := by
  by_cases h : ‖y‖ ≤ ‖x‖ ∧ ‖z‖ ≤ ‖x‖
  · let x' := x * p ^ (-x.valuation)
    let y' := y * p ^ (-x.valuation)
    let z' := z * p ^ (-x.valuation)
    have x'_unit : ‖x'‖ = 1 := norm_mul_pow_neg_valuation_eq_one (by aesop)
    have y'_int : ‖y'‖ ≤ 1 := norm_mul_zpow_valuation_le_one_of_norm_le h.1
    have z'_int : ‖z'‖ ≤ 1 := norm_mul_zpow_valuation_le_one_of_norm_le h.2
    exact ⟨⟨z', z'_int⟩, ⟨y', y'_int⟩, ⟨x', x'_unit.le⟩,
      ⟨coe_eq_zero.mp (by grind : z' ^ 2 - p * x' ^ 2 - v * y' ^ 2 = 0),
      Or.inr (Or.inr (isUnit_iff.mpr x'_unit))⟩⟩
  · by_cases h_1 : ‖z‖ ≤ ‖y‖
    · rw [or_left_comm] at hnontriv
      let x' := x * p ^ (-y.valuation)
      let y' := y * p ^ (-y.valuation)
      let z' := z * p ^(-y.valuation)
      have : ‖x‖ ≤ ‖y‖ := by grind
      have y'_unit : ‖y'‖ = 1 := norm_mul_pow_neg_valuation_eq_one (by aesop)
      have x'_int : ‖x'‖ ≤ 1 := norm_mul_zpow_valuation_le_one_of_norm_le (by grind)
      have z'_int : ‖z'‖ ≤ 1 := norm_mul_zpow_valuation_le_one_of_norm_le h_1
      exact ⟨⟨z', z'_int⟩, ⟨y', le_of_eq y'_unit⟩, ⟨x', x'_int⟩,
        ⟨coe_eq_zero.mp (by grind : z' ^ 2 - p * x' ^ 2 - v * y' ^ 2 = 0),
        Or.inr (Or.inl (isUnit_iff.mpr y'_unit))⟩⟩
    · let x' := x * p ^ (-z.valuation)
      let y' := y * p ^ (-z.valuation)
      let z' := z * p ^ (-z.valuation)
      have : ‖x‖ ≤ ‖z‖ := by grind
      have z'_unit : ‖z'‖ = 1 := norm_mul_pow_neg_valuation_eq_one (by aesop)
      have x'_int : ‖x'‖ ≤ 1 := norm_mul_zpow_valuation_le_one_of_norm_le (by grind)
      have y'_int : ‖y'‖ ≤ 1 := norm_mul_zpow_valuation_le_one_of_norm_le (not_le.mp h_1).le
      exact ⟨⟨z', le_of_eq z'_unit⟩, ⟨y', y'_int⟩, ⟨x', x'_int⟩,
        ⟨coe_eq_zero.mp (by grind : z' ^ 2 - p * x' ^ 2 - v * y' ^ 2 = 0),
        Or.inl (isUnit_iff.mpr z'_unit)⟩⟩

open PadicInt in
/-- If `p` is a prime, `x, y, z in ℚ_[p]` satisfy `z ^ 2 - p * x ^ 2 - v * y ^ 2`, with `v` nonzero,
and not all of `x, y, z` are zero, then there exists a nontrivial solution to the same equation with
`z', y'` units in `ℤ_[p]ˣ` and `x'` in `ℤ_[p]`. -/
lemma exists_nontrivial_units_zero {v : ℤ_[p]ˣ} {x y z : ℚ_[p]}
    (hnontriv : (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) :
    ∃ z' y' : ℤ_[p]ˣ, ∃ x' : ℤ_[p],
    (z' : ℤ_[p]) ^ 2 - p * (x') ^ 2 - v * (y' : ℤ_[p]) ^ 2 = 0 := by
  obtain ⟨z', y', x', hnewsol, hunits⟩ := exists_padicInt_sol hnontriv hsol
  have not_unit_x_of_not_unit_y_z (hy : ¬ IsUnit y') (hz : ¬ IsUnit z') : ¬ IsUnit x' := by
    rw [not_isUnit_iff, norm_lt_one_iff_dvd, ← Prime.dvd_pow_iff_dvd prime_p two_ne_zero]
    have hp2 : (p : ℤ_[p]) ^ 2 ∣ p * x' ^ 2 := by
      rw [show p * x' ^ 2 = z' ^ 2 - v * y' ^ 2 by grind]
      apply dvd_sub (pow_dvd_pow_of_dvd ((norm_lt_one_iff_dvd _).mp (not_isUnit_iff.mp hz)) 2)
      simp [pow_dvd_pow_of_dvd ((norm_lt_one_iff_dvd _).mp (not_isUnit_iff.mp hy)) 2]
    rwa [pow_two (p : ℤ_[p]), mul_dvd_mul_iff_left (by exact_mod_cast NeZero.out)] at hp2
  have hz'_unit : IsUnit z' := by
    by_contra hz
    have hy : ¬ IsUnit y' := by
      have : ¬ IsUnit (p * x' ^ 2 + v * y' ^ 2) := by
        have hz2 : ¬ IsUnit (z' ^ 2) := not_isUnit_iff.mpr (by simpa using not_isUnit_iff.mp hz)
        grind
      simp only [not_isUnit_iff, norm_lt_one_iff_dvd] at *
      have : (p : ℤ_[p]) ∣ v * y' ^ 2 := by rwa [← dvd_add_right (b := p * x' ^ 2) (by simp)]
      simp [Prime.dvd_pow_iff_dvd prime_p two_ne_zero] at this
      aesop
    aesop
  have hy'_unit : IsUnit y' := by
    by_contra hy
    have hz : ¬ IsUnit z' := by
      have : ¬ IsUnit (z' ^ 2 - p * x' ^ 2) := by
        have hy2 : ¬ IsUnit (v * y' ^ 2) := not_isUnit_iff.mpr
          (by simpa using not_isUnit_iff.mp hy)
        grind
      rw [not_isUnit_iff, norm_lt_one_iff_dvd, ← Prime.dvd_pow_iff_dvd prime_p two_ne_zero]
      rw [not_isUnit_iff, norm_lt_one_iff_dvd] at this
      simpa using dvd_iff_dvd_of_dvd_sub this
    aesop
  exact ⟨⟨z', z'.inv, mul_inv (isUnit_iff.mp hz'_unit), inv_mul
    (isUnit_iff.mp hz'_unit)⟩, ⟨y', y'.inv, mul_inv
    (isUnit_iff.mp hy'_unit), inv_mul (isUnit_iff.mp hy'_unit)⟩, x',
    hnewsol⟩

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

namespace PadicInt

open Polynomial

lemma p_dvd_iff_toZMod_eq_zero {p : ℕ} [Fact (Nat.Prime p)] {m : ℤ_[p]} :
    (p : ℤ_[p]) ∣ m ↔ m.toZMod = 0 := by
  rw [← Ideal.mem_span_singleton, ← maximalIdeal_eq_span_p, ← RingHom.mem_ker, ker_toZMod]

lemma pow_p_dvd_iff_toZModPow_eq_zero {p : ℕ} [Fact (Nat.Prime p)] {m : ℤ_[p]} {n : ℕ} :
    (p : ℤ_[p]) ^ n ∣ m ↔ m.toZModPow n = 0 := by
  rw [← Ideal.mem_span_singleton, ← RingHom.mem_ker, ker_toZModPow]

/-- An element in `ℤ_[p]` for odd `p` is a square if its reduction modulo `p` is a square. -/
lemma isSquare_of_zmod {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≠ 2)
    {m : ℤ_[p]} (hm : ¬ (p : ℤ_[p]) ∣ m) (hmod : IsSquare m.toZMod) : IsSquare m := by
  obtain ⟨r, hr⟩ := hmod
  let a := (r.cast : ℤ_[p])
  let F : ℤ_[p][X] := X ^ 2 - C m
  have hF : ‖(aeval a) F‖ < ‖(aeval a) (derivative F)‖ ^ 2 := by
    have h2 : ‖(2 : ℤ_[p])‖ = 1 := by
      rw [← Nat.cast_two, norm_natCast_eq_one_iff]
      simp [Nat.coprime_two_right, Nat.Prime.odd_of_ne_two Fact.out hp]
    have h1 : ‖(r.cast : ℤ_[p])‖ = 1 := by
      rw [← isUnit_iff, ← IsLocalRing.notMem_maximalIdeal, ← ker_toZMod, RingHom.mem_ker]
      simp only [ZMod.ringHom_map_cast]
      by_contra h0
      simp only [h0, mul_zero, ← p_dvd_iff_toZMod_eq_zero] at hr
      exact hm hr
    simp only [aeval_sub, coe_aeval_eq_eval, eval_pow, eval_X, aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply, derivative_sub, derivative_X_pow_succ, Nat.cast_one, one_add_one_eq_two,
      pow_one, derivative_C, sub_zero, eval_mul, eval_C, norm_mul, a, F, h2, one_mul, h1, one_pow]
    simp [norm_lt_one_iff_dvd, p_dvd_iff_toZMod_eq_zero, hr, pow_two]
  obtain ⟨z, hz0, hz⟩ := hensels_lemma hF
  simp only [aeval_sub, coe_aeval_eq_eval, eval_pow, eval_X, aeval_C, Algebra.algebraMap_self,
    RingHom.id_apply, F, sub_eq_zero] at hz0
  exact ⟨z, by simp [← hz0, pow_two]⟩

/-- An element in `ℤ_[2]` is a square if its reduction modulo `8` is a square. -/
lemma isSquare_of_zmodPow {m : ℤ_[2]} (hm : ¬ (2 : ℤ_[2]) ∣ m) (hmod : IsSquare (m.toZModPow 3)) :
    IsSquare m := by
  obtain ⟨r, hr⟩ := hmod
  let a := (r.cast : ℤ_[2])
  let F : ℤ_[2][X] := X ^ 2 - C m
  have hF : ‖(aeval a) F‖ < ‖(aeval a) (derivative F)‖ ^ 2 := by
    have h1 : ‖(r.cast : ℤ_[2])‖ = 1 := by
      rw [← isUnit_iff, ← IsLocalRing.notMem_maximalIdeal, ← ker_toZMod, RingHom.mem_ker]
      simp only [Nat.reducePow, ← p_dvd_iff_toZMod_eq_zero, Nat.cast_ofNat]
      by_contra h0
      have : toZModPow 3 r.cast = r := by simp
      rw [← sub_eq_zero, ← this, ← map_mul, ← map_sub, ← pow_p_dvd_iff_toZModPow_eq_zero,
        Nat.cast_ofNat] at hr
      exact hm ((dvd_iff_dvd_of_dvd_sub (dvd_trans (dvd_pow_self 2 three_ne_zero) hr)).mpr
        (dvd_mul_of_dvd_left h0 r.cast))
    simp only [aeval_sub, coe_aeval_eq_eval, eval_pow, eval_X, aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply, derivative_sub, derivative_X_pow_succ, Nat.cast_one, one_add_one_eq_two,
      pow_one, derivative_C, sub_zero, eval_mul, eval_C, norm_mul, a, F, mul_one, h1,
      ← Nat.cast_two (R := ℤ_[2]), PadicInt.norm_p, ← zpow_neg_one, ← zpow_natCast,
      ← zpow_mul, Nat.reducePow, Int.reduceNeg, neg_mul, one_mul,
      norm_lt_pow_iff_norm_le_pow_sub_one, Nat.cast_ofNat (R := ℤ), Int.reduceSub]
    rw [← Nat.cast_three, norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton,
      pow_p_dvd_iff_toZModPow_eq_zero]
    simp [hr, pow_two]
  obtain ⟨z, hz0, hz⟩ := hensels_lemma hF
  simp only [aeval_sub, coe_aeval_eq_eval, eval_pow, eval_X, aeval_C, Algebra.algebraMap_self,
    RingHom.id_apply, F, sub_eq_zero] at hz0
  exact ⟨z, by simp [← hz0, pow_two]⟩

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
