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
lemma exists_padicInt_solution {v : ℚ_[p]ˣ} {x y z : ℚ_[p]}
    (hnontriv : (x, y, z) ≠ (0, 0, 0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) :
    ∃ z' y' x' : ℤ_[p],
      (z' : ℚ_[p]) ^ 2 - p * (x' : ℚ_[p]) ^ 2 - v * (y' : ℚ_[p]) ^ 2 = 0
      ∧ (IsUnit z' ∨ IsUnit y' ∨ IsUnit x') := by
      let max := List.max [‖x‖, ‖y‖, ‖z‖] (by simp)
      have hmax_ne_ze : ‖x‖ ≠ 0 := by
        by_contra
        sorry
      sorry

/-- If `p` is a prime, `x, y, z in ℚ_[p]` satisfy `z ^ 2 - p * x ^ 2 - v * y ^ 2`, with `v` nonzero,
and not all of `x, y, z` are zero, then there exists a nontrivial solution to the same equation with
`z', y',` and `x'` in `ℤ_[p]`, and at least one is a unit -/
lemma lift_solutions_to_int_first {v : ℚ_[p]ˣ} {x y z : ℚ_[p]}
    (hnontriv : (x, y, z) ≠ (0, 0, 0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) :
    ∃ z' y' x' : ℤ_[p],
      (z' : ℚ_[p]) ^ 2 - p * (x' : ℚ_[p]) ^ 2 - v * (y' : ℚ_[p]) ^ 2 = 0
      ∧ (IsUnit z' ∨ IsUnit y' ∨ IsUnit x') := by
      sorry
  --     #exit
  -- wlog h_x_max : (‖y‖ ≤ ‖x‖ ∧ ‖z‖ ≤ ‖x‖)
  -- · sorry
  -- · have h_x_ne_zero : x ≠ 0 := by -- prove that in this case, x ≠ 0
  --     have h_norm_x_ne_zero : 0 < ‖x‖ := by
  --       by_cases (z ≠ 0)
  --       · have hz : 0 < ‖z‖ := by
  --           expose_names
  --           exact norm_pos_iff.mpr h
  --         apply lt_of_lt_of_le hz h_x_max.2
  --       · by_cases (y ≠ 0)
  --         · have hy : 0 < ‖y‖ := by
  --             expose_names
  --             exact norm_pos_iff.mpr h_1
  --           apply lt_of_lt_of_le hy h_x_max.1
  --         · have hx : x ≠ 0 := by
  --             by_contra
  --             have htriv : (x,y,z) = (0,0,0) := by
  --               simp only [Prod.mk.injEq]
  --               constructor
  --               · exact this
  --               · constructor
  --                 · expose_names
  --                   simp only [ne_eq, not_not] at h_1
  --                   exact h_1
  --                 · expose_names
  --                   simp only [ne_eq, not_not] at h
  --                   exact h
  --             contradiction -- completes the proof that x ≠ 0 (in this case!)
  --           exact norm_pos_iff.mpr hx -- completes the proof that 0 < ‖x‖
  --     exact norm_pos_iff.mp h_norm_x_ne_zero -- completes the proof that x ≠ 0
  --   let x' := x * p ^ (-x.valuation)
  --   let y' := y * p ^ (-x.valuation)
  --   let z' := z * p ^(-x.valuation)
  --   have hx'unit : ‖x'‖ = 1 := by
  --     unfold x'
  --     have := norm_mul_pow_neg_valuation_eq_one (Units.mk0 x h_x_ne_zero)
  --     simp only [Units.val_mk0, zpow_neg, norm_mul,
  --     norm_inv, norm_p_zpow, inv_inv] at this
  --     simp only [zpow_neg, norm_mul, norm_inv, norm_p_zpow, inv_inv]
  --     exact this
  --   have hx' : ‖x'‖ ≤ 1 := by
  --     exact Std.le_of_eq hx'unit
  --   have hy' : ‖y'‖ ≤ 1 := by
  --     unfold y'
  --     simp only [zpow_neg, norm_mul, norm_inv, norm_p_zpow, inv_inv]
  --     have hxinvval : ↑p ^ x.valuation = ‖x‖⁻¹ := by
  --       have := norm_mul_pow_neg_valuation_eq_one (Units.mk0 x h_x_ne_zero)
  --       simp only [Units.val_mk0, zpow_neg, norm_mul,
  --       norm_inv, norm_p_zpow, inv_inv] at this
  --       rw[mul_eq_one_iff_inv_eq₀] at this
  --       · exact Real.ext_cauchy (congrArg Real.cauchy (id (Eq.symm this)))
  --       · simp only [ne_eq, norm_eq_zero]
  --         exact h_x_ne_zero
  --     rw [hxinvval]
  --     rw [mul_inv_le_iff₀]
  --     · simp only [one_mul]
  --       exact h_x_max.1
  --     · simp only [norm_pos_iff, ne_eq]
  --       exact h_x_ne_zero
  --   have hz' : ‖z'‖ ≤ 1 := by
  --     unfold z'
  --     simp only [zpow_neg, norm_mul, norm_inv, norm_p_zpow, inv_inv]
  --     have hxinvval : ↑p ^ x.valuation = ‖x‖⁻¹ := by
  --       have := norm_mul_pow_neg_valuation_eq_one (Units.mk0 x h_x_ne_zero)
  --       simp only [Units.val_mk0, zpow_neg, norm_mul,
  --       norm_inv, norm_p_zpow, inv_inv] at this
  --       rw [mul_eq_one_iff_inv_eq₀] at this
  --       · exact Real.ext_cauchy (congrArg Real.cauchy (id (Eq.symm this)))
  --       · simp only [ne_eq, norm_eq_zero]
  --         exact h_x_ne_zero
  --     rw [hxinvval]
  --     rw [mul_inv_le_iff₀]
  --     · simp only [one_mul]
  --       exact h_x_max.2
  --     · simp only [norm_pos_iff, ne_eq]
  --       exact h_x_ne_zero
  --   have hnewsol : ((z' : ℚ_[p])^2 - p * (x' : ℚ_[p])^2
  --     - v * (y' : ℚ_[p])^2 = 0) := by
  --     unfold x' y' z'
  --     grind
  --   let z'' : ℤ_[p] := ⟨z',hz'⟩
  --   let y'' : ℤ_[p] := ⟨y',hy'⟩
  --   let x'' : ℤ_[p] := ⟨x',hx'⟩
  --   use z'', y'', x''
  --   constructor
  --   · exact hnewsol
  --   · right
  --     right
  --     exact PadicInt.isUnit_iff.mpr hx'unit

--better name?
/-- If `p` is a prime, `x, y, z in ℚ_[p]` satisfy `z ^ 2 - p * x ^ 2 - v * y ^ 2`, with `v` nonzero,
and not all of `x, y, z` are zero, then there exists a nontrivial solution to the same equation with
`z', y'` units in `ℤ_[p]ˣ` and `x'` in `ℤ_[p]`. -/
lemma exists_nontrivial_zero {v : (ℚ_[p])ˣ} {x y z : ℚ_[p]}
    (hnontriv : (x, y, z) ≠ (0, 0, 0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) :
    ∃ z' y' : ℤ_[p]ˣ, ∃ x' : ℤ_[p],
      (z' : ℚ_[p]) ^ 2 - p * (x' : ℚ_[p]) ^ 2 - v * (y' : ℚ_[p]) ^ 2 = 0 := by
  obtain ⟨z', y', x', hnewsol, hunits⟩ := exists_padicInt_solution hnontriv hsol
  have heq_int : ‖(z' : ℚ_[p]) ^ 2 - p * (x' : ℚ_[p]) ^ 2
     - v * (y' : ℚ_[p]) ^ 2‖ ≤ 1 := by
     rw [hnewsol]
     simp only [norm_zero, zero_le_one]
  have hz'_unit : ‖z'‖ = 1 := by
    rw [← PadicInt.norm_natCast_zmodRepr_eq_one_iff,
    PadicInt.norm_natCast_zmodRepr_eq_one_iff_ne]
    by_contra
    have hy'_zmodRep_eq_ze : y'.zmodRepr = 0 := by
      rw [PadicInt.zmodRepr_eq_zero_iff_dvd] at this ⊢
      refine (PadicInt.norm_lt_one_iff_dvd y').mp ?_
      by_cases (y = 0)
      · expose_names
        sorry
      · sorry
    have hx'_zmodRep_eq_ze : x'.zmodRepr = 0 := by
      sorry
    have hz'_not_unit : ¬IsUnit z' := by
      refine PadicInt.not_isUnit_iff.mpr ?_
      rw [← sub_zero z', ← CharP.cast_eq_zero, ← this]
      exact PadicInt.norm_sub_zmodRepr_lt_one z'
    have hy'_not_unit : ¬IsUnit y' := by
      refine PadicInt.not_isUnit_iff.mpr ?_
      rw [← sub_zero y', ← CharP.cast_eq_zero, ← hy'_zmodRep_eq_ze]
      exact PadicInt.norm_sub_zmodRepr_lt_one y'
    have hx'_not_unit : ¬IsUnit x' := by
      refine PadicInt.not_isUnit_iff.mpr ?_
      rw [← sub_zero x', ← CharP.cast_eq_zero, ← hx'_zmodRep_eq_ze]
      exact PadicInt.norm_sub_zmodRepr_lt_one x'
    have hnounits : ¬(IsUnit z' ∨ IsUnit y' ∨ IsUnit x') := by
      simp only [not_or]
      constructor
      · exact hz'_not_unit
      · constructor
        · exact hy'_not_unit
        · exact hx'_not_unit
    contradiction
  have hy'_unit : ‖y'‖ = 1 := by
    -- pretty much the same as hz'_unit
    sorry
  let z'' : ℤ_[p]ˣ := PadicInt.mkUnits hz'_unit
  let y'' : ℤ_[p]ˣ := PadicInt.mkUnits hy'_unit
  let x'' : ℤ_[p] := x'
  use z'', y'', x''
  apply hnewsol


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
