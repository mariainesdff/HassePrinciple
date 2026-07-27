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

/-- helper lemma: if `x,y ∈ ℚ_[p]` and `‖y‖ ≤ ‖x‖,` then `‖y *  p ^ (-x.valuation)‖ ≤ 1` -/
lemma mul_by_max_norm_is_int {x y : ℚ_[p]} (h_x_max : ‖y‖ ≤ ‖x‖) (x_ne_ze : x ≠ 0) :
    ‖y *  p ^ (-x.valuation)‖ ≤ 1 := by
    have x_inv_val : ↑p ^ x.valuation = ‖x‖⁻¹ := by
      have := norm_mul_pow_neg_valuation_eq_one (Units.mk0 x x_ne_ze)
      simp only [Units.val_mk0, zpow_neg, norm_mul,
        norm_inv, norm_p_zpow, inv_inv] at this
      rw[mul_eq_one_iff_inv_eq₀] at this
      · exact Real.ext_cauchy (congrArg Real.cauchy (id (Eq.symm this)))
      · simp only [ne_eq, norm_eq_zero]
        exact x_ne_ze
    simp only [zpow_neg, norm_mul, norm_inv, norm_p_zpow, inv_inv]
    rw [x_inv_val, mul_inv_le_iff₀]
    · simp only [one_mul]
      exact h_x_max
    · simp only [norm_pos_iff]
      exact x_ne_ze

/-- helper lemma: if `x,y,z ∈ ℚ_[p]`, `‖y‖ ≤ ‖x‖ ∧ ‖z‖ ≤ ‖x‖,` and `(x,y,z) ≠ (0,0,0),` then
`x ≠ 0`-/
lemma norm_max_ne_ze {x y z : ℚ_[p]} (h_x_max : ‖y‖ ≤ ‖x‖ ∧ ‖z‖ ≤ ‖x‖)
(hnontriv : (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)) : x ≠ 0 := by
  by_contra
  have normx_eq_ze : ‖x‖ = 0 := by
    exact norm_eq_zero.mpr this
  rw [normx_eq_ze] at h_x_max
  obtain ⟨maxy, maxz⟩ := h_x_max
  have y_eq_ze : y = 0 := by
    rw [norm_le_zero_iff] at maxy
    exact maxy
  have z_eq_ze : z = 0 := by
    rw [norm_le_zero_iff] at maxz
    exact maxz
  have htriv : ¬(x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) := by
    simp only [ne_eq, not_or, not_not]
    constructor
    · exact this
    · constructor
      · exact y_eq_ze
      · exact z_eq_ze
  contradiction


/-- helper lemma: if `p` is a prime and `x ∈ ℚ_[p]` is nonzero, then
`‖x * p ^ (-x.valuation)‖ = 1` -/
lemma x_mul_p_to_neg_val {x : ℚ_[p]} (x_ne_ze : x ≠ 0) : ‖x * p ^ (-x.valuation)‖ = 1 := by
  simp only [zpow_neg, norm_mul, norm_inv, norm_p_zpow, inv_inv]
  rw [norm_eq_zpow_neg_valuation (x_ne_ze)]
  apply zpow_neg_mul_zpow_self x.valuation (NeZero.out)

/-- helper lemma:  if `x, y, z ∈ ℚ_[p]` and `(‖x‖ < ‖y‖ ∨ ‖x‖ < ‖z‖) ∧ ‖z‖ ≤ ‖y‖,` then
`‖x‖ ≤ ‖y‖ ∧ ‖z‖ ≤ ‖y‖.`-/
lemma max_norm {x y z : ℚ_[p]} (hx_notmax : (‖x‖ < ‖y‖ ∨ ‖x‖ < ‖z‖)) (hy_max : ‖z‖ ≤ ‖y‖) :
  ‖x‖ ≤ ‖y‖ ∧ ‖z‖ ≤ ‖y‖ := by
  have norm_y_ge_norm_x : ‖x‖ ≤ ‖y‖ := by
    by_contra
    simp only [not_le] at this
    have h_z_min : ‖z‖ < ‖x‖ := by
      exact Std.lt_of_le_of_lt hy_max this
    have hnot : ¬(‖x‖ < ‖y‖ ∨ ‖x‖ < ‖z‖) := by
      simp only [not_or, not_lt]
      constructor
      · exact Std.le_of_lt this
      · exact Std.le_of_lt h_z_min
    contradiction
  constructor
  · exact norm_y_ge_norm_x
  · exact hy_max

/-- If `p` is a prime, `x, y, z ∈ ℚ_[p]` satisfy `z ^ 2 - p * x ^ 2 - v * y ^ 2`, with `v in`
`ℤ_[p]ˣ`, and not all of `x, y, z` are zero, then there exists a nontrivial solution to the same
equation with `z', y',x' ∈ ℤ_[p]`, and at least one is a unit -/
lemma exists_padicInt_sol {v : ℤ_[p]ˣ} {x y z : ℚ_[p]}
    (hnontriv : (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) :
    ∃ z' y' x' : ℤ_[p],
      z' ^ 2 - p * x' ^ 2 - v * y' ^ 2 = 0
      ∧ (IsUnit z' ∨ IsUnit y' ∨ IsUnit x') := by
      by_cases (‖y‖ ≤ ‖x‖ ∧ ‖z‖ ≤ ‖x‖)
      · expose_names
        let x' := x * p ^ (-x.valuation)
        let y' := y * p ^ (-x.valuation)
        let z' := z * p ^(-x.valuation)
        have x'_unit : ‖x'‖ = 1 := by
          unfold x'
          exact x_mul_p_to_neg_val (by apply norm_max_ne_ze (h) (hnontriv))
        have y'_int : ‖y'‖ ≤ 1 := by
          unfold y'
          exact mul_by_max_norm_is_int (h.left) (by apply norm_max_ne_ze (h) (hnontriv))
        have z'_int : ‖z'‖ ≤ 1 := by
          unfold z'
          exact mul_by_max_norm_is_int (h.right) (by apply norm_max_ne_ze (h) (hnontriv))
        let z'' : ℤ_[p] := ⟨z',z'_int⟩
        let y'' : ℤ_[p] := ⟨y',y'_int⟩
        let x'' : ℤ_[p] := ⟨x', (by exact Std.le_of_eq x'_unit)⟩
        use z'', y'', x''
        constructor
        · unfold z'' y'' x''
          refine PadicInt.coe_eq_zero.mp ?_
          have hnewsol : ((z' : ℚ_[p]) ^ 2 - p * (x' : ℚ_[p]) ^ 2
            - v * (y' : ℚ_[p])^2 = 0) := by
            unfold x' y' z'
            grind
          exact hnewsol
        · right
          right
          exact PadicInt.isUnit_iff.mpr x'_unit
      · expose_names
        simp only [not_and_or, not_le] at h
        by_cases (‖z‖ ≤ ‖y‖)
        · expose_names
          rw [or_left_comm] at hnontriv
          let x' := x * p ^ (-y.valuation)
          let y' := y * p ^ (-y.valuation)
          let z' := z * p ^(-y.valuation)
          have y'_unit : ‖y'‖ = 1 := by
            unfold y'
            exact x_mul_p_to_neg_val
              (by apply norm_max_ne_ze (by exact max_norm (h) (h_1)) (hnontriv))
          have x'_int : ‖x'‖ ≤ 1 := by
            unfold x'
            exact mul_by_max_norm_is_int (by exact (max_norm (h) (h_1)).left)
              (by apply norm_max_ne_ze (by exact max_norm (h) (h_1)) (hnontriv))
          have z'_int : ‖z'‖ ≤ 1 := by
            unfold z'
            exact mul_by_max_norm_is_int (by exact (max_norm (h) (h_1)).right)
             (by apply norm_max_ne_ze (by exact max_norm (h) (h_1)) (hnontriv))
          let z'' : ℤ_[p] := ⟨z',z'_int⟩
          let y'' : ℤ_[p] := ⟨y',(by exact Std.le_of_eq y'_unit)⟩
          let x'' : ℤ_[p] := ⟨x', x'_int⟩
          use z'', y'', x''
          constructor
          · unfold z'' y'' x''
            refine PadicInt.coe_eq_zero.mp ?_
            have hnewsol : ((z' : ℚ_[p])^2 - p * (x' : ℚ_[p])^2
              - v * (y' : ℚ_[p])^2 = 0) := by
              unfold x' y' z'
              grind
            exact hnewsol
          · right
            left
            exact PadicInt.isUnit_iff.mpr y'_unit
        · expose_names
          simp only [not_le] at h_1
          rw [or_comm] at h
          rw [← or_assoc, or_right_comm, or_assoc, or_left_comm] at hnontriv
          let x' := x * p ^ (-z.valuation)
          let y' := y * p ^ (-z.valuation)
          let z' := z * p ^(-z.valuation)
          have z'_unit : ‖z'‖ = 1 := by
            unfold z'
            exact x_mul_p_to_neg_val
              (by apply norm_max_ne_ze (by exact max_norm (h) (by exact le_of_lt (h_1))) (hnontriv))
          have x'_int : ‖x'‖ ≤ 1 := by
            unfold x'
            exact mul_by_max_norm_is_int (by exact (max_norm (h) (by exact le_of_lt (h_1))).left)
              (by apply norm_max_ne_ze (by exact max_norm (h) (by exact le_of_lt (h_1))) (hnontriv))
          have y'_int : ‖y'‖ ≤ 1 := by
            unfold y'
            exact mul_by_max_norm_is_int (by exact (max_norm (h) (by exact le_of_lt (h_1))).right)
              (by apply norm_max_ne_ze (by exact max_norm (h) (by exact le_of_lt (h_1))) (hnontriv))
          let z'' : ℤ_[p] := ⟨z',(by exact Std.le_of_eq z'_unit)⟩
          let y'' : ℤ_[p] := ⟨y', y'_int⟩
          let x'' : ℤ_[p] := ⟨x', x'_int⟩
          use z'', y'', x''
          constructor
          · unfold z'' y'' x''
            refine PadicInt.coe_eq_zero.mp ?_
            have hnewsol : ((z' : ℚ_[p])^2 - p * (x' : ℚ_[p])^2
              - v * (y' : ℚ_[p])^2 = 0) := by
              unfold x' y' z'
              grind
            exact hnewsol
          · left
            exact PadicInt.isUnit_iff.mpr z'_unit


/-- If `p` is a prime, `x, y, z in ℚ_[p]` satisfy `z ^ 2 - p * x ^ 2 - v * y ^ 2`, with `v` nonzero,
and not all of `x, y, z` are zero, then there exists a nontrivial solution to the same equation with
`z', y'` units in `ℤ_[p]ˣ` and `x'` in `ℤ_[p]`. -/
lemma exists_nontrivial_units_zero {v : (ℤ_[p])ˣ} {x y z : ℚ_[p]}
    (hnontriv : (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) :
    ∃ z' y' : ℤ_[p]ˣ, ∃ x' : ℤ_[p],
      (z' : ℤ_[p]) ^ 2 - p * (x') ^ 2 - v * (y' : ℤ_[p]) ^ 2 = 0 := by
  obtain ⟨z', y', x', hnewsol, hunits⟩ := exists_padicInt_sol hnontriv hsol
  have hz'_unit : IsUnit z' := by
    by_contra
    rw [PadicInt.not_isUnit_iff, PadicInt.norm_lt_one_iff_dvd, dvd_def] at this
    obtain ⟨c, hc⟩ := this
    have hy'_norm_ne_one : ‖y'‖ < 1 := by
      rw [sub_eq_zero] at hnewsol
      have vy'_sq_norm_ne_one : ‖(v) * (y' : ℤ_[p]) ^ 2‖ < 1 := by
        rw [← hnewsol, hc, PadicInt.norm_lt_one_iff_dvd]
        use (↑p * c ^ 2 - x' ^ 2)
        ring
      simp only [norm_mul, norm_pow, PadicInt.norm_units, one_mul, sq_lt_one_iff_abs_lt_one,
        abs_norm] at vy'_sq_norm_ne_one
      exact vy'_sq_norm_ne_one
    have hx'_norm_ne_one : ‖x'‖ < 1 := by
      rw [PadicInt.norm_lt_one_iff_dvd]
      have vx'_sq_eq : (z' : ℤ_[p]) ^ 2 - v * (y' : ℤ_[p]) ^ 2 = ↑p * (x') ^ 2 := by
        rw [sub_right_comm, sub_eq_zero] at hnewsol
        exact hnewsol
      have  px'_div_p2 : (p : ℤ_[p]) ^ 2 ∣ (p : ℤ_[p]) * (x') ^ 2 := by
        rw [← vx'_sq_eq]
        rw [PadicInt.norm_lt_one_iff_dvd,dvd_def] at hy'_norm_ne_one
        obtain ⟨c', hc'⟩ := hy'_norm_ne_one
        rw [hc, hc']
        have hsimp' : (↑p * c) ^ 2 - ↑v * (↑p * c') ^ 2 = ↑p ^ 2 * (c ^ 2 - ↑v * c' ^ 2) := by
          ring
        rw [hsimp', dvd_def]
        use (c ^ 2 - ↑v * c' ^ 2)
      have hpx'sq : ↑p ∣ x' ^ 2 := by
        rw [dvd_def]
        obtain ⟨d,hd⟩ := px'_div_p2
        use d
        have p_ne_zediv : (p : ℤ_[p]) ∈ nonZeroDivisors ℤ_[p] := by
          refine mem_nonZeroDivisors_of_ne_zero
            (by apply Nat.cast_ne_zero.mpr (Ne.symm (NeZero.ne' p)))
        nth_rw 2 [pow_two] at hd
        rw [← mul_cancel_left_mem_nonZeroDivisors (p_ne_zediv), ← mul_assoc]
        exact hd
      rw [Prime.dvd_pow_iff_dvd (PadicInt.prime_p) (Ne.symm (Nat.zero_ne_add_one 1))] at hpx'sq
      exact hpx'sq
    have h_not_units : ¬(IsUnit z' ∨ IsUnit y' ∨ IsUnit x') := by
      simp only [not_or]
      constructor
      · rw [PadicInt.not_isUnit_iff, PadicInt.norm_lt_one_iff_dvd, dvd_def]
        use c
      · constructor
        · rw [← PadicInt.not_isUnit_iff] at hy'_norm_ne_one
          exact hy'_norm_ne_one
        · rw [← PadicInt.not_isUnit_iff] at hx'_norm_ne_one
          exact hx'_norm_ne_one
    contradiction
  have hy'_unit : IsUnit y' := by
    by_contra
    rw [PadicInt.not_isUnit_iff, PadicInt.norm_lt_one_iff_dvd, dvd_def] at this
    obtain ⟨c, hc⟩ := this
    have hz'_norm_ne_one : ‖z'‖ < 1 := by
      have z'_sq_eq : (z' : ℤ_[p]) ^ 2 = p * (x') ^ 2 + (v) * (y' : ℤ_[p]) ^ 2 := by
        rw [sub_eq_zero] at hnewsol
        rw [← hnewsol]
        ring
      have z'_sq_norm_ne_one : ‖z' ^ 2‖ < 1 := by
        rw [z'_sq_eq, PadicInt.norm_lt_one_iff_dvd, dvd_def, hc]
        use (x' ^ 2 + ↑v * ↑p * c ^ 2)
        ring
      simp only [norm_pow, sq_lt_one_iff_abs_lt_one, abs_norm] at z'_sq_norm_ne_one
      exact z'_sq_norm_ne_one
    have hx'_norm_ne_one : ‖x'‖ < 1 := by
      rw [PadicInt.norm_lt_one_iff_dvd]
      have  px'_div_p2 : (p : ℤ_[p]) ^ 2 ∣ (p : ℤ_[p]) * (x') ^ 2 := by
        rw [sub_right_comm, sub_eq_zero] at hnewsol
        rw [← hnewsol]
        rw [PadicInt.norm_lt_one_iff_dvd,dvd_def] at hz'_norm_ne_one
        obtain ⟨c', hc'⟩ := hz'_norm_ne_one
        rw [hc, hc']
        have hsimp' : (↑p * c') ^ 2 - ↑v * (↑p * c) ^ 2 = ↑p ^ 2 * (c' ^ 2 - ↑v * c ^ 2) := by
          ring
        rw [hsimp', dvd_def]
        use (c' ^ 2 - ↑v * c ^ 2)
      have hpx'sq : ↑p ∣ x' ^ 2 := by
        rw [dvd_def]
        obtain ⟨d,hd⟩ := px'_div_p2
        use d
        have p_ne_zediv : (p : ℤ_[p]) ∈ nonZeroDivisors ℤ_[p] := by
          refine mem_nonZeroDivisors_of_ne_zero
            (by apply Nat.cast_ne_zero.mpr (Ne.symm (NeZero.ne' p)))
        nth_rw 2 [pow_two] at hd
        rw [← mul_cancel_left_mem_nonZeroDivisors (p_ne_zediv), ← mul_assoc]
        exact hd
      rw [Prime.dvd_pow_iff_dvd (PadicInt.prime_p) (Ne.symm (Nat.zero_ne_add_one 1))] at hpx'sq
      exact hpx'sq
    have h_not_units : ¬(IsUnit z' ∨ IsUnit y' ∨ IsUnit x') := by
      simp only [not_or]
      constructor
      · rw [← PadicInt.not_isUnit_iff] at hz'_norm_ne_one
        exact hz'_norm_ne_one
      · constructor
        · rw [PadicInt.not_isUnit_iff, PadicInt.norm_lt_one_iff_dvd, dvd_def]
          use c
        · rw [← PadicInt.not_isUnit_iff] at hx'_norm_ne_one
          exact hx'_norm_ne_one
    contradiction
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
