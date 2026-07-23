/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/

module

public import HassePrinciple.Padics.Lemmas
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Topology.Algebra.IsOpenUnits

/-! # Padic unit squares form an open subgroup. -/

@[expose] public section
namespace Padic

variable (p : ℕ) [Fact (Nat.Prime p)]

lemma isSquare_of_dist_one_lt_one {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≠ 2) {x : ℚ_[p]}
    (hx : dist x 1 < 1) : IsSquare x := by
  let z : ℤ_[p] := ⟨x - 1, hx.le⟩
  have : ‖x - 1‖ = ‖z‖ := by simp [z]
  rw [dist_eq_norm, ← zpow_zero (p : ℝ), norm_lt_pow_iff_norm_le_pow_sub_one, this, zero_sub,
    ← Nat.cast_one, PadicInt.norm_le_pow_iff_mem_span_pow, pow_one, Ideal.mem_span_singleton] at hx
  have hz1 : IsSquare (z + 1) := by
    have hz0 : PadicInt.toZMod z = 0 := by
      simp [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
        Ideal.mem_span_singleton, hx]
    exact (z + 1).isSquare_of_zmod hp (by simp [dvd_add_right hx, ← PadicInt.norm_lt_one_iff_dvd])
      (by simp [hz0])
  obtain ⟨r, hr⟩ := hz1
  exact ⟨r, by simp [← PadicInt.coe_mul, ← hr, z]⟩

lemma isSquare_of_dist_one_lt_pow {x : ℚ_[2]} (hx : dist x 1 < 2 ^ (-(2 : ℤ))) : IsSquare x := by
  have hx1 : ‖x - 1‖ ≤ 1 := le_trans hx.le (by norm_num)
  let z : ℤ_[2] := ⟨x - 1, hx1⟩
  have : ‖x - 1‖ = ‖z‖ := by simp [z]
  rw [dist_eq_norm, ← Nat.cast_two (R := ℝ), norm_lt_pow_iff_norm_le_pow_sub_one, this] at hx
  simp only [ Int.reduceSub, ← Nat.cast_three (R := ℤ), PadicInt.norm_le_pow_iff_mem_span_pow,
    Ideal.mem_span_singleton] at hx
  rw [Nat.cast_two] at hx
  have hz1 : IsSquare (z + 1) := by
    have hz0 : z.toZModPow 3 = 0 := by
      simp [-Nat.reducePow, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton, hx]
    refine (z + 1).isSquare_of_zmodPow ?_ (by simp [hz0])
    rw [dvd_add_right (dvd_trans (dvd_pow_self 2 three_ne_zero) hx), ← Nat.cast_two (R := ℤ_[2]),
      ← PadicInt.norm_lt_one_iff_dvd]
    simp
  obtain ⟨r, hr⟩ := hz1
  exact ⟨r, by simp [← PadicInt.coe_mul, ← hr, z]⟩

lemma exists_pow_isSquare_of_dist_one_lt (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ (n : ℕ), ∀ (x : ℚ_[p]), dist x 1 < p ^ (-(n : ℤ)) → IsSquare x := by
  by_cases hp : p = 2
  · subst hp
    exact ⟨2, fun x ↦ isSquare_of_dist_one_lt_pow⟩
  · exact ⟨0, fun x ↦ isSquare_of_dist_one_lt_one hp⟩

open Pointwise Set

lemma isOpen_squares_sdiff_zero : IsOpen ({x : ℚ_[p] | IsSquare x} \ {0}) := by
  rw [isOpen_iff_forall_mem_open]
  intro x ⟨hx, hx0⟩
  simp only [mem_setOf_eq, mem_singleton_iff] at hx hx0
  obtain ⟨n, hn⟩ := exists_pow_isSquare_of_dist_one_lt p
  refine ⟨x • (Metric.ball (1 : ℚ_[p]) (p ^ (-(n : ℤ)))), fun y hy ↦ ?_, by
    simp [smul_ball hx0, Metric.isOpen_ball], mem_smul_set.mpr ⟨1,
      Metric.mem_ball_self (zpow_pos (Nat.cast_pos.mpr (Nat.pos_of_neZero p)) _), by simp⟩⟩
  simp only [← image_smul, mem_image, Metric.mem_ball, mem_sdiff, mem_setOf_eq,
    mem_singleton_iff] at hy ⊢
  obtain ⟨u, hup, hu⟩ := hy
  simp only [← hu, smul_eq_mul, mul_eq_zero, not_or]
  refine ⟨hx.mul (hn u hup), hx0, ?_⟩
  by_contra h0
  simp only [h0, dist_zero, norm_one, ← zpow_zero (p : ℝ)] at hup
  rw [zpow_lt_zpow_iff_right₀ (Nat.one_lt_cast.mpr (Nat.Prime.one_lt Fact.out))] at hup
  simp [← not_le] at hup

-- Proven in section II.3.3.
/-- The open subgroup of `p`-adic unit squares inside `ℚ_[p]ˣ`. -/
def unitSquares : OpenSubgroup ℚ_[p]ˣ where
  carrier              := {x : ℚ_[p]ˣ | IsSquare x}
  mul_mem' {x y} hx hy := IsSquare.mul hx hy
  one_mem'             := by simp
  inv_mem' {x} hx      := IsSquare.inv hx
  isOpen'              := by
    have h : (Units.val '' {x : ℚ_[p]ˣ | IsSquare x}) = {x : ℚ_[p] | IsSquare x} \ {0} := by
      ext x
      simp only [mem_image, mem_setOf_eq, mem_sdiff, mem_singleton_iff]
      refine ⟨fun ⟨u, hu2, hux⟩ ↦ ?_, fun ⟨hxs, hx0⟩ ↦ ?_⟩
      · simp only [← hux, Units.ne_zero, not_false_eq_true, and_true]
        obtain ⟨v, hv⟩ := hu2
        exact ⟨v, by simp [hv]⟩
      · obtain ⟨r, hr⟩ := hxs
        exact ⟨Units.mk0 x hx0, ⟨Units.mk0 r (by aesop), by simp [hr]⟩, by simp⟩
    rw [IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_iff_image_isOpen, h]
    exact isOpen_squares_sdiff_zero p

end Padic
