/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.Padics.RingHoms

/-! # The Legendre Symbol for Padic Integers. -/

@[expose] public section

namespace MulChar

variable {M M' R F : Type*} [CommMonoid M] [CommMonoid M'] [CommMonoidWithZero R]
  [FunLike F M' M] [MonoidHomClass F M' M]

/-- We define the composition of monoid morphisms as the map composition. It is still a monoid
morphism. -/
@[simps]
def compMonoidHom (χ : MulChar M R) (f : F) [IsLocalHom f] : MulChar M' R where
  toFun m' := χ (f m')
  map_one' := by simp
  map_mul' := by simp
  map_nonunit' m' hm' := map_nonunit χ (isUnit_map_iff f m' |>.not.mpr hm')

end MulChar

namespace PadicInt

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The Legendre symbol of a p-adic integer is the quadratic character on ℤ_[p] precomposed with
the reduction modulo p. -/
noncomputable
def legendreSym : MulChar ℤ_[p] ℤ := (quadraticChar (ZMod p)).compMonoidHom toZMod
-- -- TODO: PR to Mathlib.NumberTheory.Padics.RingHoms
-- @[simp]
-- lemma zmodRepr_one : zmodRepr (1 : ℤ_[p]) = 1 := by
--   rw [← PadicInt.val_toZMod_eq_zmodRepr, map_one, ZMod.val_one p]

-- /-- The zmodRepr of a p-adic unit is nonzero modulo p. -/
-- lemma zmodRepr_coe_ne_zero_of_isUnit {a : ℤ_[p]} (ha : IsUnit a) :
--     ((a.zmodRepr : ℤ) : ZMod p) ≠ 0 := by
--   rw_mod_cast [ZMod.natCast_eq_zero_iff]
--   exact Nat.not_dvd_of_pos_of_lt
--     (Nat.ne_zero_iff_zero_lt.mp (PadicInt.zmodRepr_units_ne_zero ha.unit)) (zmodRepr_lt_p a)

-- /-- Let `a` be a p-adic integer. It is a unit if and only if its zmodRepr is nonzero modulo p. -/
-- lemma zmodRepr_coe_ne_zero_iff_isUnit {a : ℤ_[p]} :
--     IsUnit a ↔ ((a.zmodRepr : ℤ) : ZMod p) ≠ 0 := by
--   refine ⟨zmodRepr_coe_ne_zero_of_isUnit, fun h ↦ ?_⟩
--   rw [PadicInt.isUnit_iff, ← PadicInt.norm_natCast_zmodRepr_eq_one_iff,
--     PadicInt.norm_natCast_zmodRepr_eq_one_iff_ne]
--   aesop

-- /-- We define the Legendre symbol for a `p`-adic integer `a` as the Legendre symbol (at `p`) of its
-- reduction modulo `p`. -/
-- noncomputable def legendreSym (a : ℤ_[p]) : ℤ := _root_.legendreSym p a.zmodRepr

variable {a b : ℤ_[p]}
namespace legendreSym

-- lemma legendreSymMod (z : ℤ_[p]) : legendreSym (z) = legendreSym (z.zmodRepr : ℤ_[p]) := by
--   simp [legendreSym, _root_.legendreSym]

-- /-- The Padic Legendre symbol agrees with the classical Legendre symbol on ℕ. -/
-- lemma intCastNat (z : ℕ) : legendreSym (z : ℤ_[p]) = _root_.legendreSym p z := by sorry
-- --  simp [legendreSym, _root_.legendreSym, quadraticCharFun, zmodRepr_natCast]

/-- The Padic Legendre symbol agrees with the classical Legendre symbol on ℤ. -/
lemma intCast (z : ℤ) : legendreSym (z : ℤ_[p]) = _root_.legendreSym p z := by sorry
--  rw [legendreSym.mod, ← ZMod.val_intCast, legendreSymMod, ← val_toZMod_eq_zmodRepr, map_intCast,
--   intCastNat]

/-- We have the congruence `legendreSym a ≡ a ^ (p / 2) mod p`. -/
theorem eq_pow : (legendreSym a : ZMod p) = (a.toZMod) ^ (p / 2) := by sorry
--  rw [legendreSym, _root_.legendreSym.eq_pow, Int.cast_natCast]

/-- If `a` is a p-adic unit, then `legendreSym a` is `1` or `-1`. -/
theorem eq_one_or_neg_one (ha : IsUnit a) : legendreSym a = 1 ∨ legendreSym a = -1 := by sorry
  -- rw [legendreSym]
  -- exact _root_.legendreSym.eq_one_or_neg_one p (zmodRepr_coe_ne_zero_of_isUnit ha)

/-- If a is a p-adic unit, then `legendreSym a = -1` iff `legendreSym a ≠ 1`. -/
theorem eq_neg_one_iff_not_one (ha : IsUnit a) :
    legendreSym a = -1 ↔ ¬legendreSym a = 1 := by sorry
  -- rw [legendreSym]
  -- exact _root_.legendreSym.eq_neg_one_iff_not_one p (zmodRepr_coe_ne_zero_of_isUnit ha)

/-- The Legendre symbol of `p` and `a` is zero iff `p ∣ a`. -/
theorem eq_zero_iff : legendreSym a = 0 ↔ ¬ IsUnit a := by sorry
    -- rw [legendreSym, ← not_iff_not, not_not, _root_.legendreSym.eq_zero_iff,
    -- zmodRepr_coe_ne_zero_iff_isUnit]

-- /-- The Legendre symbol at zero is zero. -/
-- @[simp]
-- theorem at_zero : legendreSym (0 : ℤ_[p]) = 0 := by
--   simp [legendreSym]

-- /-- The Legendre symbol at 1 is 1. -/
-- @[simp]
-- theorem at_one : legendreSym (1 : ℤ_[p]) = 1 := by
--   simp [legendreSym]

-- /-- The Legendre symbol is multiplicative in `a` for `p` fixed. -/
-- protected theorem mul : legendreSym (a * b) = legendreSym a * legendreSym b := by
--   simp [legendreSym, map_mul]

/-- The Legendre symbol is a homomorphism of monoids with zero. -/
@[simps]
noncomputable def hom : ℤ_[p] →*₀ ℤ where
  toFun        := legendreSym
  map_zero'    := by simp [legendreSym]
  map_one'     := by simp [legendreSym]
  map_mul' _ _ := by simp [legendreSym, map_mul]

/-- The square of the symbol is 1 if `a` is a unit. -/
theorem sq_one (ha : IsUnit a) : legendreSym a ^ 2 = 1 := by
   cases eq_one_or_neg_one ha <;> aesop

/-- The Legendre symbol of `a^2` at `p` is 1 if `a` is a unit. -/
theorem sq_one' (ha : IsUnit a) : legendreSym (a ^ 2) = 1 := by
  rw [pow_two]
  cases eq_one_or_neg_one ha <;> aesop

/-- If `a` is a unit, then `legendreSym a = 1` iff `a` is a square mod `p`. -/
theorem eq_one_iff (ha : IsUnit a) : legendreSym a = 1 ↔ IsSquare (a.toZMod) := by
  sorry
  -- rw [legendreSym, _root_.legendreSym.eq_one_iff]
  -- exact zmodRepr_coe_ne_zero_of_isUnit ha

/-- `legendreSym p a = -1` iff `a` is a nonsquare mod `p`. -/
theorem eq_neg_one_iff (ha : IsUnit a) :
    legendreSym a = -1 ↔ ¬ IsSquare (a.toZMod) := by
  rw [eq_neg_one_iff_not_one ha, eq_one_iff ha]

end legendreSym

end PadicInt
