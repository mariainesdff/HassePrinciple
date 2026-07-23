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

variable {a b : ℤ_[p]}
namespace legendreSym

/-- The Padic Legendre symbol agrees with the classical Legendre symbol on ℤ. -/
lemma intCast (z : ℤ) : legendreSym (z : ℤ_[p]) = _root_.legendreSym p z := by
  simp [legendreSym, _root_.legendreSym, quadraticCharFun]

/-- We have the congruence `legendreSym a ≡ a ^ (p / 2) mod p`. -/
theorem eq_pow : (legendreSym a : ZMod p) = (a.toZMod) ^ (p / 2) := by
  calc (legendreSym a : ZMod p)
    _ = (legendreSym (a.zmodRepr : ℤ_[p]) : ZMod p) := by
      simp [legendreSym, (ZMod.intCast_eq_intCast_iff' (quadraticCharFun (ZMod p) (toZMod a))
        (quadraticCharFun (ZMod p) a.zmodRepr) p).mpr rfl]
    _ = _root_.legendreSym p (a.zmodRepr) := by simp [legendreSym, _root_.legendreSym]
    _ = (a.zmodRepr) ^ (p / 2) := by simp [_root_.legendreSym.eq_pow]
    _ = (a.toZMod) ^ (p / 2) := ZMod.valMinAbs_inj.mp rfl

/-- If `a` is a p-adic unit, then `legendreSym a` is `1` or `-1`. -/
theorem eq_one_or_neg_one (ha : IsUnit a) : legendreSym a = 1 ∨ legendreSym a = -1 :=
  Int.isUnit_eq_one_or (IsUnit.map ((quadraticChar (ZMod p)).compMonoidHom toZMod) ha)

/-- If a is a p-adic unit, then `legendreSym a = -1` iff `legendreSym a ≠ 1`. -/
theorem eq_neg_one_iff_not_one (ha : IsUnit a) :
    legendreSym a = -1 ↔ ¬legendreSym a = 1 := by
  have := eq_one_or_neg_one ha
  lia

/-- The Legendre symbol of `p` and `a` is zero iff `p ∣ a`. -/
theorem eq_zero_iff : legendreSym a = 0 ↔ ¬ IsUnit a :=
  ⟨fun _ h ↦ by have := eq_one_or_neg_one h; lia, fun h ↦ by rw [MulChar.map_nonunit
  legendreSym h]⟩

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
  rw [legendreSym, MulChar.compMonoidHom_apply, quadraticChar_one_iff_isSquare]
  rw [← ZMod.val_ne_zero (toZMod a), val_toZMod_eq_zmodRepr, ← norm_natCast_zmodRepr_eq_one_iff_ne,
    norm_natCast_zmodRepr_eq_one_iff.mpr (isUnit_iff.mp ha)]

/-- `legendreSym p a = -1` iff `a` is a nonsquare mod `p`. -/
theorem eq_neg_one_iff (ha : IsUnit a) :
    legendreSym a = -1 ↔ ¬ IsSquare (a.toZMod) := by
  rw [eq_neg_one_iff_not_one ha, eq_one_iff ha]

end legendreSym

end PadicInt
