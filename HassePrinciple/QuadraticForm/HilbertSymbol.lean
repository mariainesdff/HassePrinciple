/-
Copyright (c) 2026b Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

import Mathlib
public import HassePrinciple.QuadraticForm.Basic


open Classical


noncomputable section

namespace HilbertSymbol

-- k is a field and typically will be either ℝ or ℚ_p, but we need less for the definition.
variable {k : Type*} [Field k] [CharZero k]

noncomputable def a_b_quadratic_form (a b : kˣ) : QuadraticForm k (Fin (Nat.succ 0).succ.succ → k):= QuadraticMap.weightedSumSquares k ![1, -a, -b]

noncomputable def HilbertSymbol (a b : kˣ) : ℤˣ :=
  if (a_b_quadratic_form a b).Isotropic then 1 else -1

lemma HilbertSymbol_well_defined_up_to_squares (a b a' b' : kˣ) (ha : a' = a * (a' / a) ^ 2) (hb : b' = b * (b' / b) ^ 2) :
    HilbertSymbol a b = HilbertSymbol (a * a' ^ 2) (b * b' ^ 2)  := by
  sorry

def kb (b : kˣ) := QuadraticAlgebra k b 0

--may make sense to split in two lemmas, one for kb=k and the other for kb≠k.
theorem HilbertSymbol_eq_one_iff (a b : kˣ) : HilbertSymbol a b = 1 ↔ ∃ t : kb b, a =
  QuadraticAlgebra.norm t  := by
  sorry

theorem HilbertSymbol_symmetric (a b : kˣ) : HilbertSymbol a b = HilbertSymbol b a := by
  sorry

theorem HilbertSymbol_one_of_square (a c : kˣ) : HilbertSymbol a c ^ 2 = 1 := by
  sorry

theorem HilbertSymbol_one_of_neg_self (a : kˣ) : HilbertSymbol a (-a) = 1 := by
  sorry

theorem HilbertSymbol_one_of_one_minus_self (a : kˣ) (h : (1 : k) - a ≠ 0) :
  HilbertSymbol a (Units.mk0 ((1 : k) - a) h) = 1 := by
  sorry

theorem HilbertSymbol_of_mult (a a' b : kˣ) : HilbertSymbol a b = 1 → HilbertSymbol (a * a') b =
  HilbertSymbol a' b := by
  sorry

theorem HilbertSymbol_simplification_rule (a b : kˣ) : HilbertSymbol a b = HilbertSymbol a (- a * b)
  := by
  sorry

theorem HilbertSymbol_simplification_rule' (a b : kˣ) (h : (1 : k) - a ≠ 0) : HilbertSymbol a b =
  HilbertSymbol a ((Units.mk0 ((1 : k) - a) h) * b) := by
  sorry

theorem HilbertSymbol_real (a b : ℝˣ) : HilbertSymbol a b = if (0 : ℝ) < a ∨ (0 : ℝ) < b then 1
  else -1 := by
  sorry
/-
epsilon(u) is the class modulo 2 of (u-1)/2. omega(u) is the class modulo 2 of (u^2-1)/8.
-/
def epsilon (u : (PadicInt 2)ˣ) : ZMod 2 :=
  if (u : ℤ_[2]).appr 2 % 4 = 1 then 0 else 1

def omega (u : (PadicInt 2)ˣ) : ZMod 2 :=
  let u_mod_8 := (u : ℤ_[2]).appr 3 % 8
  if u_mod_8 = 1 ∨ u_mod_8 = 7 then 0 else 1

theorem HilbertSymbol_padic_odd_p (p : ℕ) [Fact (p.Prime)] (hp : p ≠ 2) (a b : ℚ_[p]ˣ) :
HilbertSymbol a b = sorry := by
  sorry



end HilbertSymbol
