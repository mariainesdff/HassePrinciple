/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import HassePrinciple.ForMathlib.Topology.Algebra.Group.Units

/-! # Approximation theorem. -/

@[expose] public section

noncomputable section

namespace Rat

local instance (p : Nat.Primes) : Fact (Nat.Prime p) :=
  fact_iff.mpr p.2

open Padic ContinuousMulEquiv

/-- Given a finite set of places and a point in the product of the completions of ℚ at those places,
there exists a rational number that is arbitrarily close to the given point at all those places. -/
theorem approximation' {S : Finset Nat.Primes} {ε : ℝ} (hε : ε > 0)
    (y : ℝ × (Π p : S, ℚ_[p])) :
    ∃ x : ℚ, ‖y.1 - x‖ + Finset.sum (Finset.attach S) (fun n ↦ ‖y.2 n - x‖) < ε := by
  sorry

/-- The finite embedding of ℚ into the product of the completions of ℚ at a finite set of places
(which includes ℝ). -/
abbrev finiteEmbedding (S : Finset Nat.Primes) : ℚ →+* ℝ × (Π p : S, ℚ_[p]) where
  toFun x   := ⟨algebraMap ℚ ℝ x, fun p ↦ (algebraMap ℚ ℚ_[p]) x⟩
  map_one'  := by aesop
  map_mul'  := by aesop
  map_zero' := by aesop
  map_add'  := by aesop

/-- The approximation theorem can be restated as saying that the finite embedding is dense. -/
theorem approximation (S : Finset Nat.Primes) :
    Dense (Set.range (finiteEmbedding S)) := by
  sorry

local instance : IsOpenUnits ℝ := instIsOpenUnitsOfContinuousInv₀OfT1Space
local instance (S : Finset Nat.Primes) : IsOpenUnits ((p : ↥S) → ℚ_[p]) := pi_units_isOpenUnits
local instance (S : Finset Nat.Primes) : IsOpenUnits (ℝ × ((p : ↥S) → ℚ_[p])) :=
  prod_units_isOpenUnits

theorem approximation_units (S : Finset Nat.Primes) :
    Dense (Set.range (Units.map (finiteEmbedding S).toMonoidHom)) := by
  have : IsOpenUnits (ℝ × ((p : ↥S) → ℚ_[p])) := by infer_instance
  rw [isOpenUnits_iff] at this
  have hd := approximation S
  simp only [Dense, RingHom.coe_mk, eq_ratCast, MonoidHom.coe_mk, OneHom.coe_mk,
    mem_closure_iff_nhds] at hd ⊢
  refine fun x N hN ↦ ?_
  obtain ⟨y, ⟨u, huN, hur⟩, ⟨r, rfl⟩⟩ :=
    hd x (Units.val '' N) ((Topology.IsOpenEmbedding.image_mem_nhds (this)).mpr hN)
  refine ⟨u, ⟨huN, ?_⟩⟩
  use Units.mk0 r (fun h0 ↦ by simp only [h0, cast_zero] at hur; exact Units.ne_zero u hur)
  simp [← Units.val_inj, hur]

end Rat
