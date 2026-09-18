/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.IsOpenUnits

/-! # Approximation theorem. -/

@[expose] public section

noncomputable section

namespace Rat

local instance (p : Nat.Primes) : Fact (Nat.Prime p) :=
  fact_iff.mpr p.2

open Padic

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

open Topology

def ContinuousMulEquiv.prodUnits (M N : Type*) [Monoid M] [TopologicalSpace M]
    [Monoid N] [TopologicalSpace N] :
    (M × N)ˣ ≃ₜ* Mˣ × Nˣ where
  __ := MulEquiv.prodUnits
  continuous_toFun := Continuous.prodMk (Units.continuous_map continuous_fst)
    (Units.continuous_map continuous_snd)
  continuous_invFun := Units.continuous_iff.mpr
    ⟨continuous_prodMk.mpr ⟨Units.continuous_val.comp continuous_fst,
        Units.continuous_val.comp continuous_snd⟩,
      continuous_prodMk.mpr ⟨Units.continuous_coe_inv.comp continuous_fst,
        Units.continuous_coe_inv.comp continuous_snd⟩⟩

theorem ContinuousMulEquiv.prodUnits_isOpenEmbedding {M N : Type*} [Monoid M] [TopologicalSpace M]
    [Monoid N] [TopologicalSpace N] :
    IsOpenEmbedding (ContinuousMulEquiv.prodUnits M N) := by
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap
    (map_continuous (ContinuousMulEquiv.prodUnits M N))
    (ContinuousMulEquiv.prodUnits M N).injective
    (ContinuousMulEquiv.prodUnits M N).toHomeomorph.isOpenMap

instance (M N : Type*) [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [hM : IsOpenUnits M]
    [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [hN : IsOpenUnits N] :
    IsOpenUnits (M × N) := by
  rw [isOpenUnits_iff] at *
  exact (Topology.IsOpenEmbedding.of_comp_iff _ (hM.prodMap hN)).mpr
    ContinuousMulEquiv.prodUnits_isOpenEmbedding

theorem approximation_units (S : Finset Nat.Primes) :
    Dense (Set.range (Units.map (finiteEmbedding S).toMonoidHom)) := by
  have : IsOpenUnits (ℝ × ((p : ↥S) → ℚ_[p])) := by
    sorry
  rw [isOpenUnits_iff] at this
  have hd := approximation S
  simp only [Dense, RingHom.coe_mk, eq_ratCast, MonoidHom.coe_mk, OneHom.coe_mk] at *
  intro x
  simp only [mem_closure_iff_nhds] at hd ⊢
  intro N hN
  let N' := Units.val '' N
  have hN' : N' ∈ nhds x.val := (Topology.IsOpenEmbedding.image_mem_nhds this).mpr hN
  specialize hd x N' hN'
  obtain ⟨y, hyN', ⟨r, rfl⟩⟩ := hd
  simp only [N', Set.mem_image] at hyN'
  obtain ⟨u, huN, hur⟩ := hyN'
  use u, huN
  have hr0 : r ≠ 0 := by
    intro h0
    simp only [h0, cast_zero] at hur
    exact Units.ne_zero u hur
  use Units.mk0 r hr0
  simp [← Units.val_inj, hur]

end Rat




/-The code needs to be cleaned up (golf, organize namespaces, move general lemmas to right file, etc), but I will leave this to you. To fill in the sorry in approximation_units, you will also need a general product version of the IsOpenUnits instance. I think this should follow similarly to the prod case (and note that Mathlib already contains ContinuousMulEquiv.piUnits ).-/
