/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Topology.Algebra.IsOpenUnits

@[expose] public section

open Topology ContinuousMulEquiv

namespace ContinuousMulEquiv

def prodUnits (M N : Type*) [Monoid M] [TopologicalSpace M]
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

theorem prodUnits_isOpenEmbedding {M N : Type*} [Monoid M] [TopologicalSpace M]
    [Monoid N] [TopologicalSpace N] :
    IsOpenEmbedding (prodUnits M N) := by
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap
    (map_continuous (prodUnits M N))
    (prodUnits M N).injective
    (prodUnits M N).toHomeomorph.isOpenMap

instance (M N : Type*) [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [hM : IsOpenUnits M]
    [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [hN : IsOpenUnits N] :
    IsOpenUnits (M × N) := by
  rw [isOpenUnits_iff] at *
  exact (Topology.IsOpenEmbedding.of_comp_iff _ (hM.prodMap hN)).mpr
    prodUnits_isOpenEmbedding

theorem piUnits_isOpenEmbedding {I : Type*} {f : I → Type _}
    [(i : I) → Monoid (f i)] [(i : I) → TopologicalSpace (f i)] :
    IsOpenEmbedding (piUnits (M := f)) := by
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    (map_continuous piUnits)
    (ContinuousMulEquiv.injective piUnits)
    (piUnits (M := f)).toHomeomorph.isOpenMap

instance {I : Type*} [Finite I] {f : I → Type _} [(i : I) → Monoid (f i)]
    [(i : I) → TopologicalSpace (f i)] [(i : I) → IsOpenUnits (f i)] :
      IsOpenUnits ((i : I) → f i) := by
  simp_rw [isOpenUnits_iff] at *
  expose_names
  exact (Topology.IsOpenEmbedding.of_comp_iff _ (Topology.IsOpenEmbedding.piMap inst_3)).mpr
    piUnits_isOpenEmbedding

end ContinuousMulEquiv
