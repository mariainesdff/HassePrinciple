/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Topological properties of units

This file contains results about units in topological monoids, namely the isomorphism of topological
groups between the units of a product of two groups and the product of the units and the facts that
the units of a (finite or infinite) product of topological monoids embeds to an open in the prodict.
-/

@[expose] public section

open Topology ContinuousMulEquiv

namespace ContinuousMulEquiv

/-- The isomorphism of topological monoids between the units of a product of two monoids and
the product of the units. -/
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

/-- Given two topological monoids M and N, (M × N)ˣ → M × N is an open embedding. -/
theorem prodUnits_isOpenEmbedding {M N : Type*} [Monoid M] [TopologicalSpace M]
    [Monoid N] [TopologicalSpace N] :
    IsOpenEmbedding (prodUnits M N) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (map_continuous (prodUnits M N)) (prodUnits M N).injective (prodUnits M N).isOpenMap

/-- Given a family of topological monoids M_i, (Π M_i)ˣ → Π M_i is an open embedding. -/
theorem piUnits_isOpenEmbedding {I : Type*} {f : I → Type _}
    [(i : I) → Monoid (f i)] [(i : I) → TopologicalSpace (f i)] :
    IsOpenEmbedding (piUnits (M := f)) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (map_continuous piUnits) (ContinuousMulEquiv.injective piUnits) piUnits.isOpenMap

end ContinuousMulEquiv
