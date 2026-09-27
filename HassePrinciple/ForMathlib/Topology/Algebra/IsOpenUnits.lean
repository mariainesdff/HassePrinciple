/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.ForMathlib.Topology.Algebra.Group.Units

/-!
# Properties of units in products

This file contains the instances that the units in a product of two or finitely many topological
monoids are open.
-/

@[expose] public section

open Topology ContinuousMulEquiv

/-- The units in a product of two topological monoids are open. -/
instance {M N : Type*} [Monoid M] [TopologicalSpace M] [Monoid N]
    [TopologicalSpace N] [hM : IsOpenUnits M] [hN : IsOpenUnits N] : IsOpenUnits (M × N) := by
  rw [isOpenUnits_iff] at *
  exact (Topology.IsOpenEmbedding.of_comp_iff _ (hM.prodMap hN)).mpr prodUnits_isOpenEmbedding

/-- The units in a product of finitely many topological monoids are open. -/
instance {I : Type*} [Finite I] {f : I → Type _} [(i : I) → Monoid (f i)]
    [(i : I) → TopologicalSpace (f i)] [(i : I) → IsOpenUnits (f i)] :
      IsOpenUnits ((i : I) → f i) := by
  simp_rw [isOpenUnits_iff] at *
  expose_names
  exact (Topology.IsOpenEmbedding.of_comp_iff _ (Topology.IsOpenEmbedding.piMap inst_3)).mpr
    piUnits_isOpenEmbedding
