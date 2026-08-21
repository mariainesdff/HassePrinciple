/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Tactic.Abel

/-! # Linear independence -/

namespace Submodule

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

open Module

/-- The `R`-linear isomorphism between `R^2` and `span {x, y}` that sends the standard basis to
`{x, y}`. -/
noncomputable def basisSpanPairAux {x y : V} (hxy : LinearIndependent R ![x, y]) :
    (Fin 2 → R) ≃ₗ[R] (span R {x, y}) where
  toFun a := ⟨a 0 • x + a 1 • y, by simp [mem_span_pair]⟩
  map_add' a b := by simp [add_smul]; abel
  map_smul' k a := by simp [mul_smul]
  invFun v := ![(mem_span_pair.mp v.2).choose, (mem_span_pair.mp v.2).choose_spec.choose]
  left_inv a := by
    ext n
    have h := (mem_span_pair.mp
      ((⟨a 0 • x + a 1 • y, by simp [mem_span_pair]⟩ : span R {x, y})).2).choose_spec.choose_spec
    simp only [Fin.isValue] at h ⊢
    apply LinearIndependent.eq_coords_of_eq hxy (by simpa using h)
  right_inv v := by simp [(mem_span_pair.mp v.2).choose_spec.choose_spec]

/-- Linearly independent `{x, y}` form a basis for `span R {x, y}`. -/
public noncomputable def basisSpanPair {x y : V} (hxy : LinearIndependent R ![x, y]) :
    Module.Basis (Fin 2) R (span R {x, y}) where
  repr := (basisSpanPairAux hxy).symm.trans (Finsupp.linearEquivFunOnFinite R R (Fin 2)).symm

open Submodule in
public lemma basisSpanPair_add_repr {x y : V} (hxy : LinearIndependent R ![x, y])
    (v : span R {x, y}) :
    ((basisSpanPair hxy).repr v) 0 • x + ((basisSpanPair hxy).repr v) 1 • y = v := by
  simp [basisSpanPair, basisSpanPairAux, (mem_span_pair.mp v.2).choose_spec.choose_spec]

end Submodule
