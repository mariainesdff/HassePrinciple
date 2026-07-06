/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

/-! # Determinants of linear maps -/

lemma LinearEquiv.det_toMatrix_ne_zero {ι R M N : Type*} [DecidableEq ι] [Fintype ι]
    [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (f : M ≃ₗ[R] N) :
    (LinearMap.toMatrix b b' f).det ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse (B := LinearMap.toMatrix b' b f.symm)
    (by simp [← LinearMap.toMatrix_comp])
