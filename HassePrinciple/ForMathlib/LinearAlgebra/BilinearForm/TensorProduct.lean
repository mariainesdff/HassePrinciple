/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-! # Base change of bilinear maps -/

@[expose] public section

namespace LinearMap

variable {R A M N P Q : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]
  [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R N] [Module R P]
  [Module R Q] [SMulCommClass R R P] (f : M →ₗ[R] N →ₗ[R] P) (g : Q →ₗ[R] N)

lemma BilinMap.baseChange_compl₁₂ {R A M P Q : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid M] [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R P]
    [Module R Q] [SMulCommClass R R P] (f : M →ₗ[R] M →ₗ[R] P) (g g' : Q →ₗ[R] M) :
    BilinMap.baseChange A (f.compl₁₂ g g') =
      (LinearMap.BilinMap.baseChange A f).compl₁₂ (g.baseChange A) (g'.baseChange A) := by
  ext; simp

lemma BilinForm.baseChange_compl₁₂ {R A M Q : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid M] [AddCommMonoid Q] [Module R M] [Module R Q]
    (f : LinearMap.BilinForm R M) (g g' : Q →ₗ[R] M) :
    BilinForm.baseChange A (f.compl₁₂ g g') =
      (LinearMap.BilinForm.baseChange A f).compl₁₂ (g.baseChange A) (g'.baseChange A) := by
  ext; simp

@[simp]
lemma BilinForm.baseChange_add {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid M] [Module R M] (f g : LinearMap.BilinForm R M) :
    BilinForm.baseChange A (f + g) = BilinForm.baseChange A f + BilinForm.baseChange A g := by
  ext; simp [add_smul]

end LinearMap
