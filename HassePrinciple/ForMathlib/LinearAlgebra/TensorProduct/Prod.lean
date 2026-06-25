/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # Lemmas about tensor products -/

@[expose] public section

namespace TensorProduct

lemma prodRight_fst {R A M₁ M₂ : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Invertible (2 : R)] [Invertible (2 : A)] [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁]
    [Module R M₂] (x : A ⊗[R] (M₁ × M₂)) :
    ((prodRight R A A M₁ M₂) x).1 = (LinearMap.baseChange A (LinearMap.fst R M₁ M₂)) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul => simp
  | add x y hx hy => simp [hx, hy]

lemma prodRight_snd {R A M₁ M₂ : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Invertible (2 : R)] [Invertible (2 : A)] [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁]
    [Module R M₂] (x : A ⊗[R] (M₁ × M₂)) :
    ((prodRight R A A M₁ M₂) x).2 = (LinearMap.baseChange A (LinearMap.snd R M₁ M₂)) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul => simp
  | add x y hx hy => simp [hx, hy]

end TensorProduct
