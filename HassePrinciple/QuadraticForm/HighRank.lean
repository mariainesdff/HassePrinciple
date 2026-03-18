/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.QuadraticForm.Basic

@[expose] public section

namespace QuadraticForm.EverywhereLocallyIsotropic

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (Q : QuadraticForm ℚ V)

lemma isotropic_of_five_le_rank (hr : 5 ≤ Module.finrank ℚ V) (hQ : Q.Nondegenerate)
    (hQ' : Q.EverywhereLocallyIsotropic) :
    Q.Isotropic := sorry


end QuadraticForm.EverywhereLocallyIsotropic
