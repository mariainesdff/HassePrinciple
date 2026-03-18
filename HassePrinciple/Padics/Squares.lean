/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/

module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

namespace Padic

variable (p : ℕ) [Fact (Nat.Prime p)]

def squares : OpenSubgroup ℚ_[p]ˣ where
  carrier  := {x : ℚ_[p]ˣ | IsSquare x}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry
  isOpen'  := sorry

end Padic
