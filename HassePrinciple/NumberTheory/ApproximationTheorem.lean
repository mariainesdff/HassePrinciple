/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.PrimeCounting

/-! # Approximation theorem. -/

@[expose] public section


noncomputable section

namespace Rat


/-- The instance that the nth prime number is prime. -/
local instance fact_prime_nth_prime (p : Nat.Primes) : Fact (Nat.Prime p) :=
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
abbrev finiteEmbedding (S : Finset Nat.Primes) (x : ℚ) : ℝ × (Π p : S, ℚ_[p]) :=
  ⟨algebraMap ℚ ℝ x, fun p ↦ (algebraMap ℚ ℚ_[p]) x⟩

/-- The approximation theorem can be restated as saying that the finite embedding is dense. -/
theorem approximation (S : Finset Nat.Primes) :
    Dense (Set.range (finiteEmbedding S)) := by
  sorry


-- maybe we need this now

/-- The finite embedding of ℚ into the product of the completions of ℚ at a finite set of places
(which includes ℝ). -/
abbrev finiteEmbedding'' (S : Finset Nat.Primes) (x : ℚˣ) : ℝˣ × Π p : S, ℚ_[p]ˣ :=
  ⟨Units.map (algebraMap ℚ ℝ) x, fun p ↦ Units.map (algebraMap ℚ ℚ_[p]) x⟩

/-- The approximation theorem can be restated as saying that the finite embedding is dense. -/
theorem approximation'' (S : Finset Nat.Primes) :
    Dense (Set.range (finiteEmbedding'' S)) := by
  sorry



end Rat
