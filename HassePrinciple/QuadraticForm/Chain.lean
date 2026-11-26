/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-! # Chains of orthogonal bases -/

@[expose] public section

namespace Module.Basis

/-- Two bases are called contiguous if they have an element in common. -/
def IsContiguous {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (b b' : Basis ι R M) : Prop :=
  ∃ (i j : ι), b i = b' j

theorem IsContiguous.map {ι R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] {b b' : Basis ι R M} (hc : b.IsContiguous b') (f : M ≃ₗ[R] N) :
    (b.map f).IsContiguous (b'.map f) := by
  obtain ⟨i, j, hij⟩ := hc
  exact ⟨i, j, by rw [Basis.map_apply, Basis.map_apply, hij]⟩

variable {k : Type*} [Field k] [Invertible (2 : k)]
  {V : Type*} [AddCommGroup V] [Module k V] --[FiniteDimensional k V]
  {Q : QuadraticForm k V}

/-- Given a quadratic form `Q` and two bases `b, b'` of the vector space `V`, a chain from `b` to
  `b'` is a finite sequence of `Q`-orthogonal bases `(b_0, ..., b_m)` of `V` such that
  `b_0 = b`, `b_m = b'` and `b_i and b_{i + 1}` are contiguous for `0 ≤ i < m`. -/
structure Chain {R M ι : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]
    [Fintype ι] (Q : QuadraticForm R M) (b b' : Basis ι R M) : Type _ where
    /-- The chain has lenght `m + 1`. -/
    m : ℕ
    /-- The underlying collection of bases. -/
    basis : Fin (m + 1) → Basis ι R M
    basis_ortho (i : Fin (m + 1)) : Q.associated.IsOrthoᵢ (basis i)
    basis_zero : basis 0 = b
    basis_m_sub_one : basis ⟨m, lt_add_one m⟩ = b'
    basis_isContiguous (i : ℕ) (hi : i < m) :
      (basis ⟨i, by omega⟩).IsContiguous (basis ⟨i + 1, by omega⟩)

-- Used in the proof of case (iii) of Theorem 2.
lemma exists_const (hdim : 3 ≤ finrank k V) (hQ : Q.Nondegenerate)
    {b b' : Basis (Fin (finrank k V)) k V} (hb : Q.associated.IsOrthoᵢ b)
    (hb' : Q.associated.IsOrthoᵢ b')
    (h1 : (Q.associated (b ⟨1, by omega⟩) (b ⟨1, by omega⟩)) *
      (Q.associated (b' ⟨1, by omega⟩) (b' ⟨1, by omega⟩)) -
      (Q.associated (b' ⟨1, by omega⟩) (b' ⟨1, by omega⟩)) ^ 2 = 0)
    (h2 : (Q.associated (b ⟨1, by omega⟩) (b ⟨1, by omega⟩)) *
      (Q.associated (b' ⟨2, by omega⟩) (b' ⟨2, by omega⟩)) -
      (Q.associated (b' ⟨2, by omega⟩) (b' ⟨2, by omega⟩)) ^ 2 = 0) :
    ∃ (x : k), Q (b' ⟨1, by omega⟩ + x • b' ⟨2, by omega⟩) ≠ 0 ∧
    ((Q.restrict (Submodule.span k {b ⟨1, by omega⟩,
      b' ⟨1, by omega⟩ + x • b' ⟨2, by omega⟩}))).Nondegenerate := by
  sorry

-- Theorem 2 in Section IV.1. Depends on Proposition 2, which is probably in Mathlib.
/-- Let `V` be a vector space of dimension at least `3`, let `Q` be a nondegenerate quadratic form
  on `V` and let `b, b'` be two `Q`-orthogonal bases of `V`. Then there exists a chain from
  `b` to `b'`. -/
def chainOfNondegenerate {ι : Type*} [Fintype ι] (hdim : 3 ≤ Fintype.card ι) (hQ : Q.Nondegenerate)
    {b b' : Basis ι k V} (hb : Q.associated.IsOrthoᵢ b) (hb' : Q.associated.IsOrthoᵢ b') :
    Chain Q b b' := sorry

theorem chain_of_nondegenerate {ι : Type*} [Fintype ι] (hdim : 3 ≤ Fintype.card ι)
    (hQ : Q.Nondegenerate) {b b' : Basis ι k V}
    (hb : Q.associated.IsOrthoᵢ b) (hb' : Q.associated.IsOrthoᵢ b') :
    Nonempty (Chain Q b b') := ⟨chainOfNondegenerate hdim hQ hb hb'⟩

end Module.Basis
