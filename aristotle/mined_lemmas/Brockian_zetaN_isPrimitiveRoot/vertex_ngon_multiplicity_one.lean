import Mathlib
/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The classical "pentagon" facts about the dihedral group `D₅` (the symmetry group of a regular
pentagon) are:

* `D₅` has two irreducible two-dimensional complex representations `ρ₁`, `ρ₂`, obtained by letting
  the rotation `r` act as a rotation by `2π/5` resp. `4π/5`;
* they are pairwise inequivalent;
* the permutation representation of `D₅` on the five vertices of the pentagon contains each of
  them with multiplicity exactly one — i.e. each `ρⱼ`-isotypic component of the vertex
  representation is exactly two-dimensional.

This file generalises all of this to an arbitrary regular `n`-gon.  For every `j : ZMod n` we build
a genuine two–dimensional complex representation `Brockian.ngonRep n j` of `DihedralGroup n`, and we
compute its character `Brockian.ngonChar n j`.  We then show, purely by character computations:

* `ngonChar n j` has norm one (so `ngonRep n j` is irreducible) as soon as `2 * j ≠ 0`;
* `ngonChar n j` and `ngonChar n l` are orthogonal when `j ≠ l` and `j ≠ -l`;
* the character of the vertex permutation representation pairs to `1` against every `ngonChar n j`,
  i.e. the multiplicity of `ρⱼ` in the vertex representation is one for every `j`.

Specialising to `n = 5` recovers the pentagon statements.
-/

open Complex DihedralGroup

namespace Brockian

section Roots

/-- A primitive `n`-th root of unity in `ℂ`. -/

theorem vertex_ngon_multiplicity_one (j : ZMod n) :
    charInner n (vertexChar n) (ngonChar n j) = 1 := by
  classical
  have hsum : ∑ x : DihedralGroup n, vertexChar n x * (starRingEnd ℂ) (ngonChar n j x)
      = 2 * n := by
    rw [sum_dihedral]
    have hsr : ∀ k : ZMod n,
        vertexChar n (sr k) * (starRingEnd ℂ) (ngonChar n j (sr k)) = 0 := by
      intro k; simp
    simp only [hsr, Finset.sum_const_zero, add_zero]
    have hterm : ∀ k : ZMod n,
        vertexChar n (r k) * (starRingEnd ℂ) (ngonChar n j (r k))
          = if k = 0 then (2 * n : ℂ) else 0 := by
      intro k
      rw [vertexChar_r]
      by_cases hk : k = 0
      · subst hk
        rw [if_pos rfl, ngonChar_r, conj_pair]
        simp
        ring
      · rw [if_neg hk, if_neg hk, zero_mul]
    simp only [hterm]
    rw [Finset.sum_ite_eq' Finset.univ (0 : ZMod n) (fun _ => (2 * n : ℂ))]
    simp
  rw [charInner, hsum, card_dihedral_ne_zero]
  have hn : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp

end Computations

section Intertwiner

/-!
## An explicit embedding of `ngonRep n j` into the vertex representation

The character computation above shows that the multiplicity is one.  Here we make the
"multiplicity at least one" half completely concrete by exhibiting an explicit injective
intertwiner: the `n x 2` discrete-Fourier matrix whose two columns are `a` mapsto `ζₙ^(j a)` and
`a` mapsto `ζₙ^(-j a)`.
-/

variable (n : ℕ) [NeZero n]

