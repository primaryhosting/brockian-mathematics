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

lemma vertexRep_sr_mul_apply (k : ZMod n) (M : Matrix (ZMod n) (Fin 2) ℂ)
    (a : ZMod n) (c : Fin 2) :
    (vertexRep n (sr k) * M) a c = M (k - a) c := by
  rw [vertexRep_mul_apply]
  have hinv : (vertexAction n (sr k))⁻¹ = vertexAction n (sr k) := by rw [← map_inv, inv_sr]
  have h2 : (vertexAction n (sr k)).symm a = k - a := by
    rw [← Equiv.Perm.inv_def, hinv]; exact (sub_eq_add_neg k a).symm
  rw [h2]

/-- The `n × 2` matrix whose columns are the two discrete-Fourier vectors
`a ↦ ζₙ^(j a)` and `a ↦ ζₙ^(-j a)`. -/
