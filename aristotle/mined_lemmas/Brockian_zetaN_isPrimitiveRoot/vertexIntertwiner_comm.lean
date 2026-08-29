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

theorem vertexIntertwiner_comm (j : ZMod n) (g : DihedralGroup n) :
    vertexRep n g * vertexIntertwiner n j = vertexIntertwiner n j * ngonRep n j g := by
  rcases g with k | k
  · ext a c
    rw [vertexRep_r_mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases c
    · simp [vertexIntertwiner, ngonRep, mul_add, chiN_add]
    · simp only [vertexIntertwiner, ngonRep, Matrix.of_apply, MonoidHom.coe_mk, OneHom.coe_mk]
      norm_num
      rw [show -(j * (a + k)) = -(j * a) + -(j * k) by ring, chiN_add]
  · ext a c
    rw [vertexRep_sr_mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases c
    · simp only [vertexIntertwiner, ngonRep, Matrix.of_apply, MonoidHom.coe_mk, OneHom.coe_mk]
      norm_num
      rw [show j * (k - a) = -(j * a) + j * k by ring, chiN_add]
    · simp only [vertexIntertwiner, ngonRep, Matrix.of_apply, MonoidHom.coe_mk, OneHom.coe_mk]
      norm_num
      rw [show -(j * (k - a)) = j * a + -(j * k) by ring, chiN_add]

