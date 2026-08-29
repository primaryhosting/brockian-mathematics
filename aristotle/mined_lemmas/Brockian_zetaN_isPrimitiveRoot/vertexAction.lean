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

def vertexAction : DihedralGroup n →* Equiv.Perm (ZMod n) where
  toFun g := match g with
    | .r i => Equiv.subRight i
    | .sr i => (Equiv.neg (ZMod n)).trans (Equiv.addLeft i)
  map_one' := by ext k; exact sub_zero k
  map_mul' := by
    rintro (a | a) (b | b) <;> ext k <;>
      simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr, Equiv.Perm.mul_apply,
        Equiv.subRight_apply, Equiv.trans_apply, Equiv.neg_apply, Equiv.coe_addLeft] <;>
      ring

/-- The permutation representation of `DihedralGroup n` on the vertices of the regular `n`-gon. -/
