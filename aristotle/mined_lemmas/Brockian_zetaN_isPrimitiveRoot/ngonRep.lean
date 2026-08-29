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

noncomputable def ngonRep (j : ZMod n) : DihedralGroup n →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun g := match g with
    | .r k => !![chiN n (j * k), 0; 0, chiN n (-(j * k))]
    | .sr k => !![0, chiN n (-(j * k)); chiN n (j * k), 0]
  map_one' := by
    show (!![chiN n (j * (0 : ZMod n)), 0; 0, chiN n (-(j * (0 : ZMod n)))] :
      Matrix (Fin 2) (Fin 2) ℂ) = 1
    simp [Matrix.one_fin_two]
  map_mul' := by
    rintro (a | a) (b | b) <;>
      simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr] <;>
      ext i k <;> fin_cases i <;> fin_cases k <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, mul_add, mul_sub, neg_sub,
        AddChar.map_add_eq_mul, AddChar.map_sub_eq_div, AddChar.map_neg_eq_inv] <;>
      field_simp

/-- The character of `ngonRep n j`. -/
