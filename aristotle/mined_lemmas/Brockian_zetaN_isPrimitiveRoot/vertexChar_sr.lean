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

lemma vertexChar_sr (i : ZMod n) :
    vertexChar n (sr i) = ({a : ZMod n | 2 * a = i} : Finset (ZMod n)).card := by
  classical
  have h : vertexRep n (sr i) = ((vertexAction n (sr i))⁻¹).permMatrix ℂ := rfl
  rw [vertexChar, h, Matrix.trace]
  simp only [Matrix.diag_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq]
  have hinv : (vertexAction n (sr i))⁻¹ = vertexAction n (sr i) := by
    rw [← map_inv, inv_sr]
  have hkey : ∀ a : ZMod n, ((vertexAction n (sr i))⁻¹) a = i - a := by
    intro a; rw [hinv]; exact (sub_eq_add_neg i a).symm ▸ rfl
  have hcond : ∀ a : ZMod n, (i - a = a) ↔ (2 * a = i) := by
    intro a; constructor <;> intro h' <;> linear_combination -h'
  simp_rw [hkey, hcond]
  rw [Finset.sum_boole]

/-- The standard hermitian inner product on class functions of `DihedralGroup n`. -/
