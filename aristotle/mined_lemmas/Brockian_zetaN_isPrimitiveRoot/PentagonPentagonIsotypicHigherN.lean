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

theorem PentagonPentagonIsotypicHigherN (n : ℕ) [NeZero n] (j l : ZMod n) :
    ngonChar n j 1 = 2 ∧
    (∀ k : ZMod n, ngonChar n j (r k) = chiN n (j * k) + chiN n (-(j * k))) ∧
    (∀ k : ZMod n, ngonChar n j (sr k) = 0) ∧
    (2 * j ≠ 0 → charInner n (ngonChar n j) (ngonChar n j) = 1) ∧
    (j ≠ l → j ≠ -l → charInner n (ngonChar n j) (ngonChar n l) = 0) ∧
    charInner n (vertexChar n) (ngonChar n j) = 1 ∧
    (∀ g : DihedralGroup n,
      vertexRep n g * vertexIntertwiner n j = vertexIntertwiner n j * ngonRep n j g) ∧
    (2 * j ≠ 0 →
      Function.Injective (fun u : Fin 2 → ℂ => Matrix.mulVec (vertexIntertwiner n j) u)) :=
  ⟨ngonChar_one n j, fun k => ngonChar_r n j k, fun k => ngonChar_sr n j k,
    ngonChar_self_inner n j, ngonChar_orthogonal n j l, vertex_ngon_multiplicity_one n j,
    vertexIntertwiner_comm n j, vertexIntertwiner_injective n j⟩

/-- The original pentagon (`n = 5`) statements, recovered as a special case: the two
two-dimensional representations `ρ₁`, `ρ₂` of `D₅` are irreducible, inequivalent, and each occurs
with multiplicity one in the permutation representation on the five vertices of the pentagon. -/
