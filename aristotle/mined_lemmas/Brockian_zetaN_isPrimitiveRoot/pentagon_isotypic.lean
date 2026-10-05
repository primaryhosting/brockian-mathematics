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

theorem pentagon_isotypic :
    charInner 5 (ngonChar 5 1) (ngonChar 5 1) = 1 ∧
    charInner 5 (ngonChar 5 2) (ngonChar 5 2) = 1 ∧
    charInner 5 (ngonChar 5 1) (ngonChar 5 2) = 0 ∧
    charInner 5 (vertexChar 5) (ngonChar 5 1) = 1 ∧
    charInner 5 (vertexChar 5) (ngonChar 5 2) = 1 ∧
    Function.Injective (fun u : Fin 2 → ℂ => Matrix.mulVec (vertexIntertwiner 5 1) u) ∧
    Function.Injective (fun u : Fin 2 → ℂ => Matrix.mulVec (vertexIntertwiner 5 2) u) :=
  ⟨ngonChar_self_inner 5 1 (by decide), ngonChar_self_inner 5 2 (by decide),
    ngonChar_orthogonal 5 1 2 (by decide) (by decide),
    vertex_ngon_multiplicity_one 5 1, vertex_ngon_multiplicity_one 5 2,
    vertexIntertwiner_injective 5 1 (by decide), vertexIntertwiner_injective 5 2 (by decide)⟩

end Brockian

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

