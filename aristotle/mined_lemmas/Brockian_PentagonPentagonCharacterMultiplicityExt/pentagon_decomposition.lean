import RequestProject.PentagonExt

/-!
# Decomposition of the vertex representation of a regular `n`-gon, `n` odd

For an odd number of vertices `n = 2m+1`, the permutation character of `DihedralGroup n`
acting on the vertices of the regular `n`-gon decomposes as the trivial character plus the
`m` two-dimensional characters `rotChar n 1, …, rotChar n m`.

For `n = 5` this is the classical pentagon statement `5 = 1 + 2 + 2`.
-/

open Finset

namespace Brockian

open DihedralGroup

variable {n : ℕ}

/-- For an odd `n`-gon every reflection fixes exactly one vertex. -/

theorem pentagon_decomposition (g : DihedralGroup 5) :
    permChar 5 g = trivChar 5 g + rotChar 5 1 g + rotChar 5 2 g := by
  have h := permChar_odd_decomposition 2 g
  simpa [Finset.sum_Icc_succ_top, add_assoc] using h

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

import Mathlib

/-!
# Character multiplicities of the vertex representation of a regular `n`-gon

The regular pentagon has symmetry group `DihedralGroup 5`, acting on its five vertices.
Here we generalize the pentagon computations to an arbitrary regular `n`-gon
(`n ≥ 1`, i.e. `[NeZero n]`), whose symmetry group is `DihedralGroup n` acting on the
vertex set `ZMod n`.

The main result, `Brockian.PentagonPentagonCharacterMultiplicityExt`, computes the
multiplicity of the trivial character, of the sign character, and of each two-dimensional
rotation character inside the permutation character of the vertex action:
they are `1`, `0` and `1` respectively.
-/

open Finset

namespace Brockian

open DihedralGroup

variable {n : ℕ}

/-- The action of a dihedral symmetry on the vertex set `ZMod n` of the regular `n`-gon.
The rotation `r i` acts by `x ↦ x - i` and the reflection `sr i` acts by `x ↦ i - x`;
these conventions make the map `g ↦ (x ↦ ngonAct n g x)` a genuine group action. -/
