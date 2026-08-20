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

/-!
# Character multiplicities for the vertex representation of the dihedral group

This file generalizes the classical `D₅` (pentagon) representation-theoretic computation to
arbitrary regular `n`-gons.

The symmetry group of the regular `n`-gon is `DihedralGroup n`, acting on the vertex set
`ZMod n`.  We define

* `Brockian.vertexAct` : the action of `DihedralGroup n` on the vertices `ZMod n`;
* `Brockian.permChar`  : the character of the permutation (vertex) representation, i.e. the
  number of vertices fixed by a group element;
* `Brockian.dihedralChar n k` : the character of the two–dimensional representation `ρ_k`
  of `DihedralGroup n` (rotation by `2πk/n`), namely `r i ↦ 2 cos (2πki/n)`, `sr i ↦ 0`;
* `Brockian.charMult` : the multiplicity `⟨χ_perm, χ⟩ = (1/|G|) ∑_g χ_perm(g) χ(g)`.

The main theorem `Brockian.PentagonPentagonCharacterMultiplicityExt` states that every such
two–dimensional character occurs in the vertex representation with multiplicity exactly `1`,
for every `n` and every `k`.  Auxiliary results compute the multiplicity of the trivial
character (`1`, i.e. Burnside's lemma for the transitive vertex action) and of the sign
character (`0`).
-/

namespace Brockian

open DihedralGroup

/-- The action of the symmetry group of the regular `n`-gon on its vertex set `ZMod n`:
the rotation `r i` sends `v` to `v - i`, and the reflection `sr i` sends `v` to `i - v`. -/

@[simp] lemma permChar_one (n : ℕ) [NeZero n] : permChar n 1 = n := by
  have h : (1 : DihedralGroup n) = r 0 := rfl
  rw [h, permChar_r, if_pos rfl]

/-- Summed over all reflections, the number of fixed vertices is `n`. -/
