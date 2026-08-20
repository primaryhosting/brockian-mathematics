import Mathlib

/-!
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The natural action of the dihedral group `DihedralGroup n` on the `n` vertices of a regular
`n`-gon, the vertices being modelled by `ZMod n`.  The rotation `r i` sends a vertex `x` to
`x - i`, and the reflection `sr i` sends `x` to `i - x`. -/

theorem ngon_sum_char (n : ℕ) [NeZero n] :
    ∑ g : DihedralGroup n, ngonChar n g = 2 * n := by
  rw [sum_dihedral, ngon_sum_char_rotations, ngon_sum_char_reflections, two_mul]

/-- **Pentagon Pentagon Character Multiplicity Ext.**

Generalization of the `D₅` pentagon computation to an arbitrary regular `n`-gon (`n ≥ 1`).

The permutation character of `DihedralGroup n` acting on the `n` vertices of the regular `n`-gon
is `χ g = #{x | g • x = x}`.  Its multiplicity as a constituent of the trivial character,
`⟨χ, 1⟩ = |G|⁻¹ ∑_{g ∈ G} χ g`, equals `1`: the vertex action is transitive, so it has a single
orbit, and hence (Burnside) the sum of the fixed-point counts equals `|G| = 2n`. -/
