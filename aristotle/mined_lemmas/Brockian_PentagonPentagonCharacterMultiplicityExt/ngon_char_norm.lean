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

theorem ngon_char_norm (n : ℕ) [NeZero n] :
    ((Fintype.card (DihedralGroup n) : ℚ)⁻¹ *
      ∑ g : DihedralGroup n, (ngonChar n g : ℚ) ^ 2)
      = ((n : ℚ) + (ngonChar n (DihedralGroup.sr 0) : ℚ)) / 2 := by
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hcast : ∑ g : DihedralGroup n, ((ngonChar n g : ℚ)) ^ 2
      = (n : ℚ) * ((n : ℚ) + (ngonChar n (DihedralGroup.sr 0) : ℚ)) := by
    calc ∑ g : DihedralGroup n, ((ngonChar n g : ℚ)) ^ 2
        = ((∑ g : DihedralGroup n, (ngonChar n g) ^ 2 : ℕ) : ℚ) := by push_cast; ring
      _ = (n : ℚ) * ((n : ℚ) + (ngonChar n (DihedralGroup.sr 0) : ℚ)) := by
            rw [ngon_sum_char_sq n]; push_cast; ring
  rw [hcast, DihedralGroup.card]
  push_cast
  field_simp

/-- For odd `n` the permutation character of the `n`-gon satisfies `⟨χ, χ⟩ = (n+1)/2`; equivalently
the permutation representation splits as the trivial representation plus `(n-1)/2` pairwise
distinct two-dimensional irreducible constituents. -/
