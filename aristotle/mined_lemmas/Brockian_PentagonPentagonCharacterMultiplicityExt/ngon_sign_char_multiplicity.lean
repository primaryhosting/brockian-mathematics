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

theorem ngon_sign_char_multiplicity (n : ℕ) [NeZero n] :
    ((Fintype.card (DihedralGroup n) : ℚ)⁻¹ *
      ∑ g : DihedralGroup n, (ngonChar n g : ℚ) * ngonSignChar n g) = 0 := by
  have hrot : ∑ i : ZMod n, ((ngonChar n (DihedralGroup.r i) : ℚ) *
      ngonSignChar n (DihedralGroup.r i)) = (n : ℚ) := by
    have : ∀ i : ZMod n, ((ngonChar n (DihedralGroup.r i) : ℚ) *
        ngonSignChar n (DihedralGroup.r i)) = (ngonChar n (DihedralGroup.r i) : ℚ) := by
      intro i; simp [ngonSignChar]
    rw [Finset.sum_congr rfl fun i _ => this i, ← Nat.cast_sum, ngon_sum_char_rotations]
  have hrefl : ∑ i : ZMod n, ((ngonChar n (DihedralGroup.sr i) : ℚ) *
      ngonSignChar n (DihedralGroup.sr i)) = -(n : ℚ) := by
    have : ∀ i : ZMod n, ((ngonChar n (DihedralGroup.sr i) : ℚ) *
        ngonSignChar n (DihedralGroup.sr i)) = -(ngonChar n (DihedralGroup.sr i) : ℚ) := by
      intro i; simp [ngonSignChar]
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_neg_distrib, ← Nat.cast_sum,
      ngon_sum_char_reflections]
  rw [sum_dihedral n (fun g => (ngonChar n g : ℚ) * ngonSignChar n g), hrot, hrefl]
  ring

/-- For an odd-sided polygon every reflection fixes exactly one vertex, because doubling is a
bijection of `ZMod n`. -/
