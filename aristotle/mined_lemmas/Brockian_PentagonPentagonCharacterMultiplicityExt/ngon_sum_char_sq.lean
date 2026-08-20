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

lemma ngon_sum_char_sq (n : ℕ) [NeZero n] :
    ∑ g : DihedralGroup n, (ngonChar n g) ^ 2 = n * (n + ngonChar n (DihedralGroup.sr 0)) := by
  classical
  have hrot : ∑ i : ZMod n, (ngonChar n (DihedralGroup.r i)) ^ 2 = n ^ 2 := by
    have h : ∀ i : ZMod n, (ngonChar n (DihedralGroup.r i)) ^ 2 = if i = 0 then n ^ 2 else 0 := by
      intro i
      rw [ngonChar_r]
      by_cases hi : i = 0 <;> simp [hi]
    rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_ite_eq' Finset.univ (0 : ZMod n)]
    simp
  have hrefl : ∑ i : ZMod n, (ngonChar n (DihedralGroup.sr i)) ^ 2
      = n * ngonChar n (DihedralGroup.sr 0) := by
    simp only [ngonChar_sr]
    exact sum_sq_reflection_solutions n
  rw [sum_dihedral n (fun g => (ngonChar n g) ^ 2), hrot, hrefl]
  ring

/-- The general inner product of the `n`-gon permutation character with itself:
`⟨χ, χ⟩ = (n + χ(sr 0)) / 2`, where `χ(sr 0)` is the number of solutions of `2d = 0` in `ZMod n`
(one for odd `n`, two for even `n`).  Equivalently, `⟨χ, χ⟩` is the number of orbits of the
dihedral group on ordered pairs of vertices. -/
