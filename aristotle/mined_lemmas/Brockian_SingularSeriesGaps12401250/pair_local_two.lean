/-
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- A finite set of integers `H` (a *pattern*, or *gap tuple*) is **admissible** when for every
prime `p` the reductions of the elements of `H` modulo `p` miss at least one residue class.
This is exactly the condition under which every local factor `1 - ν_p(H)/p` of the
Hardy–Littlewood singular series `𝔖(H) = ∏_p (1 - ν_p(H)/p)(1 - 1/p)^{-|H|}` is nonzero. -/

theorem pair_local_two (g : ℤ) :
    (∃ r : ZMod 2, ∀ h ∈ ({0, g} : Finset ℤ), (h : ZMod 2) ≠ r) ↔ Even g := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hcast : ((g : ℤ) : ZMod 2) = 0 ↔ Even g := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.even_iff]
    push_cast
    omega
  constructor
  · rintro ⟨r, hr⟩
    have h0 : ((0 : ℤ) : ZMod 2) ≠ r := hr 0 (by simp)
    have h1 : ((g : ℤ) : ZMod 2) ≠ r := hr g (by simp)
    rw [Int.cast_zero] at h0
    rcases hz r with rfl | rfl
    · exact absurd rfl h0
    · rcases hz ((g : ℤ) : ZMod 2) with h | h
      · exact hcast.1 h
      · exact absurd h h1
  · intro hg
    refine ⟨1, ?_⟩
    intro h hh
    rcases Finset.mem_insert.1 hh with rfl | h'
    · rw [Int.cast_zero]; decide
    · rw [Finset.mem_singleton.1 h', hcast.2 hg]; decide

/-- Characterization of admissibility for the two element pattern `{0, g}`: it is admissible
exactly when the gap `g` is even. -/
