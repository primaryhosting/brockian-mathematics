import Mathlib
/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
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

namespace Math

/-- The smallest element of a finite set of naturals (junk value `0` if empty). -/

lemma run_spec {s : Finset ℕ} (h0 : 0 ∉ s) : 1 ≤ run s ∧ (fmax s - run s) ∉ s := by
  have hex : ∃ t, t ∈ {t : ℕ | 1 ≤ t ∧ (fmax s - t) ∉ s} := by
    rcases Nat.eq_zero_or_pos (fmax s) with h | h
    · exact ⟨1, by simp [h, h0]⟩
    · exact ⟨fmax s, ⟨h, by simpa using h0⟩⟩
  exact Nat.sInf_mem hex

