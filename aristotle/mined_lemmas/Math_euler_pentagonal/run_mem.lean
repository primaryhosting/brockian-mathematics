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

lemma run_mem {s : Finset ℕ} (hne : s.Nonempty) {i : ℕ} (hi : i < run s) :
    (fmax s - i) ∈ s := by
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · simpa using fmax_mem hne
  · by_contra hmem
    have : run s ≤ i := Nat.sInf_le ⟨hipos, hmem⟩
    omega

