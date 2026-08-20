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

lemma mem_filter_props {n : ℕ} {s : Finset ℕ} (hn : 1 ≤ n)
    (hs : s ∈ (D n).filter (fun s => ¬ isExc s)) :
    0 ∉ s ∧ s.Nonempty ∧ (∑ i ∈ s, i) = n ∧ ¬ isExc s := by
  rw [Finset.mem_filter, mem_D_iff] at hs
  obtain ⟨⟨h0, hsum⟩, hexc⟩ := hs
  refine ⟨h0, ?_, hsum, hexc⟩
  rw [Finset.nonempty_iff_ne_empty]
  rintro rfl
  simp at hsum
  omega

