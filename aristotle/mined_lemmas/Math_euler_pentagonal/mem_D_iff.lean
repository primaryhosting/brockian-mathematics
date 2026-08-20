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

lemma mem_D_iff {n : ℕ} {s : Finset ℕ} : s ∈ D n ↔ (0 ∉ s ∧ ∑ i ∈ s, i = n) := by
  simp only [D, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hsum⟩
    refine ⟨fun h0 => ?_, hsum⟩
    have := hsub h0
    simp at this
  · rintro ⟨h0, hsum⟩
    refine ⟨fun a ha => ?_, hsum⟩
    have h1 : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (fun h => h0 (h ▸ ha))
    have h2 : a ≤ n := hsum ▸ Finset.single_le_sum (f := fun i : ℕ => i)
      (fun i _ => Nat.zero_le i) ha
    simp [Finset.mem_Icc, h1, h2]

/-! ### Case A of Franklin's involution -/

