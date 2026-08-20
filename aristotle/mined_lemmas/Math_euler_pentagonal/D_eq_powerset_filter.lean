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

lemma D_eq_powerset_filter {n N : ℕ} (h : n ≤ N) :
    D n = (Finset.Icc 1 N).powerset.filter (fun s => ∑ i ∈ s, i = n) := by
  ext s
  rw [mem_D_iff, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨h0, hsum⟩
    refine ⟨fun a ha => ?_, hsum⟩
    have h1 : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (fun hh => h0 (hh ▸ ha))
    have h2 : a ≤ n :=
      hsum ▸ Finset.single_le_sum (f := fun i : ℕ => i) (fun i _ => Nat.zero_le i) ha
    rw [Finset.mem_Icc]
    omega
  · rintro ⟨hsub, hsum⟩
    refine ⟨fun h0 => ?_, hsum⟩
    have := hsub h0
    simp at this

