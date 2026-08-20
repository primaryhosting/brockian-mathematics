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

lemma run_Icc {a b : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ b) : run (Finset.Icc a b) = b - a + 1 := by
  have h0 : (0 : ℕ) ∉ Finset.Icc a b := zero_notMem_Icc h1
  have hne : (Finset.Icc a b).Nonempty := ⟨a, by simp [h2]⟩
  have hmax : fmax (Finset.Icc a b) = b := fmax_Icc h2
  have hle : run (Finset.Icc a b) ≤ b - a + 1 := by
    refine Nat.sInf_le ⟨by omega, ?_⟩
    rw [hmax]
    simp only [Finset.mem_Icc]
    omega
  by_contra hcon
  have hlt : run (Finset.Icc a b) < b - a + 1 := lt_of_le_of_ne hle hcon
  have hpos : 0 < run (Finset.Icc a b) := run_pos h0
  refine run_notMem h0 ?_
  rw [hmax]
  simp only [Finset.mem_Icc]
  omega

/-! ### The involution kills the non-exceptional part -/

