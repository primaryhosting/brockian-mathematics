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

lemma Icc2_mem_exc {n m : ℕ} (hm : 1 ≤ m) (h : 2 * n = m * (3 * m + 1)) :
    Finset.Icc (m + 1) (2 * m) ∈ (D n).filter isExc := by
  have hle : m + 1 ≤ 2 * m := by omega
  have h0 : (0 : ℕ) ∉ Finset.Icc (m + 1) (2 * m) := zero_notMem_Icc (by omega)
  have hmin : fmin (Finset.Icc (m + 1) (2 * m)) = m + 1 := fmin_Icc hle
  have hmax : fmax (Finset.Icc (m + 1) (2 * m)) = 2 * m := fmax_Icc hle
  have hrun : run (Finset.Icc (m + 1) (2 * m)) = m := by
    rw [run_Icc (by omega) hle]; omega
  have hsum : (∑ i ∈ Finset.Icc (m + 1) (2 * m), i) = n := by
    have h1 := sum_Icc_id (m + 1) (2 * m) (by omega)
    simp only [Nat.add_sub_cancel] at h1
    nlinarith [h1, h]
  rw [Finset.mem_filter, mem_D_iff]
  refine ⟨⟨h0, hsum⟩, Or.inr ⟨by omega, by omega⟩⟩

/-! ### Matching the exceptional partitions with pentagonal indices -/

/-- The (generalized) pentagonal index attached to an exceptional partition. -/
