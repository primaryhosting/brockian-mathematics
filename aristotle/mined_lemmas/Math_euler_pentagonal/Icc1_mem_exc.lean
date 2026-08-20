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

lemma Icc1_mem_exc {n m : ℕ} (hm : 1 ≤ m) (h : 2 * n = m * (3 * m - 1)) :
    Finset.Icc m (2 * m - 1) ∈ (D n).filter isExc := by
  have hle : m ≤ 2 * m - 1 := by omega
  have h0 : (0 : ℕ) ∉ Finset.Icc m (2 * m - 1) := zero_notMem_Icc hm
  have hmin : fmin (Finset.Icc m (2 * m - 1)) = m := fmin_Icc hle
  have hmax : fmax (Finset.Icc m (2 * m - 1)) = 2 * m - 1 := fmax_Icc hle
  have hrun : run (Finset.Icc m (2 * m - 1)) = m := by
    rw [run_Icc hm hle]; omega
  have hsum : (∑ i ∈ Finset.Icc m (2 * m - 1), i) = n := by
    have h1 := sum_Icc_id m (2 * m - 1) (by omega)
    obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    subst hm'
    have h2 : 2 * (m' + 1) - 1 + 1 = 2 * m' + 2 := by omega
    have h3 : 2 * (m' + 1) - 1 = 2 * m' + 1 := by omega
    have h4 : 3 * (m' + 1) - 1 = 3 * m' + 2 := by omega
    rw [h3] at h1 ⊢
    rw [h4] at h
    simp only [Nat.add_sub_cancel] at h1
    nlinarith [h1, h]
  rw [Finset.mem_filter, mem_D_iff]
  refine ⟨⟨h0, hsum⟩, Or.inl ⟨by omega, by omega⟩⟩

