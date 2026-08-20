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

lemma exc_eq {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) (h : isExc s) :
    s = Finset.Icc (fmin s) (fmax s) ∧
      (fmax s + 1 = 2 * fmin s ∨ fmax s + 2 = 2 * fmin s) := by
  have hσM : fmin s ≤ fmax s := le_fmax (fmin_mem hne)
  have hσpos : 0 < fmin s := fmin_pos h0 hne
  have hτpos : 0 < run s := run_pos h0
  have hd : fmax s - fmin s < run s ∧ (fmax s + 1 = 2 * fmin s ∨ fmax s + 2 = 2 * fmin s) := by
    rcases h with ⟨hA, hE⟩ | ⟨hB, hE⟩
    · exact ⟨by omega, Or.inl hE⟩
    · have h1 : run s - 1 < run s := by omega
      have h3 := fmin_le (run_mem hne h1)
      exact ⟨by omega, Or.inr (by omega)⟩
  refine ⟨Finset.Subset.antisymm (fun a ha => ?_) (fun a ha => ?_), hd.2⟩
  · simp only [Finset.mem_Icc]
    exact ⟨fmin_le ha, le_fmax ha⟩
  · rw [Finset.mem_Icc] at ha
    have h1 : fmax s - a < run s := by omega
    have h2 := run_mem hne h1
    have h3 : fmax s - (fmax s - a) = a := by omega
    rwa [h3] at h2

