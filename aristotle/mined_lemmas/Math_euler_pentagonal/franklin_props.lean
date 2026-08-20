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

lemma franklin_props {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) (hexc : ¬ isExc s) :
    0 ∉ franklin s ∧ (∑ i ∈ franklin s, i) = (∑ i ∈ s, i) ∧
      ((franklin s).card + 1 = s.card ∨ s.card + 1 = (franklin s).card) ∧
      ¬ isExc (franklin s) ∧ franklin (franklin s) = s := by
  by_cases hA : fmin s ≤ run s
  · have hnexc : fmax s + 1 ≠ 2 * fmin s := fun h => hexc (Or.inl ⟨hA, h⟩)
    obtain ⟨a, b, c, d, e⟩ := caseA h0 hne hA hnexc
    exact ⟨a, b, Or.inl c, d, e⟩
  · have hA' : run s < fmin s := by omega
    have hnexc : fmax s ≠ 2 * run s := fun h => hexc (Or.inr ⟨hA', h⟩)
    obtain ⟨a, b, c, d, e⟩ := caseB h0 hne hA hnexc
    exact ⟨a, b, Or.inr c, d, e⟩

