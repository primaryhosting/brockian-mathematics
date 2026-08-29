import Mathlib

/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
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

namespace Brockian

/-- The residues modulo `p` covered by the tuple `H`. -/

theorem coveredResidues_apTuple (k d p : ℕ) :
    coveredResidues (apTuple k d) p
      = (Finset.range k).image (fun i : ℕ => (i : ZMod p) * (d : ZMod p)) := by
  ext r
  simp only [mem_coveredResidues, apTuple, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨h, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, by push_cast; ring⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i * d, ⟨i, hi, rfl⟩, by push_cast; ring⟩

/-- **Admissibility criterion for arithmetic progressions.**
The tuple `{0, d, 2d, …, (k-1)d}` is admissible iff every prime `p ≤ k` divides `d`. -/
