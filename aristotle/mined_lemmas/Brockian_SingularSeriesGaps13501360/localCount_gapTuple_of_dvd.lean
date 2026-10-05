import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
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

set_option grind.warning false

namespace Brockian

/-- The set of residue classes modulo `p` occupied by the tuple `H`. -/

lemma localCount_gapTuple_of_dvd {a d k p : ℕ} (hk : 0 < k) (hpd : p ∣ d) :
    localCount (gapTuple a d k) p = 1 := by
  have hres : residues (gapTuple a d k) p = {a % p} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    constructor
    · simp only [residues, Finset.mem_image, gapTuple]
      exact ⟨a, ⟨0, Finset.mem_range.mpr hk, by simp⟩, rfl⟩
    · intro r hr
      simp only [residues, gapTuple, Finset.mem_image, Finset.mem_range] at hr
      obtain ⟨h, ⟨i, _, rfl⟩, rfl⟩ := hr
      obtain ⟨c, rfl⟩ := hpd
      simp [Nat.mul_left_comm, Nat.add_mul_mod_self_left]
  simp [localCount, hres]

/-- The gap range: every element of the tuple lies in the interval `[a, a + (k-1)d]`,
and both endpoints are attained (for `k > 0`), so the diameter is exactly `(k-1)·d`. -/
