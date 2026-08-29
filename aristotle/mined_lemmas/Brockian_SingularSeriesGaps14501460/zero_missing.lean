import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Brockian

/-- The gap window: the integers of the range `[1450, 1460]`. -/

lemma zero_missing {p : ℕ} (hp : p.Prime) (hp8 : p ≤ 8) : ∀ h ∈ gapTuple, (h : ZMod p) ≠ 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h2 := hp.two_le
  have hdvd : (p : ℤ) ∣ 210 := by
    interval_cases p <;> revert hp <;> decide
  intro h hh hz
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  have hgcd : Int.gcd h 210 = 1 := by
    have := (Finset.mem_filter.mp hh).2
    simpa using this
  have hdd : (p : ℕ) ∣ Int.gcd h 210 := Int.dvd_gcd hz hdvd
  rw [hgcd] at hdd
  have := Nat.le_of_dvd one_pos hdd
  omega

