/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

/-- `residueCount H p` is the number of distinct residue classes modulo `p`
occupied by the shifts in the tuple `H`. -/

theorem residueCount_gapLadder_small {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpn : p ≤ n) :
    residueCount (gapLadder n) p = 1 := by
  have hdvd : p ∣ n ! := Nat.dvd_factorial hp.pos hpn
  have hzero : ((n ! : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
  have himg : (gapLadder n).image (fun h : ℤ => (h : ZMod p)) = {0} := by
    apply Finset.eq_singleton_iff_unique_mem.2
    constructor
    · simp only [Finset.mem_image, gapLadder, Finset.mem_image, Finset.mem_range]
      exact ⟨0, ⟨0, hn, by simp⟩, by simp⟩
    · intro x hx
      simp only [Finset.mem_image, gapLadder, Finset.mem_range] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨i, _, rfl⟩ := hy
      push_cast
      rw [hzero, mul_zero]
  rw [residueCount, himg, Finset.card_singleton]

/-- Every gap ladder is admissible. -/
