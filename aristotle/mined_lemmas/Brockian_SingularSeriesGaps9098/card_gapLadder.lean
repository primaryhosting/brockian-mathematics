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

theorem card_gapLadder (n : ℕ) : (gapLadder n).card = n := by
  rw [gapLadder, Finset.card_image_of_injective _ ?_, Finset.card_range]
  intro a b hab
  have hfac : ((n ! : ℤ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have : (a : ℤ) = (b : ℤ) := mul_right_cancel₀ hfac hab
  exact_mod_cast this

/-- For a prime `p ≤ n`, the whole ladder collapses to the single class `0 mod p`. -/
