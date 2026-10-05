/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- The number of distinct residue classes modulo `p` occupied by the tuple `H`.
This is the local density `ν_p(H)` appearing in the Hardy–Littlewood singular series. -/

lemma singularFactor_pair_of_not_dvd {p : ℕ} {d : ℤ} (hd0 : d ≠ 0) (hd : ¬ (p : ℤ) ∣ d) :
    singularFactor p ({0, d} : Finset ℤ) = (1 - 2 / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 2 := by
  rw [singularFactor, nu_pair_of_not_dvd p hd, card_pair hd0]
  norm_num

/-- Explicit local factor of a pair at an odd prime dividing the gap: it equals `p / (p - 1)`. -/
