/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian

/-- The number of distinct residue classes modulo `p` occupied by the integers of `H`.
This is the local density `ν_p(H)` appearing in the Hardy–Littlewood singular series. -/

lemma admissible_of_card_three {H : Finset ℤ} (hcard : H.card = 3)
    (h2 : nu 2 H < 2) (h3 : nu 3 H < 3) : Admissible H := by
  intro p hp
  rcases lt_or_ge p 5 with hlt | hge
  · interval_cases p
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · exact h2
    · exact h3
    · exact absurd hp (by decide)
  · calc nu p H ≤ H.card := nu_le_card _ _
      _ = 3 := hcard
      _ < p := by omega

/-- **Singular Series Gaps 13501360.**  The triple `{0, 1350, 1360}` is an admissible
prime-gap pattern: it has three elements, it omits a residue class modulo every prime, and
consequently every local factor of its Hardy–Littlewood singular series is strictly positive. -/
