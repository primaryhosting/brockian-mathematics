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

theorem isAdmissible_pair_iff {d : ℤ} (hd : d ≠ 0) :
    IsAdmissible ({0, d} : Finset ℤ) ↔ Even d := by
  constructor
  · intro h
    by_contra hodd
    have := h 2 Nat.prime_two
    rw [nu_two_pair_of_odd hodd] at this
    exact lt_irrefl 2 this
  · intro heven p hp
    rcases eq_or_lt_of_le hp.two_le with h2 | h2
    · rw [← h2, nu_two_pair_of_even heven]; norm_num
    · exact nu_lt_of_card_lt (by rw [card_pair hd]; omega)

/-- For an admissible tuple, every local factor of the singular series is positive. -/
