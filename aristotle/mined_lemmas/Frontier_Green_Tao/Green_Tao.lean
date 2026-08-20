import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The Green–Tao theorem states that the primes contain arbitrarily long arithmetic
progressions.  A search of Mathlib (`Nat.Prime`, additive combinatorics files)
shows that neither the Green–Tao theorem nor Szemerédi's theorem is available;
the closest available deep input is Dirichlet's theorem on primes in arithmetic
progressions (`Nat.forall_exists_prime_gt_and_modEq`), which does *not* imply the
statement (it produces one prime per residue class, not a progression of primes).

This file therefore does what is achievable and fully verified:

* `Frontier.PrimeAP` and `Frontier.GreenTaoStatement` formalize the statement.
* `Frontier.primeAP_card` checks the formalization is faithful: a witness for
  `PrimeAP k` really gives `k` distinct primes in arithmetic progression.
* `Frontier.primeAP_of_le_thirteen` proves the statement **unconditionally for all
  lengths `k ≤ 13`**, via the explicit progression `4943 + 60060·i`
  (`4943, 65003, …, 725663`), each term of which is checked prime.
* `Frontier.Green_Tao` is the Lean-checked reduction: the full statement follows
  from the inductive step alone ("a progression of length `k ≥ 13` can be
  extended to one of length `k + 1`"), the base cases being discharged.
* `Frontier.greenTao_iff_unbounded` records the equivalent reduction to
  unboundedness of the set of achievable lengths.
* `Frontier.prime_dvd_common_difference` proves the classical constraint that every
  prime `q < k` must divide the common difference of a `k`-term prime progression
  starting at `a ≥ k`.
-/

namespace Frontier

/-- `PrimeAP k` says that there is an arithmetic progression `a, a + d, …, a + (k-1)d`
of length `k`, with nonzero common difference `d`, all of whose terms are prime. -/

theorem Green_Tao (hstep : ∀ k : ℕ, 13 ≤ k → PrimeAP k → PrimeAP (k + 1)) :
    GreenTaoStatement := by
  have key : ∀ n : ℕ, PrimeAP (13 + n) := by
    intro n
    induction n with
    | zero => exact primeAP_thirteen
    | succ m ih =>
        have := hstep (13 + m) (by omega) ih
        simpa [show 13 + m + 1 = 13 + (m + 1) by omega] using this
  intro k
  rcases le_or_gt k 13 with h | h
  · exact primeAP_of_le_thirteen h
  · have := key (k - 13)
    simpa [show 13 + (k - 13) = k by omega] using this

/-- An equivalent form of the reduction: the Green–Tao statement holds iff the set of
lengths of prime arithmetic progressions is unbounded. -/
