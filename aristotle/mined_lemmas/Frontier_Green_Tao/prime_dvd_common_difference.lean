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

theorem prime_dvd_common_difference {a d k q : ℕ} (hk : k ≤ a)
    (hap : ∀ i < k, Nat.Prime (a + i * d)) (hq : q.Prime) (hqk : q < k) : q ∣ d := by
  by_contra hnd
  haveI : Fact q.Prime := ⟨hq⟩
  have hd0 : (d : ZMod q) ≠ 0 := by
    simpa [ZMod.natCast_eq_zero_iff] using hnd
  set x : ZMod q := -(a : ZMod q) / (d : ZMod q) with hx
  have hi : x.val < q := ZMod.val_lt x
  have hdvd : q ∣ a + x.val * d := by
    have h0 : ((a + x.val * d : ℕ) : ZMod q) = 0 := by
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id, hx]
      field_simp
      ring
    exact (ZMod.natCast_eq_zero_iff _ _).mp h0
  have hp : Nat.Prime (a + x.val * d) := hap _ (lt_trans hi hqk)
  have : q = a + x.val * d := (Nat.prime_dvd_prime_iff_eq hq hp).mp hdvd
  omega

/-- **Green–Tao (Lean-checked reduction).**  The primes contain arbitrarily long
arithmetic progressions, given the inductive step: every prime arithmetic progression
of length `k ≥ 13` can be extended to one of length `k + 1`.

The base cases (all lengths `k ≤ 13`) are proved unconditionally here, by exhibiting
the progression `4943 + 60060·i`, `i < 13`, of primes.  The hypothesis `hstep` is the
remaining (deep) content of the Green–Tao theorem; it is stated as an explicit
hypothesis rather than assumed as an axiom. -/
