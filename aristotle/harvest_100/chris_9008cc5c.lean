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
def PrimeAP (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, Nat.Prime (a + i * d)

/-- The Green–Tao theorem: the primes contain arbitrarily long arithmetic progressions. -/
def GreenTaoStatement : Prop := ∀ k : ℕ, PrimeAP k

/-- Faithfulness check: a witness for `PrimeAP k` yields a set of exactly `k` distinct
primes forming an arithmetic progression. -/
theorem primeAP_card {k : ℕ} (h : PrimeAP k) :
    ∃ a d : ℕ, 0 < d ∧ (∀ i < k, Nat.Prime (a + i * d)) ∧
      ((Finset.range k).image (fun i => a + i * d)).card = k := by
  obtain ⟨a, d, hd, hp⟩ := h
  refine ⟨a, d, hd, hp, ?_⟩
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i _ j _ hij
  simp only at hij
  exact Nat.eq_of_mul_eq_mul_right hd (by omega : i * d = j * d)

/-- Having a progression of length `k` gives progressions of all shorter lengths. -/
theorem PrimeAP.antitone {m k : ℕ} (hmk : m ≤ k) (h : PrimeAP k) : PrimeAP m := by
  obtain ⟨a, d, hd, hp⟩ := h
  exact ⟨a, d, hd, fun i hi => hp i (lt_of_lt_of_le hi hmk)⟩

/-- The explicit 13-term arithmetic progression of primes
`4943, 65003, 125063, …, 725663` (common difference `60060`). -/
theorem primeAP_thirteen : PrimeAP 13 := by
  refine ⟨4943, 60060, by norm_num, ?_⟩
  intro i hi
  interval_cases i <;> norm_num

/-- Unconditional base cases: the primes contain arithmetic progressions of every
length `k ≤ 13`. -/
theorem primeAP_of_le_thirteen {k : ℕ} (hk : k ≤ 13) : PrimeAP k :=
  PrimeAP.antitone hk primeAP_thirteen

/-- A classical structural constraint on prime arithmetic progressions: if
`a, a + d, …, a + (k-1)d` are all prime and `a ≥ k`, then every prime `q < k` divides the
common difference `d`.  (For `k = 13` this forces `2·3·5·7·11·13 = 30030 ∣ d`, consistent with
the witness `d = 60060` used above.) -/
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
theorem greenTao_iff_unbounded :
    GreenTaoStatement ↔ ∀ N : ℕ, ∃ k, N < k ∧ PrimeAP k := by
  constructor
  · intro h N
    exact ⟨N + 1, by omega, h (N + 1)⟩
  · intro h k
    obtain ⟨m, hm, hpm⟩ := h k
    exact PrimeAP.antitone hm.le hpm

end Frontier

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

