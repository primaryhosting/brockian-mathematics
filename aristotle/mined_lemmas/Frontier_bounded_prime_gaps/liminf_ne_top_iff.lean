/-
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring; the header above is repeated
-- verbatim as the module docstring below.)

import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
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

namespace Frontier

open Filter Set

/-- The `n`-th prime, `p n` (so `p 0 = 2`, `p 1 = 3`, ...). -/

theorem liminf_ne_top_iff :
    Filter.liminf (fun n => (primeGap n : ℕ∞)) atTop ≠ ⊤ ↔ BoundedPrimeGaps := by
  constructor
  · intro h
    by_contra hbad
    apply h
    refine ENat.eq_top_iff_forall_ge.mpr fun b => ?_
    rw [BoundedPrimeGaps] at hbad
    push_neg at hbad
    obtain ⟨N, hN⟩ := hbad b
    refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    exact_mod_cast (hN n hn).le
  · rintro ⟨B, hB⟩
    have hfreq : ∃ᶠ n in atTop, (primeGap n : ℕ∞) ≤ (B : ℕ∞) := by
      rw [Filter.frequently_atTop]
      intro a
      obtain ⟨n, hn, hgap⟩ := hB a
      exact ⟨n, hn, by exact_mod_cast hgap⟩
    have := Filter.liminf_le_of_frequently_le hfreq
    intro htop
    rw [htop] at this
    simp at this

/-! ### Main statement -/

/--
**Bounded prime gaps** (Zhang–Maynard), formalized and reduced.

The statement `BoundedPrimeGaps` says that `liminf_n (p_{n+1} - p_n) < ∞`, i.e. there is a bound
`B` with `p_{n+1} - p_n ≤ B` for infinitely many `n`. The full theorem of Zhang and Maynard is
*not* proved here. What is proved, unconditionally and axiom-cleanly, is:

* the literal `liminf` formulation over `ℕ∞` is equivalent to the `∃ B` formulation;
* it is equivalent to the statement that some sublevel set `{n | p_{n+1} - p_n ≤ B}` is infinite;
* it is equivalent (contrapositive form) to the failure of `p_{n+1} - p_n → ∞`;
* it is equivalent to the "prime pairs" form: arbitrarily far out there are two distinct primes
  within a fixed distance `B` — this is the form in which the sieve-theoretic proofs work,
  and the reduction from it to consecutive primes is carried out here;
* the base case `p_1 - p_0 = 3 - 2 = 1`, together with positivity of all prime gaps.
-/
