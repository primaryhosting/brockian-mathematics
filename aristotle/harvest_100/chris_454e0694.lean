/-
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter

namespace Frontier

/-- `primeGap n = p_{n+1} - p_n`, where `p_n = Nat.nth Nat.Prime n` is the `n`-th prime
(so `p_0 = 2`, `p_1 = 3`, ...). -/
noncomputable def primeGap (n : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- The Zhang–Maynard statement: the `liminf` of the prime gaps is finite.

The `liminf` is taken in `ℕ∞ = WithTop ℕ`, so that "finite" is faithfully expressed as `≠ ⊤`.
(Taking the `liminf` inside `ℕ` itself would be meaningless: `ℕ` is only conditionally
complete, so an unbounded supremum returns the junk value `0` and finiteness would hold
vacuously.) -/
noncomputable def BoundedPrimeGaps : Prop :=
  Filter.liminf (fun n => (primeGap n : ℕ∞)) Filter.atTop ≠ ⊤

/-- Every prime gap is positive: `p_n < p_{n+1}`. -/
theorem primeGap_pos (n : ℕ) : 0 < primeGap n := by
  have h : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
    (Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr (by omega)
  unfold primeGap
  omega

/-- **Reduction for bounded prime gaps.**  Finiteness of `liminf (p_{n+1} - p_n)` — the
Zhang–Maynard theorem — is equivalent to the existence of a bound `B` such that infinitely
many pairs of consecutive primes differ by at most `B`.

The unconditional truth of either side is Zhang's theorem (refined by Maynard and Tao), which
is not available in Mathlib; what is proved here is the Lean-checked equivalence of the two
standard formulations of the statement.  The Mathlib ingredients are
`Filter.liminf_le_of_frequently_le` and `Filter.liminf_eq` (`liminf` as a supremum). -/
theorem bounded_prime_gaps :
    BoundedPrimeGaps ↔ ∃ B : ℕ, ∀ N : ℕ, ∃ n, N ≤ n ∧ primeGap n ≤ B := by
  constructor
  · intro h
    unfold BoundedPrimeGaps at h
    set L := Filter.liminf (fun n => (primeGap n : ℕ∞)) Filter.atTop with hL
    refine ⟨L.untop h, ?_⟩
    set B : ℕ := L.untop h with hB
    have hLB : L = (B : ℕ∞) := (WithTop.coe_untop L h).symm
    by_contra hcon
    push_neg at hcon
    obtain ⟨N, hN⟩ := hcon
    have hle : ((B : ℕ∞) + 1) ≤ L := by
      rw [hL, Filter.liminf_eq]
      refine le_sSup ?_
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have h1 : B + 1 ≤ primeGap n := hN n hn
      have h2 : (((B + 1 : ℕ)) : ℕ∞) ≤ ((primeGap n : ℕ) : ℕ∞) := by exact_mod_cast h1
      simpa using h2
    rw [hLB] at hle
    have : (B + 1 : ℕ) ≤ B := by exact_mod_cast hle
    omega
  · rintro ⟨B, hB⟩
    have hfreq : ∃ᶠ n in Filter.atTop, ((primeGap n : ℕ∞)) ≤ (B : ℕ∞) := by
      rw [Filter.frequently_atTop]
      intro N
      obtain ⟨n, hn, h⟩ := hB N
      exact ⟨n, hn, by exact_mod_cast h⟩
    have hle := Filter.liminf_le_of_frequently_le hfreq
    intro hcon
    rw [hcon] at hle
    exact (ENat.coe_ne_top B) (top_le_iff.mp hle)

/-- If `p ≠ 2` and both `p` and `p + 2` are prime, then they are consecutive primes: with
`n = Nat.count Nat.Prime p` we have `p_n = p`, `p_{n+1} = p + 2`, hence `primeGap n = 2`. -/
theorem primeGap_count_eq_two_of_twin {p : ℕ} (hp : p.Prime) (hp2 : (p + 2).Prime)
    (hne : p ≠ 2) : primeGap (Nat.count Nat.Prime p) = 2 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hne)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hnp1 : ¬ (p + 1).Prime := by
    intro h
    have hdvd : 2 ∣ (p + 1) := by omega
    rcases h.eq_one_or_self_of_dvd 2 hdvd with h' | h' <;> omega
  have hcount : Nat.count Nat.Prime (p + 2) = Nat.count Nat.Prime p + 1 := by
    rw [show p + 2 = (p + 1) + 1 from rfl, Nat.count_succ, Nat.count_succ]
    simp [hp, hnp1]
  have h1 : Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
  have h2 : Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) = p + 2 := by
    rw [← hcount]; exact Nat.nth_count hp2
  unfold primeGap
  rw [h1, h2]
  omega

/-- **Conditional reduction:** the twin prime conjecture implies bounded prime gaps, with the
explicit bound `B = 2`. -/
theorem boundedPrimeGaps_of_twin_prime_conjecture
    (H : ∀ M : ℕ, ∃ p, M ≤ p ∧ p.Prime ∧ (p + 2).Prime) : BoundedPrimeGaps := by
  rw [bounded_prime_gaps]
  refine ⟨2, fun N => ?_⟩
  obtain ⟨p, hpM, hp, hp2⟩ := H (max 3 (Nat.nth Nat.Prime N + 1))
  have hp3 : 3 ≤ p := le_trans (le_max_left _ _) hpM
  have hpN : Nat.nth Nat.Prime N < p := by
    have := le_trans (le_max_right 3 (Nat.nth Nat.Prime N + 1)) hpM
    omega
  refine ⟨Nat.count Nat.Prime p, ?_,
    le_of_eq (primeGap_count_eq_two_of_twin hp hp2 (by omega))⟩
  by_contra hlt
  push_neg at hlt
  have hcontra : Nat.nth Nat.Prime (Nat.count Nat.Prime p) < Nat.nth Nat.Prime N :=
    (Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr hlt
  rw [Nat.nth_count hp] at hcontra
  omega

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

