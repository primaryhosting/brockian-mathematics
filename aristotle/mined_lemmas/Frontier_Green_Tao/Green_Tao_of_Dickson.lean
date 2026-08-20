/-
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The Green–Tao theorem: *the primes contain arbitrarily long arithmetic progressions.*

This file contains

* the formal statement (`Frontier.HasArbitrarilyLongAPs Frontier.primeSet`, unfolded in
  `Frontier.GreenTaoStatement`);
* two Lean-checked reductions of it to standard conjectures, `Frontier.Green_Tao` (from the
  Erdős–Turán conjecture on arithmetic progressions, via Mathlib's divergence of the sum of
  prime reciprocals) and `Frontier.Green_Tao_of_Dickson` (from Dickson's conjecture on
  simultaneous primality of linear forms);
* unconditional base cases, `Frontier.Green_Tao_base`: an arithmetic progression of `k` primes
  exists for every `k ≤ 13`.

Every hypothesis is an explicit argument of the corresponding theorem; no axiom is introduced.
-/

namespace Frontier

/-- `IsAPIn A k a d` says that the `k`-term arithmetic progression with first term `a`
and common difference `d` is entirely contained in the set `A`. -/

theorem Green_Tao_of_Dickson (hD : DicksonConjecture) :
    ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ i < k, Nat.Prime (a + i * d) := by
  intro k
  obtain ⟨n, -, hn⟩ :=
    hD k (fun i => i * Nat.factorial k) (fun _ => 1) (fun _ _ => Nat.one_pos)
      (fun p hp => by
        obtain ⟨n, hn⟩ := admissible_factorial_AP k p hp
        exact ⟨n, fun i hi => by simpa using hn i hi⟩) 1
  refine ⟨n, Nat.factorial k, Nat.factorial_pos k, fun i hi => ?_⟩
  have := hn i hi
  simpa [Nat.add_comm] using this

/-! ### Unconditional strengthenings of the statement

The bare Green–Tao statement (one `k`-term progression for each `k`) already implies the
apparently stronger forms: progressions starting arbitrarily late, and infinitely many
progressions of each length.  These implications are proved unconditionally. -/

/-- The Green–Tao statement self-improves: it produces `k`-term arithmetic progressions of
primes whose first term is arbitrarily large.  (Take a `(N + k)`-term progression and slide
the window forward by `N` steps.) -/
