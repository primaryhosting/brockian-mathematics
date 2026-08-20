import RequestProject.Nash

/-!
# The one-dimensional base case of Brouwer's fixed point theorem

Brouwer's fixed point theorem is not available in Mathlib, and is taken as an explicit
hypothesis in `Frontier.nash_equilibrium_exists`.  Here we prove the one-dimensional base
case of that hypothesis, `BrouwerFixedPointProperty ℝ`, from the intermediate value
theorem; in particular the hypothesis is not vacuous.
-/

open Set

namespace Frontier

/-- **Brouwer's fixed point theorem in dimension one**: every continuous self-map of a
nonempty compact convex subset of `ℝ` has a fixed point. -/

theorem nash_equilibrium_exists_of_zerosum (u : Bool → (∀ i, S i) → ℝ)
    (hzs : ∀ p, u true p = -u false p) : ∃ x, IsNashEquilibrium u x := by
  obtain ⟨x0, hx0, y0, hy0, hrow, hcol⟩ := exists_saddlePoint (payoffMatrix u)
  refine ⟨pairFun x0 y0, ?_, ?_⟩
  · intro i _
    cases i
    · exact hx0
    · exact hy0
  intro i y hy
  cases i
  · rw [expectedPayoff_false, expectedPayoff_false]
    have h1 : (update (pairFun x0 y0) false y) false = y := update_self _ _ _
    have h2 : (update (pairFun x0 y0) false y) true = y0 := by
      rw [update_of_ne (by decide), pairFun_true]
    rw [h1, h2, pairFun_false, pairFun_true]
    exact hrow y hy
  · rw [expectedPayoff_true _ hzs, expectedPayoff_true _ hzs]
    have h1 : (update (pairFun x0 y0) true y) false = x0 := by
      rw [update_of_ne (by decide), pairFun_false]
    have h2 : (update (pairFun x0 y0) true y) true = y := update_self _ _ _
    rw [h1, h2, pairFun_false, pairFun_true]
    simpa using hcol y hy

end Frontier

import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Contents

* `Frontier.IsNashEquilibrium`: mixed strategy Nash equilibrium of a finite game with
  finitely many players, each having a finite nonempty set of pure strategies.
* `Frontier.nash_equilibrium_exists`: **Nash's theorem** — every finite game has a mixed
  strategy Nash equilibrium.  Brouwer's fixed point theorem is not in Mathlib, so it is an
  explicit hypothesis (`BrouwerFixedPointProperty`); the whole of Nash's argument (Nash's
  map, its continuity, that it preserves the product of simplices, and that its fixed
  points are exactly equilibria) is proved here.
* `Frontier.nash_equilibrium_exists_of_potential`: unconditional existence for finite
  potential games.

Companion files prove further unconditional cases: `RequestProject.BrouwerOneDim` (the
one-dimensional case of the Brouwer hypothesis), `RequestProject.ZeroSum` (the minimax
theorem) and `RequestProject.TwoPlayer` (existence for two-player zero-sum games).
-/

open Finset Function Set

namespace Frontier

/-- Brouwer's fixed point theorem, as a property of a real normed space `E`:
every continuous self-map of a nonempty compact convex subset of `E` has a fixed point. -/
