import Mathlib

/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
## Overview

We formalise the statement of the Birch–Swinnerton-Dyer conjecture (rank part) for an
elliptic curve over `ℚ`, given by a minimal integral Weierstrass model `E`:

  `ord_{s=1} L(E, s) = rank E(ℚ)`.

* The *analytic* side is the order of vanishing at `s = 1` of any entire function `L`
  which agrees with the Dirichlet series `∑ a_n n^{-s}` on the half plane `Re s > 3/2`
  (where that series converges); the coefficients `a_n` are built from the point counts
  of the reductions `E mod p` in the usual way.
* The *algebraic* side is the Mordell–Weil rank, i.e. the `ℚ`-dimension of
  `ℚ ⊗_ℤ E(ℚ)`.

The statement is well posed: by the identity theorem, an entire continuation of the
Dirichlet series is unique (`Frontier.LFunction_unique`), so the analytic order of
vanishing does not depend on the choice of `L`
(`Frontier.analyticOrder_eq_of_isLFunction`).

The target theorem `Frontier.BSD_statement` is a Lean-checked reduction: assuming the
conjecture, we derive the classical rank-zero criterion
`L(E, 1) ≠ 0 ↔ rank E(ℚ) = 0`.
-/

namespace Frontier

open WeierstrassCurve

/-- The trace of Frobenius at `p` for the integral Weierstrass model `E`, defined as
`a_p = p + 1 - #E_ns(𝔽_p)`, where `E_ns(𝔽_p)` is the group of nonsingular points of the
reduction of `E` modulo `p` (this is the usual `a_p` for good primes, and gives
`1`, `-1`, `0` at primes of split multiplicative, nonsplit multiplicative and additive
reduction respectively, provided the model is minimal). -/

theorem BSD_statement (hBSD : BSD_conjecture) (E : WeierstrassCurve ℤ) (hΔ : E.Δ ≠ 0)
    (hmin : IsMinimalModel E) (L : ℂ → ℂ) (hL : IsLFunction E L) :
    L 1 ≠ 0 ↔ mordellWeilRank E = 0 := by
  have hord : analyticOrderAt L 1 = (mordellWeilRank E : ℕ∞) := hBSD E hΔ hmin L hL
  have hana : AnalyticAt ℂ L 1 := hL.1 (1 : ℂ) (Set.mem_univ _)
  constructor
  · intro hne
    have : analyticOrderAt L 1 = 0 := analyticOrderAt_eq_zero.2 (Or.inr hne)
    rw [hord] at this
    exact_mod_cast this
  · intro hrank
    rw [hrank] at hord
    have : ¬ AnalyticAt ℂ L 1 ∨ L 1 ≠ 0 := analyticOrderAt_eq_zero.1 (by exact_mod_cast hord)
    rcases this with h | h
    · exact absurd hana h
    · exact h

end Frontier

