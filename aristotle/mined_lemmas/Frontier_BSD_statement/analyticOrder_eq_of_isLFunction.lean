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

theorem analyticOrder_eq_of_isLFunction (E : WeierstrassCurve ℤ) (L₁ L₂ : ℂ → ℂ)
    (h₁ : IsLFunction E L₁) (h₂ : IsLFunction E L₂) :
    analyticOrderAt L₁ 1 = analyticOrderAt L₂ 1 := by
  rw [LFunction_unique E L₁ L₂ h₁ h₂]

/-- **Target: a Lean-checked reduction of BSD.** Assuming the Birch–Swinnerton-Dyer
conjecture, for a minimal integral model `E` of an elliptic curve over `ℚ` and its
`L`-function `L`, the Mordell–Weil rank of `E(ℚ)` vanishes exactly when `L(E, 1) ≠ 0`
(the rank-zero, i.e. "base", case of the conjecture). -/
