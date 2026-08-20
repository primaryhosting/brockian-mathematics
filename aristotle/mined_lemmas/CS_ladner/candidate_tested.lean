/-
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean does not allow a module docstring before `import`; the header is repeated verbatim
-- as the module docstring immediately below the imports.)
import Mathlib

/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
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

/-!
## Overview

We prove Ladner's theorem: *if `P ≠ NP` then there is an NP-intermediate language*, i.e. a
language in `NP` which is neither in `P` nor `NP`-complete.

Complexity theory is not available in Mathlib, so the development is carried out over an
explicit abstract model of polynomial time computation, packaged as the structure
`PolyFramework` below.  Strings are encoded as natural numbers, the *size* (bit length) of a
string `x` being `Nat.size x`, and a *language* is a function `ℕ → Bool`.

A `PolyFramework` consists of an enumeration `Red : ℕ → ℕ → ℕ` of the polynomial time
computable functions (`Red e` is the function computed by the `e`-th polynomial time program),
together with a degree function `deg` (`Red e` runs in time `(size x + 2) ^ deg e`), subject to
the standard closure properties of polynomial time:  closure under composition, pairing,
conditionals, basic arithmetic, bit counting, *clocked universal simulation* (running a program
with a unary time budget is polynomial), *bounded search* (searching a unary sized range for a
certificate is polynomial) and *iteration* (iterating a polynomial time function a unary number
of times, along an orbit whose sizes stay polynomially bounded, is polynomial).

All of these are standard true facts about polynomial time; they are taken as the hypotheses of
the theorem rather than as Lean `axiom`s, so the final result is axiom clean.
-/

namespace Ladner

/-- The number of set bits of `h` at positions `< m`. -/

theorem candidate_tested (n₀ c : ℕ) (hstab : ∀ n, n₀ ≤ n → prC (stateAt F vIdx dL n) = c)
    (hnoj : ∀ n, n₀ ≤ n → jmp F vIdx dL n = false) (hs0 : prS (stateAt F vIdx dL n₀) = 0) :
    ∀ x, ∃ n, n₀ ≤ n ∧ prS (stateAt F vIdx dL n) = x ∧
      stReady F dL (stateAt F vIdx dL n) = true := by
  intro x
  induction x with
  | zero =>
      obtain ⟨m, hm, hr, hS⟩ := ready_with_same_S F vIdx dL n₀ c hstab n₀ le_rfl
      exact ⟨m, le_trans le_rfl hm, by rw [hS, hs0], hr⟩
  | succ x ih =>
      obtain ⟨n, hn, hSn, hr⟩ := ih
      have hw : stWitness F vIdx (stateAt F vIdx dL n) = false := by
        have := hnoj n hn
        rw [jmp, hr] at this
        simpa using this
      have hnext : prS (stateAt F vIdx dL (n + 1)) = x + 1 := by
        rw [stateAt_succ, step_prS, if_pos hr, if_neg (by simp [hw]), hSn]
      obtain ⟨m, hm, hr', hS'⟩ := ready_with_same_S F vIdx dL n₀ c hstab (n + 1) (by omega)
      exact ⟨m, by omega, by rw [hS', hnext], hr'⟩

/-- If the machine gets stuck on an even requirement, the corresponding program decides the
diagonal language. -/
