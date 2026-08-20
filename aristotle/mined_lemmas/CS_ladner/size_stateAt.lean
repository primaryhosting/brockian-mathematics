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

theorem size_stateAt (n : ℕ) : Nat.size (stateAt F vIdx dL n) ≤ (n + 2) ^ 3 := by
  have hP : prP (stateAt F vIdx dL n) < 2 ^ (n + 1) := by
    rw [inv_P]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hC : prC (stateAt F vIdx dL n) < 2 ^ (n + 1) :=
    lt_of_le_of_lt (inv_C_le F vIdx dL n) (Nat.lt_two_pow_self.trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hS : prS (stateAt F vIdx dL n) < 2 ^ (n + 1) :=
    lt_of_le_of_lt (inv_S_le F vIdx dL n) (Nat.lt_two_pow_self.trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hH : prH (stateAt F vIdx dL n) < 2 ^ (n + 1) :=
    (inv_H_lt F vIdx dL n).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hz : stateAt F vIdx dL n < 2 ^ (4 * (n + 1)) := by
    have h1 := pair_lt_pow hP hC
    have h2 := pair_lt_pow hS hH
    have := pair_lt_pow h1 h2
    have he : stateAt F vIdx dL n =
        Nat.pair (Nat.pair (prP (stateAt F vIdx dL n)) (prC (stateAt F vIdx dL n)))
          (Nat.pair (prS (stateAt F vIdx dL n)) (prH (stateAt F vIdx dL n))) := by
      simp [prP, prC, prS, prH]
    rw [he]
    have h4 : 2 * (2 * (n + 1)) = 4 * (n + 1) := by ring
    rwa [h4] at this
  have := Nat.size_le.mpr hz
  refine this.trans ?_
  nlinarith [sq_nonneg n]

