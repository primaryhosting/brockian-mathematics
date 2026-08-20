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

theorem eventually_readyO (c s : ℕ) : ∃ N : ℕ, ∀ n, N ≤ n →
    ∀ z, prC z = c → prS z = s → prP z = 2 ^ n → readyO F dL z = true := by
  set e := c / 2 with he
  set y := F.Red e s with hy
  set K := max (max ((Nat.size s + 2) ^ F.deg e) ((Nat.size s + 2) ^ dL + 1))
    (max (Nat.size s + 1) (max ((Nat.size y + 2) ^ dL + 1) (Nat.size y + 1))) with hK
  refine ⟨2 ^ K, fun n hn z hc hs hp => ?_⟩
  have hsize : Nat.size (prP z) = n + 1 := by rw [hp, Nat.size_pow]
  have hKn : K ≤ n + 1 := le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (by omega)
  have hK2 : K < Nat.size (Nat.size (prP z)) := by
    rw [hsize]
    refine Nat.lt_size.mpr ?_
    omega
  have hmv : mval F z = y + 1 := by
    rw [mval, simval, hc, hs, ← he, hsize, if_pos (by omega), hy]
  have h1 : mval F z ≠ 0 := by omega
  have h2 : bready dL (prS z) (prP z) = true := by
    rw [bready, hs]
    simp only [decide_eq_true_eq]
    omega
  have h3 : Nat.size (prS z) + 1 ≤ Nat.size (prP z) := by
    rw [hs, hsize]; omega
  have hyv : yval F z = y := by rw [yval, hmv]; omega
  have h4 : bready dL (yval F z) (prP z) = true := by
    rw [bready, hyv]
    simp only [decide_eq_true_eq]
    omega
  have h5 : Nat.size (yval F z) + 1 ≤ Nat.size (prP z) := by
    rw [hyv, hsize]; omega
  simp [readyO, readyE, h1, h2, h3, h4, h5]

