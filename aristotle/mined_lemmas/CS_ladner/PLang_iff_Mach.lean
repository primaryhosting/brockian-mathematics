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

theorem PLang_iff_Mach (A : ℕ → Bool) :
    PLang F A ↔ ∃ e, ∀ x, A x = decide (F.Red e x = 1) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, fun x => ?_⟩
    have : F.Red e x = if A x then 1 else 0 := congrFun he x
    rw [this]
    by_cases hx : A x = true <;> simp [hx]
  · rintro ⟨e, he⟩
    have : PF F (fun x => if decide (F.Red e x = 1) then 1 else 0) :=
      pf_ite F (pfb_eq F (pf_Red F e) (pf_const F 1)) (pf_const F 1) (pf_const F 0)
    refine pf_congr this ?_
    funext x
    rw [he x]

/-- `P` is closed under finite modifications. -/
