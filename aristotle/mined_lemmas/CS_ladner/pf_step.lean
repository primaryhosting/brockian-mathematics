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

theorem pf_step : PF F (step F vIdx dL) := by
  have hP2 : PF F (fun z => 2 * prP z) := pf_mul F (pf_const F 2) (pf_prP F)
  have h1 : PF F (fun z => mkst (2 * prP z) (prC z + 1) 0 (prH z + prP z)) :=
    pf_pair F (pf_pair F hP2 (pf_add F (pf_prC F) (pf_const F 1)))
      (pf_pair F (pf_const F 0) (pf_add F (pf_prH F) (pf_prP F)))
  have h2 : PF F (fun z => mkst (2 * prP z) (prC z) (prS z + 1) (prH z)) :=
    pf_pair F (pf_pair F hP2 (pf_prC F))
      (pf_pair F (pf_add F (pf_prS F) (pf_const F 1)) (pf_prH F))
  have h3 : PF F (fun z => mkst (2 * prP z) (prC z) (prS z) (prH z)) :=
    pf_pair F (pf_pair F hP2 (pf_prC F)) (pf_pair F (pf_prS F) (pf_prH F))
  exact pf_ite F (pfb_stReady F dL) (pf_ite F (pfb_stWitness F vIdx) h1 h2) h3

/-! ### The orbit of the initial state -/

/-- Whether the machine completes a requirement at time `n`. -/
