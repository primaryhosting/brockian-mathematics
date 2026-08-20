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

theorem Adiag_NP (L : ℕ → Bool)
    (hcert : ∀ x y, F.Red vIdx (Nat.pair x y) = 1 → y ≤ 2 ^ ((Nat.size x + 2) ^ dL))
    (hLdef : ∀ x, L x = true ↔ ∃ y, F.Red vIdx (Nat.pair x y) = 1) :
    NPLang F (Adiag F vIdx dL L) := by
  refine ⟨fun z => decide (F.Red vIdx z = 1) &&
      decide (fF F vIdx dL (Nat.size (Nat.unpair z).1) % 2 = 0), dL, ?_, ?_, ?_⟩
  · have h1 : PFb F (fun z => decide (F.Red vIdx z = 1)) :=
      pfb_eq F (pf_Red F vIdx) (pf_const F 1)
    have h2 : PFb F (fun z => decide (fF F vIdx dL (Nat.size (Nat.unpair z).1) % 2 = 0)) :=
      pfb_comp F (pfb_even_fF F vIdx dL) F.mem_fst
    exact pfb_and F h1 h2
  · intro x y hxy
    simp only [Nat.unpair_pair, Bool.and_eq_true, decide_eq_true_eq] at hxy
    exact hcert x y hxy.1
  · intro x
    simp only [Nat.unpair_pair, Adiag, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hL, hp⟩
      obtain ⟨y, hy⟩ := (hLdef x).mp hL
      exact ⟨y, hy, hp⟩
    · rintro ⟨y, hy, hp⟩
      exact ⟨(hLdef x).mpr ⟨y, hy⟩, hp⟩

/-! ### Putting the two cases together -/

