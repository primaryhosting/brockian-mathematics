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

theorem NPLang_of_PLang (F : PolyFramework) (A : ℕ → Bool) (h : PLang F A) : NPLang F A := by
  refine ⟨fun z => A (Nat.unpair z).1 && decide ((Nat.unpair z).2 = 0), 0, ?_, ?_, ?_⟩
  · have h1 : PF F (fun z => if A (Nat.unpair z).1 then 1 else 0) := F.mem_comp _ _ h F.mem_fst
    have h2 : PF F (fun z => if decide ((Nat.unpair z).2 = 0) then 1 else 0) := by
      have hle : PF F (fun z => if (Nat.unpair z).2 ≤ 0 then 1 else 0) := by
        have := F.mem_comp _ _ F.mem_le
          (F.mem_pair _ _ F.mem_snd (F.mem_const 0))
        exact Set.mem_of_eq_of_mem (by funext z; simp) this
      exact Set.mem_of_eq_of_mem (by funext z; simp) hle
    have h3 := F.mem_ite _ _ _ (F.mem_comp _ _ (F.mem_sub) (F.mem_pair _ _ (F.mem_const 1) h1))
      h2 (F.mem_const 0)
    refine Set.mem_of_eq_of_mem ?_ h3
    funext z
    by_cases hA : A (Nat.unpair z).1 = true <;> by_cases hz : (Nat.unpair z).2 = 0 <;>
      simp [hA, hz]
  · intro x y hxy
    simp only [Nat.unpair_pair, Bool.and_eq_true, decide_eq_true_eq] at hxy
    simp [hxy.2]
  · intro x
    constructor
    · intro hx
      exact ⟨0, by simp [hx]⟩
    · rintro ⟨y, hy⟩
      simp only [Nat.unpair_pair, Bool.and_eq_true] at hy
      exact hy.1

/-! ### A toolkit of closure lemmas -/

