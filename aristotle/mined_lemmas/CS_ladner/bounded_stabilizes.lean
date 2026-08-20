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

theorem bounded_stabilizes (hb : ∃ B, ∀ n, fF F vIdx dL n ≤ B) :
    ∃ n₀ c, (∀ n, n₀ ≤ n → prC (stateAt F vIdx dL n) = c) ∧
      (∀ n, n₀ ≤ n → jmp F vIdx dL n = false) ∧ prS (stateAt F vIdx dL n₀) = 0 := by
  classical
  obtain ⟨B, hB⟩ := hb
  set S : Set ℕ := Set.range (fF F vIdx dL) with hS
  have hne : S.Nonempty := ⟨fF F vIdx dL 0, ⟨0, rfl⟩⟩
  have hbdd : BddAbove S := ⟨B, by rintro _ ⟨n, rfl⟩; exact hB n⟩
  have hmem : sSup S ∈ S := Nat.sSup_mem hne hbdd
  obtain ⟨m, hm⟩ := hmem
  set c := sSup S with hc
  have hex : ∃ n, fF F vIdx dL n = c := ⟨m, hm⟩
  set n₀ := Nat.find hex with hn₀
  have hfn₀ : fF F vIdx dL n₀ = c := Nat.find_spec hex
  have hconst : ∀ n, n₀ ≤ n → fF F vIdx dL n = c := by
    intro n hn
    have h1 : fF F vIdx dL n₀ ≤ fF F vIdx dL n := fF_mono F vIdx dL hn
    have h2 : fF F vIdx dL n ≤ c := le_csSup hbdd ⟨n, rfl⟩
    omega
  refine ⟨n₀, c, fun n hn => hconst n hn, fun n hn => ?_, ?_⟩
  · have h1 := hconst n hn
    have h2 := hconst (n + 1) (by omega)
    have := fF_succ F vIdx dL n
    by_cases hj : jmp F vIdx dL n = true
    · rw [hj] at this; simp at this; omega
    · simpa using hj
  · rcases Nat.eq_zero_or_pos n₀ with h | h
    · rw [h]; simp [stateAt, s0]
    · obtain ⟨k, hk⟩ : ∃ k, n₀ = k + 1 := ⟨n₀ - 1, by omega⟩
      have hlt : fF F vIdx dL k ≠ c := by
        rw [hn₀] at hk
        exact Nat.find_min hex (by omega)
      have hjk : jmp F vIdx dL k = true := by
        have := fF_succ F vIdx dL k
        rw [← hk, hfn₀] at this
        by_cases hj : jmp F vIdx dL k = true
        · exact hj
        · rw [if_neg (by simpa using hj)] at this; omega
      rw [hk, stateAt_succ, step_prS]
      rw [jmp] at hjk
      simp at hjk
      simp [hjk.1, hjk.2]

/-- While no test is affordable, the candidate counter does not move. -/
