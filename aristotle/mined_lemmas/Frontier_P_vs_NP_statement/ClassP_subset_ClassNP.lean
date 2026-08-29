import Mathlib

/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
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

namespace Frontier

/-! ## Words and tapes

Languages are sets of finite binary strings.  Machines work on a one-sided-infinite-free,
two-way infinite tape over the alphabet `Option Bool`, where `none` is the blank symbol.
We reuse Mathlib's `Turing.Tape` for the tape datatype. -/

/-- A binary word: the inputs of our machines. -/
abbrev Word : Type := List Bool

/-- The tape alphabet: `none` is the blank symbol, `some b` is the bit `b`. -/
abbrev Alph : Type := Option Bool

/-- The initial tape holding the input word `x`, with the head on its first cell. -/

theorem ClassP_subset_ClassNP : ClassP ⊆ ClassNP := by
  rintro L ⟨M, c, k, hM⟩
  exact ⟨M.toNTM, c, k, fun x => (hM x).trans ⟨DTM.toNTM_acceptsIn, fun h => by
    obtain ⟨s, hs, path, h0, hstep, hacc⟩ := h
    refine ⟨s, hs, ?_⟩
    have key : ∀ i ≤ s, path i = M.step^[i] (M.init x) := by
      intro i hi
      induction i with
      | zero => simpa [DTM.init, NTM.init, DTM.toNTM] using h0
      | succ n ih =>
          obtain ⟨r, hr, hpath⟩ := hstep n (by omega)
          rw [hpath, ih (by omega), Function.iterate_succ_apply']
          have : r = M.δ (M.step^[n] (M.init x)).1 (M.step^[n] (M.init x)).2.head := by
            have := hr
            simp only [DTM.toNTM, Set.mem_singleton_iff] at this
            rw [this, ih (by omega)]
          rw [this]
          rfl
    rw [← key s le_rfl]
    exact hacc⟩⟩

/-- **The P vs NP problem.**

`P ≠ NP` — the assertion that the classes of languages decidable in deterministic
polynomial time and acceptable in nondeterministic polynomial time differ — is equivalent
to the existence of a language which is accepted by some polynomially time-bounded
nondeterministic Turing machine but is decided by no polynomially time-bounded
deterministic Turing machine.

This theorem records the precise statement of the open problem (whose truth value is *not*
settled here) in the two standard equivalent forms; the equivalence itself follows from
`ClassP ⊆ ClassNP`. -/
