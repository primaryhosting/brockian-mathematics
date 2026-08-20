import Mathlib

/-!
# Complement closure for regular languages, in Mathlib's language

This file restates `CS.dfa_complement_regular` using Mathlib's `Language.IsRegular`
(defined via `DFA`s with a `Fintype` of states).
-/

universe u

namespace CS

/--
**Regular languages are closed under complement**, phrased with Mathlib's `Language.IsRegular`.

The proof is the standard DFA construction: keep the states, the start state and the transition
function of a DFA recognizing `L`, and complement its set of accepting states.

Mathlib also has this result, as `Language.IsRegular.compl` / `Language.IsRegular_compl`.
-/

theorem dfa_complement_regular_language {T : Type u} {L : Language T} (h : L.IsRegular) :
    Lᶜ.IsRegular := by
  obtain ⟨σ, hσ, M, hM⟩ := h
  -- `Mᶜ` is by definition `⟨M.step, M.start, M.acceptᶜ⟩` (`DFA.compl_def`).
  refine ⟨σ, hσ, Mᶜ, ?_⟩
  rw [DFA.accepts_compl, hM]

end CS

/-!
# Dfa Complement Regular
Category: Computer Science
Target: CS.dfa_complement_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (Lean requires `import` commands to precede any
module documentation, and the header above must be the very first thing in the file), so the
development below is self-contained: deterministic finite automata, the languages they accept,
regularity, and closure of the regular languages under complement.

A Mathlib-based version of the same statement, phrased with `Language.IsRegular`, is proved in
`RequestProject/MathlibVersion.lean` (`CS.dfa_complement_regular_language`).
-/

namespace CS

universe u v

/-- A deterministic finite automaton over the input alphabet `α` with state type `σ`:
a transition function, an initial state, and a set of accepting states. -/
structure DFA (α : Type u) (σ : Type v) where
  /-- The transition function. -/
  step : σ → α → σ
  /-- The initial state. -/
  start : σ
  /-- The set of accepting states. -/
  accept : σ → Prop

namespace DFA

variable {α : Type u} {σ : Type v}

/-- Run the automaton on a word, starting from the state `s`. -/
