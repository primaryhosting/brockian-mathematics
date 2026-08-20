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

def evalFrom (M : DFA α σ) : σ → List α → σ
  | s, [] => s
  | s, a :: w => M.evalFrom (M.step s a) w

/-- Run the automaton on a word, starting from its initial state. -/
