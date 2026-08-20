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

def accepts (M : DFA α σ) (w : List α) : Prop := M.accept (M.eval w)

end DFA

/-- A language over the alphabet `α`, viewed as a predicate on words. -/
