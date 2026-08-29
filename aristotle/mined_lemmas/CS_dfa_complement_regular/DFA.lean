import Mathlib

/-!
# Dfa Complement Regular
Category: Computer Science
Target: CS.dfa_complement_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to be the very first commands in a
file, so the header comment above is placed immediately after the single `import Mathlib`
line; its text is otherwise verbatim.
-/

open Computability

namespace CS

variable {α : Type*} {σ : Type*}

/-- The complement automaton of a DFA: same transition function and start state,
but the accepting states are complemented. -/

theorem DFA.accepts_compl (M : DFA α σ) : (DFA.compl M).accepts = M.acceptsᶜ := rfl

/-- **Regular languages are closed under complement.**
If `L` is regular (accepted by some DFA with finitely many states), then so is `Lᶜ`.
The proof is by the explicit complement-automaton construction `CS.DFA.compl`.
(Mathlib also provides this as `Language.IsRegular.compl`.) -/
