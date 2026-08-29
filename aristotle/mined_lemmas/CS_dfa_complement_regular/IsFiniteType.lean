/-!
# Dfa Complement Regular
Category: Computer Science
Target: CS.dfa_complement_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file structure: in Lean 4 an `import` command must be the very first command of a
file, and a `/-! ... -/` module documentation block already counts as a command.  Since the
file is required to begin with the header block above, this module is written to be fully
self-contained: it develops deterministic finite automata, regular languages and the
complement construction from first principles, using nothing beyond Lean's core `Init`
library.  A companion module, `RequestProject.DfaComplementRegularMathlib`, states and proves
the same closure result for Mathlib's `Language.IsRegular`.
-/

set_option autoImplicit false

universe u v

namespace CS

/-- A language over the alphabet `α` is a predicate on words (finite lists of letters). -/

def IsFiniteType (σ : Type) : Prop := ∃ l : List σ, ∀ s : σ, s ∈ l

/-- A language is regular when it is the language of some automaton with finitely many
states. -/
