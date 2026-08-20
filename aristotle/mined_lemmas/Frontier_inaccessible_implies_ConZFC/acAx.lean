/-
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
This file formalizes the statement that a (strongly) inaccessible cardinal `κ` yields a model of
`ZFC`, namely the rank-initial segment `V κ = {x : ZFSet | rank x < κ.ord}` of the von Neumann
hierarchy, and deduces the semantic consistency statement `Con(ZFC)` (i.e. satisfiability of the
first-order theory `ZFCTheory`) from the existence of an inaccessible cardinal.
-/

universe u

namespace Frontier

open FirstOrder Language Cardinal Ordinal ZFSet

/-! ## The first-order language of set theory -/

/-- The relations of the language of set theory: a single binary relation `∈`. -/
inductive memRel : ℕ → Type
  | mem : memRel 2

/-- The first-order language of set theory: one binary relation symbol, no functions. -/

def acAx : setLang.Sentence :=
  ∀' (((∀' ((memf &1 &0) ⟹ ∃' (memf &2 &1))) ⊓
        (∀' ∀' ((((memf &1 &0) ⊓ (memf &2 &0)) ⊓ ∼(&1 =' &2)) ⟹
          ∼(∃' ((memf &3 &1) ⊓ (memf &3 &2)))))) ⟹
    ∃' (∀' ((memf &2 &0) ⟹
      ∃' (((memf &3 &2) ⊓ (memf &3 &1)) ⊓
        ∀' (((memf &4 &2) ⊓ (memf &4 &1)) ⟹ (&4 =' &3))))))

section Schemas

variable {n : ℕ}

/-- The separation (subset) schema, for a formula `φ` whose free variables are `n` parameters
together with the variable being separated. -/
