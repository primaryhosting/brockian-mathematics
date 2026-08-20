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

def collAx (φ : setLang.BoundedFormula Empty (n + 2)) : setLang.Sentence :=
  (∀' ((∀' ((memf (&(Fin.last (n + 1))) (&((Fin.last n).castSucc))) ⟹
      ∃' (φ.liftAt 1 n))) ⟹
    ∃' ∀' ((memf (&(Fin.last (n + 2))) (&(((Fin.last n).castSucc).castSucc))) ⟹
      ∃' (((memf (&(Fin.last (n + 3))) (&(((Fin.last (n + 1)).castSucc).castSucc)))) ⊓
        φ.liftAt 2 n)))).alls

end Schemas

/-- The first-order theory ZFC: extensionality, foundation, pairing, union, power set, infinity,
choice, together with the separation and collection schemas. (Separation and collection together
are deductively equivalent to the usual separation and replacement schemas.) -/
