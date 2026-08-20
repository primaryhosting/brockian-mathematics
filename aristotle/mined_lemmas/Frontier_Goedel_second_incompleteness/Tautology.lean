/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalize Gödel's second incompleteness theorem in its standard abstract
(Hilbert–Bernays–Löb) form: *no consistent theory `T` whose provability predicate
satisfies the derivability conditions proves its own consistency*.

The arithmetization of syntax is packaged in the usual way.  For a recursively
axiomatized theory `T` extending `PA`, Gödel numbering yields a provability
formula `Pr_T(⌜·⌝)` in the language of `T`, and the Hilbert–Bernays–Löb
derivability conditions hold:

* `D1` : `T ⊢ φ  ⟹  T ⊢ Pr_T(⌜φ⌝)`               (formalized soundness of proofs)
* `D2` : `T ⊢ Pr_T(⌜φ → ψ⌝) → (Pr_T(⌜φ⌝) → Pr_T(⌜ψ⌝))`   (internal modus ponens)
* `D3` : `T ⊢ Pr_T(⌜φ⌝) → Pr_T(⌜Pr_T(⌜φ⌝)⌝)`     (formalized `D1`)

together with closure of `T ⊢ ·` under propositional logic, and the diagonal
lemma, which produces a Gödel sentence `G` with `T ⊢ G ↔ ¬Pr_T(⌜G⌝)`.

`ProvabilitySystem` below is exactly this data: a language of formulas built from
`⊥`, `→` and the unary provability operator `box` (`box φ` denotes
`Pr_T(⌜φ⌝)`), a deducibility predicate `Thm` closed under propositional
tautologies and modus ponens, and the three derivability conditions.  The
consistency statement of `T` is the formula `Con := ¬ box ⊥`, i.e.
`¬Pr_T(⌜0=1⌝)`.

The main theorem `Frontier.Goedel_second_incompleteness` states: if `T` is
consistent and `G` is a Gödel fixed point, then `T ⊬ Con`.  We also record the
first incompleteness theorem `Frontier.Goedel_first_incompleteness`
(`T ⊬ G`) and Löb's theorem, from which the second incompleteness theorem
follows as well.
-/

namespace Frontier

/-- Formulas of the language of a theory, presented in the modal (provability
logic) signature: propositional atoms, falsity, implication, and the unary
provability operator `box p`, which stands for the arithmetized statement
"`p` is provable in `T`". -/
inductive Formula : Type
  | atom : Nat → Formula
  | bot : Formula
  | imp : Formula → Formula → Formula
  | box : Formula → Formula
  deriving DecidableEq

namespace Formula

/-- Negation, `¬p := p → ⊥`. -/

def Tautology (p : Formula) : Prop := ∀ v : Formula → Prop, eval v p

end Formula

open Formula

/-- An abstract provability system: a deducibility predicate `Thm` (read
`T ⊢ ·`) that contains all propositional tautologies, is closed under modus
ponens, and whose provability operator `box` satisfies the three
Hilbert–Bernays–Löb derivability conditions.  Any recursively axiomatized
theory extending `PA`, with `box` interpreted as its arithmetized provability
predicate, gives rise to such a system. -/
structure ProvabilitySystem where
  /-- `Thm p` means that the theory proves the formula `p`. -/
  Thm : Formula → Prop
  /-- The theory proves every propositional tautology. -/
  taut : ∀ {p : Formula}, Tautology p → Thm p
  /-- The theory is closed under modus ponens. -/
  mp : ∀ {p q : Formula}, Thm (imp p q) → Thm p → Thm q
  /-- First derivability condition: provable formulas are provably provable. -/
  D1 : ∀ {p : Formula}, Thm p → Thm (box p)
  /-- Second derivability condition: internal modus ponens. -/
  D2 : ∀ p q : Formula, Thm (imp (box (imp p q)) (imp (box p) (box q)))
  /-- Third derivability condition: internalized `D1`. -/
  D3 : ∀ p : Formula, Thm (imp (box p) (box (box p)))

namespace ProvabilitySystem

variable (T : ProvabilitySystem)

/-- The theory is consistent when it does not prove `⊥`. -/
