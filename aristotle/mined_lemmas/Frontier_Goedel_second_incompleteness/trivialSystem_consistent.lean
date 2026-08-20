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

theorem trivialSystem_consistent : trivialSystem.Consistent := id

/-- `⊥` is a Gödel fixed point for `trivialSystem`, so the hypotheses of the
second incompleteness theorem are jointly satisfiable. -/
