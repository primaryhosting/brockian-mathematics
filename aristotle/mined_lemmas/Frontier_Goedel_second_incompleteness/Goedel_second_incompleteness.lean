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

theorem Goedel_second_incompleteness (T : ProvabilitySystem) (hcon : T.Consistent)
    (G : Formula) (hG1 : T.Thm (imp G (neg (box G)))) (hG2 : T.Thm (imp (neg (box G)) G)) :
    ¬ T.Thm Con := by
  intro hC
  have key : T.Thm (imp (box G) (box bot)) := box_goedel_imp_box_bot hG1
  have h4 : T.Thm (neg (box G)) := by
    refine T.mp (T.mp (T.taut (p := imp (imp (box G) (box bot))
      (imp (neg (box bot)) (neg (box G)))) ?_) key) hC
    intro v
    simp only [eval, neg]
    intro hbb hnb hbG
    exact hnb (hbb hbG)
  exact Goedel_first_incompleteness hcon hG1 (T.mp hG2 h4)

/-- The second incompleteness theorem, stated with the diagonal lemma as an
existential hypothesis: if the theory is consistent and admits a Gödel fixed
point, it does not prove its own consistency. -/
