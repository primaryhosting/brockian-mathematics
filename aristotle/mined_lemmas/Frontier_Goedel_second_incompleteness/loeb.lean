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

theorem Loeb (T : ProvabilitySystem)
    (hdiag : ∀ p : Formula, ∃ L : Formula,
      T.Thm (imp L (imp (box L) p)) ∧ T.Thm (imp (imp (box L) p) L))
    {p : Formula} (hp : T.Thm (imp (box p) p)) : T.Thm p := by
  obtain ⟨L, hL1, hL2⟩ := hdiag p
  have h1 : T.Thm (imp (box L) (box (imp (box L) p))) :=
    T.mp (T.D2 L (imp (box L) p)) (T.D1 hL1)
  have h2 : T.Thm (imp (box (imp (box L) p)) (imp (box (box L)) (box p))) :=
    T.D2 (box L) p
  have h3 : T.Thm (imp (box L) (box (box L))) := T.D3 L
  have h4 : T.Thm (imp (box L) (box p)) := by
    refine T.mp (T.mp (T.mp (T.taut (p := imp (imp (box L) (box (imp (box L) p)))
      (imp (imp (box (imp (box L) p)) (imp (box (box L)) (box p)))
        (imp (imp (box L) (box (box L))) (imp (box L) (box p))))) ?_) h1) h2) h3
    intro v
    simp only [eval]
    intro k1 k2 k3 hbL
    exact k2 (k1 hbL) (k3 hbL)
  have h5 : T.Thm (imp (box L) p) := Thm.trans h4 hp
  have h6 : T.Thm L := T.mp hL2 h5
  exact T.mp h5 (T.D1 h6)

/-!
## Non-vacuity

The hypotheses of the main theorem are satisfiable: the "everything is provable
according to `box`" system, in which `Thm p` means that `p` is true under the
valuation sending every atom and every boxed formula to `True`, is a consistent
provability system possessing a Gödel fixed point.  (This is the one-world
Kripke model with no accessible worlds.)  Hence the theorem below is not
vacuously true.
-/

/-- A consistent provability system: truth under the valuation making every
atomic and boxed formula true. -/
