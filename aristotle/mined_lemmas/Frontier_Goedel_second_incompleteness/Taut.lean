/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-!
## The syntactic setting

We work with the standard abstract (Hilbert–Bernays–Löb) formulation of Gödel's second
incompleteness theorem.

`Fml` is a language of sentences built from atoms, falsum and implication, together with a
unary operator `box`.  For a recursively axiomatized theory `T` extending `PA`, one reads
`Fml` as (a fragment of) the sentences of arithmetic and `box p` as the arithmetized
provability sentence `Prov_T(⌜p⌝)`; the fact that `T` is recursively axiomatized and extends
`PA` is exactly what supplies the three Löb derivability conditions `D1`, `D2`, `D3` recorded
in `ProvabilitySystem` below, and the diagonal lemma supplies the Gödel fixed point.
-/

/-- Sentences: propositional atoms, falsum, implication, and a provability operator `box`. -/
inductive Fml where
  | atom : Nat → Fml
  | bot : Fml
  | imp : Fml → Fml → Fml
  | box : Fml → Fml
  deriving DecidableEq

namespace Fml

/-- Negation, `¬ p := p → ⊥`. -/

def Taut (p : Fml) : Prop := ∀ v, eval v p = true

/-- An abstract provability system: a set of theorems closed under propositional logic and
modus ponens, whose `box` operator satisfies the three Löb derivability conditions.

Any recursively axiomatized theory `T` extending `PA`, with `box` interpreted as the
arithmetized provability predicate `Prov_T`, is such a system. -/
structure ProvabilitySystem where
  /-- `Thm p` means: the theory proves the sentence `p`. -/
  Thm : Fml → Prop
  /-- The theory proves every propositional tautology. -/
  taut : ∀ p, Taut p → Thm p
  /-- The theory is closed under modus ponens. -/
  mp : ∀ {a b : Fml}, Thm (Fml.imp a b) → Thm a → Thm b
  /-- D1: provable sentences are provably provable. -/
  D1 : ∀ {a : Fml}, Thm a → Thm (Fml.box a)
  /-- D2: the provability predicate is provably closed under modus ponens. -/
  D2 : ∀ a b : Fml, Thm (Fml.imp (Fml.box (Fml.imp a b)) (Fml.imp (Fml.box a) (Fml.box b)))
  /-- D3: provable formal provability is provably provable. -/
  D3 : ∀ a : Fml, Thm (Fml.imp (Fml.box a) (Fml.box (Fml.box a)))

/-- The sentence expressing the consistency of the theory: `¬ Prov(⌜⊥⌝)`. -/
