/-!
# Loeb No Self Trust
Category: Frontier Mind
Target: Frontier.loeb_no_self_trust
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-! ## The language

We work in the language of propositional provability logic: propositional atoms, falsum,
implication, and a unary modality `box`, which is read as the arithmetized provability
predicate `Prov(⌜·⌝)` of the theory under consideration. -/

/-- Formulas of the language of provability logic. `Formula.box a` is read as the formal
sentence `Prov(⌜a⌝)`, i.e. "`a` is provable in the theory". -/
inductive Formula : Type
  /-- A propositional atom. -/
  | atom : Nat → Formula
  /-- Falsum. -/
  | bot : Formula
  /-- Implication. -/
  | imp : Formula → Formula → Formula
  /-- The provability modality `Prov(⌜·⌝)`. -/
  | box : Formula → Formula

@[inherit_doc] scoped infixr:26 " ⟶ " => Formula.imp
@[inherit_doc] scoped prefix:max "□" => Formula.box
/-- Falsum. -/
scoped notation "⊥'" => Formula.bot

/-! ## Propositional (tautological) consequence

A *valuation* is any assignment of truth values to formulas that treats falsum and
implication classically; atoms and boxed formulas may receive arbitrary truth values.  A
formula is a *tautology* when it is true under every valuation; these are exactly the
formulas that are substitution instances of propositional tautologies in the modal
language. -/

/-- `v` respects the classical meaning of falsum and implication. -/
structure IsValuation (v : Formula → Prop) : Prop where
  /-- Falsum is false. -/
  bot : ¬ v ⊥'
  /-- Implication is material implication. -/
  imp : ∀ a b : Formula, v (a ⟶ b) ↔ (v a → v b)

/-- A formula is a tautology if it holds under every valuation. -/

theorem no_uniform_reflection (T : Theory) (hcon : T.Consistent) :
    ¬ (∀ a : Formula, T.Thm (T.reflection a)) := fun h => hcon (T.loeb ⊥' (h ⊥'))

/-- A concrete instance of `Frontier.loeb_no_self_trust`: a consistent theory does not prove
the reflection principle for falsum, i.e. it does not prove its own consistency statement
`Prov(⌜⊥⌝) → ⊥`.  (Gödel's second incompleteness theorem, in its Löb-derived form.) -/
