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

theorem not_tautology_bot : ¬ Tautology ⊥' := by
  intro h
  exact (isValuation_stdVal (fun _ => True) (fun _ => True)).bot
    (h _ (isValuation_stdVal (fun _ => True) (fun _ => True)))

/-! ## Theories with a provability predicate

We axiomatize a theory by its set `Thm` of theorems, subject to the Hilbert–Bernays–Löb
derivability conditions for `box`, together with the diagonal (fixed point) lemma. -/

/-- A theory, presented by its set of theorems `Thm`, equipped with an internal provability
predicate `box` satisfying the Hilbert–Bernays–Löb derivability conditions and the diagonal
lemma.  These are the standard properties enjoyed by `Prov_T(⌜·⌝)` for a recursively
axiomatized, sufficiently strong theory `T`. -/
structure Theory : Type where
  /-- The theorems of the theory. -/
  Thm : Formula → Prop
  /-- The theory contains all propositional tautologies. -/
  taut : ∀ a : Formula, Tautology a → Thm a
  /-- The theory is closed under modus ponens. -/
  mp : ∀ a b : Formula, Thm (a ⟶ b) → Thm a → Thm b
  /-- First derivability condition (necessitation): if `a` is provable, then the theory
  proves that `a` is provable. -/
  nec : ∀ a : Formula, Thm a → Thm (□a)
  /-- Second derivability condition (internal modus ponens, axiom K). -/
  distrib : ∀ a b : Formula, Thm (□(a ⟶ b) ⟶ (□a ⟶ □b))
  /-- Third derivability condition (provable `Σ₁`-completeness, axiom 4). -/
  four : ∀ a : Formula, Thm (□a ⟶ □□a)
  /-- Diagonal (fixed point) lemma: every formula `a` has a fixed point `d` that the theory
  proves equivalent to `□d ⟶ a`. -/
  diag : ∀ a : Formula, ∃ d : Formula, Thm (d ⟶ (□d ⟶ a)) ∧ Thm ((□d ⟶ a) ⟶ d)

/-- A theory is consistent when it does not prove falsum. -/
