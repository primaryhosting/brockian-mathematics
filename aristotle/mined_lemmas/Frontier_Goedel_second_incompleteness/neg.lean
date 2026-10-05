/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The statement "no consistent recursively axiomatized theory extending `PA` proves its own
consistency" is formalized here in the standard abstract (Hilbert–Bernays–Löb) way.

For a recursively axiomatized theory `T ⊇ PA` one has an arithmetized provability predicate
`Pr_T(⌜·⌝)`, written here as the modality `□`.  The two ingredients supplied by the
arithmetization are:

* the *derivability conditions*: `T ⊢ a → T ⊢ □a` (necessitation), `T ⊢ □(a → b) → (□a → □b)`
  (distribution) and `T ⊢ □a → □□a` (provable Σ₁-completeness);
* the *diagonal lemma*: there is a sentence `G` with `T ⊢ G ↔ ¬□G`.

Both are packaged below: the derivability conditions as the inference system `Prov`, and the
diagonal lemma as an explicit hypothesis `hdiag` of the main theorem.  Everything else — the
implication from consistency of `T` to the unprovability of the consistency statement
`Con_T = ¬□⊥` — is proved here from scratch inside the calculus.

`Prov A` is a *sublogic* of provability in any classical theory `T` whose axiom set is `A`
(all of its axioms and rules are correct for `T ⊢ ·` and `Pr_T`), so the unprovability
conclusion transfers to such theories.
-/

namespace Frontier

/-- Sentences of the language: falsity, implication, and the provability modality `□`. -/
inductive Fml : Type
  | bot : Fml
  | imp : Fml → Fml → Fml
  | box : Fml → Fml
  deriving DecidableEq

namespace Fml

/-- Negation, `¬a := a → ⊥`. -/

def neg (a : Fml) : Fml := imp a bot

end Fml

open Fml

/-- Derivability from an axiom set `A`: classical propositional logic together with the
Hilbert–Bernays–Löb derivability conditions for the provability modality `□`. -/
inductive Prov (A : Fml → Prop) : Fml → Prop
  /-- Axioms of the theory. -/
  | ax {a : Fml} : A a → Prov A a
  /-- Propositional axiom `a → (b → a)`. -/
  | k1 (a b : Fml) : Prov A (imp a (imp b a))
  /-- Propositional axiom `(a → b → c) → (a → b) → (a → c)`. -/
  | k2 (a b c : Fml) :
      Prov A (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- Double negation elimination, making the propositional part classical. -/
  | dne (a : Fml) : Prov A (imp (imp (imp a bot) bot) a)
  /-- Second derivability condition: `□(a → b) → (□a → □b)`. -/
  | distrib (a b : Fml) : Prov A (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Third derivability condition: `□a → □□a`. -/
  | four (a : Fml) : Prov A (imp (box a) (box (box a)))
  /-- First derivability condition (necessitation): if `a` is provable, so is `□a`. -/
  | nec {a : Fml} : Prov A a → Prov A (box a)
  /-- Modus ponens. -/
  | mp {a b : Fml} : Prov A (imp a b) → Prov A a → Prov A b

/-- The consistency statement of the theory: `¬□⊥`. -/
