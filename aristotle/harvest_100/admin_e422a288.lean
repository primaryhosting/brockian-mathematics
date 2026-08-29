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
def Con : Fml := Fml.neg (box bot)

/-- A theory is consistent if it does not derive falsity. -/
def Consistent (A : Fml → Prop) : Prop := ¬ Prov A bot

namespace Prov

variable {A : Fml → Prop} {a b c : Fml}

/-- If `b` is derivable then so is `a → b`. -/
theorem weaken (h : Prov A b) : Prov A (imp a b) := (Prov.k1 b a).mp h

/-- Distributing a hypothesis: from `a → b → c` and `a → b` infer `a → c`. -/
theorem mp_under (h₁ : Prov A (imp a (imp b c))) (h₂ : Prov A (imp a b)) :
    Prov A (imp a c) := ((Prov.k2 a b c).mp h₁).mp h₂

/-- Transitivity of implication. -/
theorem trans_imp (h₁ : Prov A (imp a b)) (h₂ : Prov A (imp b c)) : Prov A (imp a c) :=
  mp_under (weaken h₂) h₁

end Prov

/-- **Gödel's second incompleteness theorem** (abstract, Hilbert–Bernays–Löb form).

Let `A` be the axiom set of a consistent theory whose provability predicate satisfies the
derivability conditions (built into `Prov`) and for which the diagonal lemma provides a
Gödel sentence `G` with `⊢ G ↔ ¬□G` — this is the case for every consistent recursively
axiomatized theory extending `PA`.  Then the theory does not prove its own consistency
statement `Con = ¬□⊥`. -/
theorem Goedel_second_incompleteness (A : Fml → Prop)
    (hdiag : ∃ G : Fml, Prov A (imp G (Fml.neg (box G))) ∧ Prov A (imp (Fml.neg (box G)) G))
    (hcon : Consistent A) : ¬ Prov A Con := by
  intro hCon
  obtain ⟨G, hG1, hG2⟩ := hdiag
  -- `□G → □(□G → ⊥)`, by necessitating `G → (□G → ⊥)` and distributing.
  have h1 : Prov A (imp (box G) (box (imp (box G) bot))) :=
    (Prov.distrib G (imp (box G) bot)).mp hG1.nec
  -- `□(□G → ⊥) → (□□G → □⊥)`.
  have h2 : Prov A (imp (box (imp (box G) bot)) (imp (box (box G)) (box bot))) :=
    Prov.distrib (box G) bot
  -- Hence `□G → (□□G → □⊥)`.
  have h3 : Prov A (imp (box G) (imp (box (box G)) (box bot))) := Prov.trans_imp h1 h2
  -- With `□G → □□G` this gives `□G → □⊥`.
  have h4 : Prov A (imp (box G) (box bot)) := Prov.mp_under h3 (Prov.four G)
  -- Consistency `□⊥ → ⊥` then yields `¬□G`.
  have h5 : Prov A (Fml.neg (box G)) := Prov.trans_imp h4 hCon
  -- The Gödel sentence is derivable, hence so is `□G`, contradicting `¬□G`.
  have h6 : Prov A G := hG2.mp h5
  exact hcon (h5.mp h6.nec)


/-!
### Non-vacuity

The hypotheses of `Goedel_second_incompleteness` are satisfiable: below we exhibit a consistent
axiom set possessing a fixed point of `¬□·`.  Consistency is checked by the trivial
interpretation in which `□` is read as "true".
-/

/-- The interpretation of formulas in which `□a` is always true.  It validates all axioms and
rules of `Prov`, and is used to certify consistency of concrete axiom sets. -/
def triv : Fml → Prop
  | bot => False
  | imp a b => triv a → triv b
  | box _ => True

/-- Soundness of `Prov` with respect to the interpretation `triv`. -/
theorem triv_sound {A : Fml → Prop} (hA : ∀ a, A a → triv a) {f : Fml} (h : Prov A f) : triv f := by
  induction h with
  | ax ha => exact hA _ ha
  | k1 a b => exact fun ha _ => ha
  | k2 a b c => exact fun h1 h2 ha => h1 ha (h2 ha)
  | dne a => exact fun h => Classical.byContradiction h
  | distrib a b => exact fun _ _ => trivial
  | four a => exact fun _ => trivial
  | nec _ _ => trivial
  | mp _ _ ih1 ih2 => exact ih1 ih2

/-- A one-axiom theory: it asserts `¬Con`, i.e. `(¬□⊥) → ⊥`. -/
def A₀ : Fml → Prop := fun f => f = imp (Fml.neg (box bot)) bot

theorem A₀_consistent : Consistent A₀ := by
  intro h
  exact triv_sound (fun a ha => by subst ha; exact fun h => h trivial) h

/-- The hypotheses of Gödel's second incompleteness theorem are satisfiable: `A₀` is consistent
and `⊥` is a fixed point of `¬□·` over `A₀`. -/
theorem hypotheses_satisfiable :
    ∃ A : Fml → Prop, Consistent A ∧
      ∃ G : Fml, Prov A (imp G (Fml.neg (box G))) ∧ Prov A (imp (Fml.neg (box G)) G) :=
  ⟨A₀, A₀_consistent, bot, Prov.k1 bot (box bot), Prov.ax rfl⟩

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

