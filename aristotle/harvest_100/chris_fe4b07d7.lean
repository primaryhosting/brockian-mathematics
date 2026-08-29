/-
# Loeb No Self Trust
Category: Frontier Mind
Target: Frontier.loeb_no_self_trust
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Loeb No Self Trust
Category: Frontier Mind
Target: Frontier.loeb_no_self_trust
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/--
An abstract *provability system*: a theory `T` together with a provability predicate
`box` (read `box a` as the sentence "`a` is provable in `T`", i.e. `Prov(⌜a⌝)`).

The data and axioms are exactly the standard ingredients of the Hilbert–Bernays–Löb
analysis of self-reference:

* `Sentence`, `imp`: the sentences of the language, with an implication connective;
* `Thm`: the theorems of `T` (`Thm a` means `T ⊢ a`);
* `mp`, `ax_K1`, `ax_K2`: `T` contains the implicational fragment of propositional
  logic (the axiom schemas `a → (b → a)` and `(a → (b → c)) → ((a → b) → (a → c))`)
  and is closed under modus ponens;
* `nec` (**D1**): if `T ⊢ a` then `T ⊢ Prov(⌜a⌝)`;
* `ax_distr` (**D2**): `T ⊢ Prov(⌜a → b⌝) → (Prov(⌜a⌝) → Prov(⌜b⌝))`;
* `ax_four` (**D3**): `T ⊢ Prov(⌜a⌝) → Prov(⌜Prov(⌜a⌝)⌝)`;
* `fixpoint`: the diagonal (Gödel fixed point) lemma — every sentence `a` admits a
  sentence `d` with `T ⊢ d ↔ (Prov(⌜d⌝) → a)`.

These conditions are satisfied, for instance, by any consistent r.e. extension of
Peano arithmetic with its canonical provability predicate.
-/
structure ProvabilitySystem where
  /-- The sentences of the language. -/
  Sentence : Type
  /-- The implication connective. -/
  imp : Sentence → Sentence → Sentence
  /-- The provability predicate, internalized as an operation on sentences:
  `box a` is the sentence `Prov(⌜a⌝)`. -/
  box : Sentence → Sentence
  /-- `Thm a` means that the theory proves `a`. -/
  Thm : Sentence → Prop
  /-- The theory is closed under modus ponens. -/
  mp : ∀ {a b : Sentence}, Thm (imp a b) → Thm a → Thm b
  /-- Propositional axiom schema `a → (b → a)`. -/
  ax_K1 : ∀ (a b : Sentence), Thm (imp a (imp b a))
  /-- Propositional axiom schema `(a → (b → c)) → ((a → b) → (a → c))`. -/
  ax_K2 : ∀ (a b c : Sentence),
    Thm (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- Derivability condition D1 (necessitation). -/
  nec : ∀ {a : Sentence}, Thm a → Thm (box a)
  /-- Derivability condition D2 (internal modus ponens). -/
  ax_distr : ∀ (a b : Sentence), Thm (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Derivability condition D3 (provable Σ₁-completeness for provability). -/
  ax_four : ∀ (a : Sentence), Thm (imp (box a) (box (box a)))
  /-- The diagonal lemma: every `a` has a fixed point `d` with `T ⊢ d ↔ (□d → a)`. -/
  fixpoint : ∀ (a : Sentence), ∃ d : Sentence,
    Thm (imp d (imp (box d) a)) ∧ Thm (imp (imp (box d) a) d)

namespace ProvabilitySystem

variable (P : ProvabilitySystem)

/-- A theory is *consistent* if it does not prove every sentence. -/
def Consistent : Prop := ∃ a : P.Sentence, ¬ P.Thm a

/-- The *local reflection principle* for the sentence `a`: the sentence
`Prov(⌜a⌝) → a`, expressing that the theory trusts its own proofs of `a`. -/
def Refl (a : P.Sentence) : P.Sentence := P.imp (P.box a) a

variable {P}

/-- Identity: `T ⊢ a → a`. -/
theorem thm_imp_self (a : P.Sentence) : P.Thm (P.imp a a) :=
  P.mp (P.mp (P.ax_K2 a (P.imp a a) a) (P.ax_K1 a (P.imp a a))) (P.ax_K1 a a)

/-- Syllogism: from `T ⊢ a → b` and `T ⊢ b → c` infer `T ⊢ a → c`. -/
theorem thm_syllogism {a b c : P.Sentence} (hab : P.Thm (P.imp a b))
    (hbc : P.Thm (P.imp b c)) : P.Thm (P.imp a c) :=
  P.mp (P.mp (P.ax_K2 a b c) (P.mp (P.ax_K1 (P.imp b c) a) hbc)) hab

/-- Contraction (the `S` combinator): from `T ⊢ a → (b → c)` and `T ⊢ a → b`
infer `T ⊢ a → c`. -/
theorem thm_contract {a b c : P.Sentence} (h₁ : P.Thm (P.imp a (P.imp b c)))
    (h₂ : P.Thm (P.imp a b)) : P.Thm (P.imp a c) :=
  P.mp (P.mp (P.ax_K2 a b c) h₁) h₂

/--
**Löb's theorem.** If a theory satisfying the derivability conditions proves the
reflection principle `Prov(⌜a⌝) → a` for a sentence `a`, then it already proves `a`.
-/
theorem loeb {a : P.Sentence} (h : P.Thm (P.Refl a)) : P.Thm a := by
  obtain ⟨d, hd₁, hd₂⟩ := P.fixpoint a
  -- `T ⊢ □d → □(□d → a)`
  have h₃ : P.Thm (P.imp (P.box d) (P.box (P.imp (P.box d) a))) :=
    P.mp (P.ax_distr d (P.imp (P.box d) a)) (P.nec hd₁)
  -- `T ⊢ □d → (□□d → □a)`
  have h₅ : P.Thm (P.imp (P.box d) (P.imp (P.box (P.box d)) (P.box a))) :=
    thm_syllogism h₃ (P.ax_distr (P.box d) a)
  -- `T ⊢ □d → □a`, using D3 to contract
  have h₇ : P.Thm (P.imp (P.box d) (P.box a)) := thm_contract h₅ (P.ax_four d)
  -- `T ⊢ □d → a`, using the assumed reflection principle
  have h₈ : P.Thm (P.imp (P.box d) a) := thm_syllogism h₇ h
  -- hence `T ⊢ d`, so `T ⊢ □d`, so `T ⊢ a`
  exact P.mp h₈ (P.nec (P.mp hd₂ h₈))

/-- Contrapositive of Löb's theorem: reflection for an unprovable sentence is
itself unprovable. -/
theorem not_thm_refl_of_not_thm {a : P.Sentence} (ha : ¬ P.Thm a) :
    ¬ P.Thm (P.Refl a) := fun h => ha (loeb h)

/-- A theory with an unprovable sentence is consistent. -/
theorem consistent_of_not_thm {a : P.Sentence} (ha : ¬ P.Thm a) : P.Consistent :=
  ⟨a, ha⟩

/-- A theory proving its full local reflection schema is inconsistent. -/
theorem not_consistent_of_refl_schema (h : ∀ a : P.Sentence, P.Thm (P.Refl a)) :
    ¬ P.Consistent := fun ⟨a, ha⟩ => ha (loeb (h a))

end ProvabilitySystem

/--
**Löb: no self-trust.**

Let `P` be a consistent theory equipped with a provability predicate satisfying the
Hilbert–Bernays–Löb derivability conditions and the diagonal lemma. Then:

* for *every* unprovable sentence `S`, the theory cannot prove the corresponding
  reflection principle `Prov(⌜S⌝) → S`; and
* consistency guarantees that such a sentence exists, so the theory genuinely fails
  to prove its own local reflection schema.

(The first conjunct is the contrapositive of Löb's theorem; the second uses the
consistency hypothesis to produce a witness.)
-/
theorem loeb_no_self_trust (P : ProvabilitySystem) (hcon : P.Consistent) :
    (∀ S : P.Sentence, ¬ P.Thm S → ¬ P.Thm (P.imp (P.box S) S)) ∧
      (∃ S : P.Sentence, ¬ P.Thm S ∧ ¬ P.Thm (P.imp (P.box S) S)) := by
  have key : ∀ S : P.Sentence, ¬ P.Thm S → ¬ P.Thm (P.imp (P.box S) S) :=
    fun S hS => ProvabilitySystem.not_thm_refl_of_not_thm hS
  obtain ⟨S, hS⟩ := hcon
  exact ⟨key, S, hS, key S hS⟩

end Frontier

section Sanity
/-- The hypotheses of `Frontier.loeb_no_self_trust` are satisfiable: there is a
consistent provability system. (Here sentences are propositions, `Thm` is truth,
and `box` is the constantly-true sentence; all derivability conditions and the
diagonal lemma hold.) -/
example : ∃ P : Frontier.ProvabilitySystem, P.Consistent := by
  refine ⟨{ Sentence := Prop
            imp := fun a b => a → b
            box := fun _ => True
            Thm := fun a => a
            mp := fun h ha => h ha
            ax_K1 := fun _ _ ha _ => ha
            ax_K2 := fun _ _ _ h g ha => h ha (g ha)
            nec := fun _ => trivial
            ax_distr := fun _ _ _ _ => trivial
            ax_four := fun _ _ => trivial
            fixpoint := fun a => ⟨a, fun ha _ => ha, fun h => h trivial⟩ }, False, id⟩
end Sanity

