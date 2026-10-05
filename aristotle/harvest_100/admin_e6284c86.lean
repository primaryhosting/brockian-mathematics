/-!
# Loeb Theorem
Category: Frontier — Set Theory
Target: Frontier.Loeb_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Löb's theorem

Löb's theorem states: if `PA ⊢ (□φ → φ)` then `PA ⊢ φ`, where `□φ` abbreviates the
arithmetical sentence `Prov_PA(⌜φ⌝)` expressing "`φ` is provable in `PA`".

The mathematical content of the theorem is entirely captured by the following properties of
the pair (theory `T`, provability predicate `□`), all of which hold for `PA` together with
the standard Gödel provability predicate:

* the theory is closed under *modus ponens* and proves all instances of the two implicational
  axiom schemes `K` and `S` (this is exactly the implicational fragment of propositional logic,
  which is all the logic that Löb's argument uses);
* the **Hilbert–Bernays–Löb derivability conditions**
  - `D1` : if `T ⊢ φ` then `T ⊢ □φ`,
  - `D2` : `T ⊢ □(φ → ψ) → (□φ → □ψ)`,
  - `D3` : `T ⊢ □φ → □□φ`;
* the **diagonal (fixed point) lemma**: for every sentence `φ` there is a sentence `ψ` with
  `T ⊢ ψ ↔ (□ψ → φ)`.

These data are packaged in the structure `Frontier.ProvabilitySystem` below, and
`Frontier.Loeb_theorem` proves Löb's theorem for every such system. The arithmetization of
syntax needed to verify these conditions for `PA` itself (Gödel numbering, representability of
the proof relation, the diagonal lemma) is Gödel's incompleteness machinery; it is *assumed*
here, being the input to Löb's theorem rather than part of it.

`Frontier.ProvabilitySystem.nonempty_example` checks that the axioms of a provability system are
satisfiable, so that `Frontier.Loeb_theorem` is not vacuously true.

The file is self-contained: it uses no library beyond the Lean 4 prelude.
-/

universe u

namespace Frontier

/-- A *provability system*: an abstract axiomatization of a formal theory `T` together with a
provability predicate `□`, carrying exactly the hypotheses used in Löb's argument.

`Sentence` is the type of sentences of the language, `imp` is the implication connective,
`box φ` is the sentence expressing "`φ` is provable in `T`", and `Provable φ` means `T ⊢ φ`. -/
structure ProvabilitySystem where
  /-- The type of sentences of the language of the theory. -/
  Sentence : Type u
  /-- The implication connective on sentences. -/
  imp : Sentence → Sentence → Sentence
  /-- `box φ` is the sentence expressing "`φ` is provable in the theory". -/
  box : Sentence → Sentence
  /-- `Provable φ` means `T ⊢ φ`. -/
  Provable : Sentence → Prop
  /-- Modus ponens: from `T ⊢ φ → ψ` and `T ⊢ φ` infer `T ⊢ ψ`. -/
  mp : ∀ {p q : Sentence}, Provable (imp p q) → Provable p → Provable q
  /-- The axiom scheme `K` of the implicational propositional calculus. -/
  axK : ∀ p q : Sentence, Provable (imp p (imp q p))
  /-- The axiom scheme `S` of the implicational propositional calculus. -/
  axS : ∀ p q r : Sentence,
    Provable (imp (imp p (imp q r)) (imp (imp p q) (imp p r)))
  /-- First derivability condition: if `T ⊢ φ` then `T ⊢ □φ`. -/
  D1 : ∀ {p : Sentence}, Provable p → Provable (box p)
  /-- Second derivability condition: `T ⊢ □(φ → ψ) → (□φ → □ψ)`. -/
  D2 : ∀ p q : Sentence, Provable (imp (box (imp p q)) (imp (box p) (box q)))
  /-- Third derivability condition: `T ⊢ □φ → □□φ`. -/
  D3 : ∀ p : Sentence, Provable (imp (box p) (box (box p)))
  /-- The diagonal lemma, in the instance needed: for every `φ` there is a sentence `ψ` with
  `T ⊢ ψ ↔ (□ψ → φ)`, stated as the two separate implications so that no connective beyond
  `→` is required. -/
  diagonal : ∀ p : Sentence, ∃ q : Sentence,
    Provable (imp q (imp (box q) p)) ∧ Provable (imp (imp (box q) p) q)

namespace ProvabilitySystem

section Logic

variable {S : ProvabilitySystem.{u}}

/-- From `T ⊢ p → (q → r)` and `T ⊢ p → q` infer `T ⊢ p → r`. -/
theorem mp_imp {p q r : S.Sentence} (h₁ : S.Provable (S.imp p (S.imp q r)))
    (h₂ : S.Provable (S.imp p q)) : S.Provable (S.imp p r) :=
  S.mp (S.mp (S.axS p q r) h₁) h₂

/-- `T ⊢ p → p`. -/
theorem imp_self (p : S.Sentence) : S.Provable (S.imp p p) :=
  mp_imp (S.axK p (S.imp p p)) (S.axK p p)

/-- Transitivity of provable implication. -/
theorem imp_trans {p q r : S.Sentence} (h₁ : S.Provable (S.imp p q))
    (h₂ : S.Provable (S.imp q r)) : S.Provable (S.imp p r) :=
  mp_imp (S.mp (S.axK (S.imp q r) p) h₂) h₁

end Logic

end ProvabilitySystem

/-- **Löb's theorem.** In any theory `T` equipped with a provability predicate `□` satisfying
the Hilbert–Bernays–Löb derivability conditions and the diagonal lemma — for instance `PA` with
the standard provability predicate — if `T ⊢ (□φ → φ)` then `T ⊢ φ`. -/
theorem Loeb_theorem (S : ProvabilitySystem.{u}) (p : S.Sentence)
    (h : S.Provable (S.imp (S.box p) p)) : S.Provable p := by
  -- Take a fixed point `q` of `x ↦ (□x → p)`, i.e. `T ⊢ q ↔ (□q → p)`.
  obtain ⟨q, hq₁, hq₂⟩ := S.diagonal p
  -- `T ⊢ □q → □(□q → p)`, by `D1` applied to `hq₁` followed by `D2`.
  have hbox : S.Provable (S.imp (S.box q) (S.box (S.imp (S.box q) p))) :=
    S.mp (S.D2 q (S.imp (S.box q) p)) (S.D1 hq₁)
  -- `T ⊢ □q → (□□q → □p)`, by `D2` again.
  have hchain : S.Provable (S.imp (S.box q) (S.imp (S.box (S.box q)) (S.box p))) :=
    ProvabilitySystem.imp_trans hbox (S.D2 (S.box q) p)
  -- `T ⊢ □q → □p`, using `D3`.
  have hboxp : S.Provable (S.imp (S.box q) (S.box p)) :=
    ProvabilitySystem.mp_imp hchain (S.D3 q)
  -- `T ⊢ □q → p`, using the hypothesis `T ⊢ □p → p`.
  have hqp : S.Provable (S.imp (S.box q) p) := ProvabilitySystem.imp_trans hboxp h
  -- Hence `T ⊢ q`, hence `T ⊢ □q`, hence `T ⊢ p`.
  exact S.mp hqp (S.D1 (S.mp hq₂ hqp))

/-- **Gödel's second incompleteness theorem**, an immediate consequence of Löb's theorem: if the
theory proves its own consistency statement `Con(T) = (□⊥ → ⊥)`, then it proves `⊥`, i.e. it is
inconsistent. -/
theorem second_incompleteness_of_Loeb (S : ProvabilitySystem.{u}) (bot : S.Sentence)
    (h : S.Provable (S.imp (S.box bot) bot)) : S.Provable bot :=
  Loeb_theorem S bot h

namespace ProvabilitySystem

/-- The axioms of a provability system are satisfiable: they hold, for instance, for the
(inconsistent) theory in which every sentence is provable. Hence the hypotheses of
`Frontier.Loeb_theorem` are consistent and the theorem is not vacuously true. -/
theorem nonempty_example : Nonempty ProvabilitySystem.{0} :=
  ⟨{ Sentence := Unit
     imp := fun _ _ => ()
     box := fun _ => ()
     Provable := fun _ => True
     mp := fun _ _ => trivial
     axK := fun _ _ => trivial
     axS := fun _ _ _ => trivial
     D1 := fun _ => trivial
     D2 := fun _ _ => trivial
     D3 := fun _ => trivial
     diagonal := fun _ => ⟨(), trivial, trivial⟩ }⟩

end ProvabilitySystem

end Frontier

#print axioms Frontier.Loeb_theorem
#print axioms Frontier.second_incompleteness_of_Loeb
#print axioms Frontier.ProvabilitySystem.nonempty_example

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

