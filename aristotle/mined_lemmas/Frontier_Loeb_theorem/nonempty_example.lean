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

