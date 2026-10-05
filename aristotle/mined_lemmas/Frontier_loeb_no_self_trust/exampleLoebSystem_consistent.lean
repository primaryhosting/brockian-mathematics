/-!
# Loeb No Self Trust
Category: Frontier Mind
Target: Frontier.loeb_no_self_trust
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- An abstract axiomatization of a formal theory `T` equipped with a provability
predicate, in the style of the Hilbert–Bernays–Löb derivability conditions.

* `Sentence` is the type of sentences of the language;
* `imp`, `bot` and `box` are the implication connective, the false sentence and the
  sentence `Pr(⌜·⌝)` expressing provability-in-`T` inside the language;
* `Prov A` means "`T` proves `A`".

The fields record: closure of `T` under modus ponens, the two implicational axiom
schemes of a Hilbert calculus together with ex falso (so that `T` contains classical
propositional logic), the three derivability conditions (necessitation, distribution
`K`, and internal necessitation `4`), and the diagonal (Gödel fixed-point) lemma. -/
structure LoebSystem where
  /-- The type of sentences of the language of the theory. -/
  Sentence : Type
  /-- Implication between sentences. -/
  imp : Sentence → Sentence → Sentence
  /-- The false sentence. -/
  bot : Sentence
  /-- The provability sentence `Pr(⌜A⌝)`, internalizing provability in the language. -/
  box : Sentence → Sentence
  /-- `Prov A` means: the theory proves the sentence `A`. -/
  Prov : Sentence → Prop
  /-- The theory is closed under modus ponens. -/
  mp : ∀ {A B : Sentence}, Prov (imp A B) → Prov A → Prov B
  /-- Hilbert axiom scheme `A → (B → A)`. -/
  k1 : ∀ A B : Sentence, Prov (imp A (imp B A))
  /-- Hilbert axiom scheme `(A → (B → C)) → ((A → B) → (A → C))`. -/
  k2 : ∀ A B C : Sentence,
    Prov (imp (imp A (imp B C)) (imp (imp A B) (imp A C)))
  /-- Ex falso: `⊥ → A`. -/
  exfalso : ∀ A : Sentence, Prov (imp bot A)
  /-- First derivability condition (necessitation): if `T ⊢ A` then `T ⊢ Pr(⌜A⌝)`. -/
  nec : ∀ {A : Sentence}, Prov A → Prov (box A)
  /-- Second derivability condition: `Pr(⌜A → B⌝) → (Pr(⌜A⌝) → Pr(⌜B⌝))`. -/
  boxK : ∀ A B : Sentence, Prov (imp (box (imp A B)) (imp (box A) (box B)))
  /-- Third derivability condition: `Pr(⌜A⌝) → Pr(⌜Pr(⌜A⌝)⌝)`. -/
  box4 : ∀ A : Sentence, Prov (imp (box A) (box (box A)))
  /-- Diagonal lemma: every `A` has a fixed point `G` with `T ⊢ G ↔ (Pr(⌜G⌝) → A)`. -/
  fix : ∀ A : Sentence, ∃ G : Sentence,
    Prov (imp G (imp (box G) A)) ∧ Prov (imp (imp (box G) A) G)

namespace LoebSystem

variable (S : LoebSystem)

/-- The theory is consistent: it does not prove `⊥`. -/

theorem exampleLoebSystem_consistent : exampleLoebSystem.Consistent := id

end Frontier

