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
def Consistent : Prop := ¬ S.Prov S.bot

/-- The reflection principle for `A`: the sentence `Pr(⌜A⌝) → A`. -/
def Reflection (A : S.Sentence) : S.Sentence := S.imp (S.box A) A

variable {S}

/-- Hypothetical syllogism, derived from the Hilbert axiom schemes. -/
theorem syll {A B C : S.Sentence} (hAB : S.Prov (S.imp A B))
    (hBC : S.Prov (S.imp B C)) : S.Prov (S.imp A C) :=
  S.mp (S.mp (S.k2 A B C) (S.mp (S.k1 (S.imp B C) A) hBC)) hAB

/-- **Löb's theorem**: if the theory proves the reflection principle for `A`,
then it proves `A`. -/
theorem loeb {A : S.Sentence} (h : S.Prov (S.Reflection A)) : S.Prov A := by
  obtain ⟨G, hG1, hG2⟩ := S.fix A
  -- `T ⊢ Pr(⌜G⌝) → Pr(⌜Pr(⌜G⌝) → A⌝)`
  have h3 : S.Prov (S.imp (S.box G) (S.box (S.imp (S.box G) A))) :=
    S.mp (S.boxK G (S.imp (S.box G) A)) (S.nec hG1)
  -- `T ⊢ Pr(⌜G⌝) → (Pr(⌜Pr(⌜G⌝)⌝) → Pr(⌜A⌝))`
  have h5 : S.Prov (S.imp (S.box G) (S.imp (S.box (S.box G)) (S.box A))) :=
    syll h3 (S.boxK (S.box G) A)
  -- `T ⊢ Pr(⌜G⌝) → Pr(⌜A⌝)`
  have h7 : S.Prov (S.imp (S.box G) (S.box A)) :=
    S.mp (S.mp (S.k2 (S.box G) (S.box (S.box G)) (S.box A)) h5) (S.box4 G)
  -- `T ⊢ Pr(⌜G⌝) → A`
  have h9 : S.Prov (S.imp (S.box G) A) := syll h7 h
  exact S.mp h9 (S.nec (S.mp hG2 h9))

end LoebSystem

/-- **Löb: no self-trust.**

For any theory equipped with a provability predicate satisfying the derivability
conditions and the diagonal lemma:

1. if a sentence `A` is not provable, then the theory cannot prove the reflection
   instance `Pr(⌜A⌝) → A` for it;
2. a consistent theory cannot prove its full reflection schema.

In particular a consistent theory always has unprovable sentences (e.g. `⊥`), and so
it never proves that its own provability of a sentence implies that sentence. -/
theorem loeb_no_self_trust (S : LoebSystem) (hcon : S.Consistent) :
    (∀ A : S.Sentence, ¬ S.Prov A → ¬ S.Prov (S.Reflection A)) ∧
      ¬ (∀ A : S.Sentence, S.Prov (S.Reflection A)) := by
  refine ⟨fun A hA h => hA (LoebSystem.loeb h), fun h => hcon ?_⟩
  exact LoebSystem.loeb (h S.bot)

/-! ### Non-vacuity

The axioms of `LoebSystem` are satisfiable by a *consistent* system, so the theorem
above is not vacuous. We use the modal language with no atoms, interpreted in the
one-point Kripke frame with empty accessibility relation, where `Pr(⌜A⌝)` is always
true and `⊥` is false. -/

/-- Modal sentences built from `⊥`, implication and the provability operator. -/
inductive Fml : Type
  | bot : Fml
  | imp : Fml → Fml → Fml
  | box : Fml → Fml
  deriving DecidableEq

/-- Truth of a modal sentence in the one-point frame with empty accessibility. -/
def Fml.Truth : Fml → Prop
  | Fml.bot => False
  | Fml.imp A B => A.Truth → B.Truth
  | Fml.box _ => True

/-- A consistent model of the `LoebSystem` axioms. -/
def exampleLoebSystem : LoebSystem where
  Sentence := Fml
  imp := Fml.imp
  bot := Fml.bot
  box := Fml.box
  Prov := Fml.Truth
  mp := fun h h' => h h'
  k1 := fun _ _ => fun h _ => h
  k2 := fun _ _ _ => fun h h' h'' => h h'' (h' h'')
  exfalso := fun _ => False.elim
  nec := fun _ => trivial
  boxK := fun _ _ => fun _ _ => trivial
  box4 := fun _ => fun _ => trivial
  fix := fun A => ⟨A, fun h _ => h, fun h => h trivial⟩

/-- The example system is consistent, so the hypotheses of `loeb_no_self_trust`
are satisfiable. -/
theorem exampleLoebSystem_consistent : exampleLoebSystem.Consistent := id

end Frontier

