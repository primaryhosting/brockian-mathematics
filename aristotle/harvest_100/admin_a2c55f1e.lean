-- Lean requires `import` to be the first command, so the mandated header appears as an
-- ordinary block comment here and is repeated verbatim as the module docstring below.
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
An abstract axiomatic theory equipped with a provability predicate, satisfying the
Hilbert–Bernays–Löb derivability conditions and admitting Gödel-style diagonalization.

* `Sentence` is the type of sentences of the language of the theory;
* `imp a b` is the (object-level) implication `a → b`;
* `box a` is the sentence `Pr(⌜a⌝)` expressing "`a` is provable in the theory";
* `Thm a` means "the theory proves `a`".

The fields `mp`, `impTrans`, `impDist` record the (very small) amount of propositional
logic that is used; `nec`, `boxK`, `boxFour` are the three derivability conditions
(D1, D2, D3); and `diagonal` is the diagonal lemma, providing for every sentence `a`
a sentence `l` provably equivalent to `Pr(⌜l⌝) → a`.

Mathlib has no development of provability logic, so the framework is set up here from
scratch. (A search of Mathlib turns up no Löb-style fixed point theorem: the only
occurrences of the name `Loeb` are unrelated.)
-/
structure ProvabilitySystem where
  /-- The sentences of the language of the theory. -/
  Sentence : Type
  /-- Object-level implication. -/
  imp : Sentence → Sentence → Sentence
  /-- The provability predicate: `box a` is the sentence `Pr(⌜a⌝)`. -/
  box : Sentence → Sentence
  /-- `Thm a` means that the theory proves `a`. -/
  Thm : Sentence → Prop
  /-- Modus ponens. -/
  mp : ∀ {a b : Sentence}, Thm (imp a b) → Thm a → Thm b
  /-- Transitivity of implication (a propositional tautology of the theory). -/
  impTrans : ∀ {a b c : Sentence}, Thm (imp a b) → Thm (imp b c) → Thm (imp a c)
  /-- Distribution of implication over implication (the `S` combinator). -/
  impDist : ∀ {a b c : Sentence}, Thm (imp a (imp b c)) → Thm (imp a b) → Thm (imp a c)
  /-- D1: necessitation — what is proved is provably provable. -/
  nec : ∀ {a : Sentence}, Thm a → Thm (box a)
  /-- D2: the provability predicate distributes over implication. -/
  boxK : ∀ {a b : Sentence}, Thm (imp (box (imp a b)) (imp (box a) (box b)))
  /-- D3: provability is provably transitive. -/
  boxFour : ∀ {a : Sentence}, Thm (imp (box a) (box (box a)))
  /-- The diagonal lemma: every `a` has a fixed point `l` with `⊢ l ↔ (Pr(⌜l⌝) → a)`. -/
  diagonal : ∀ a : Sentence, ∃ l : Sentence,
    Thm (imp l (imp (box l) a)) ∧ Thm (imp (imp (box l) a) l)

namespace ProvabilitySystem

variable (S : ProvabilitySystem)

/-- A theory is consistent if some sentence is not provable in it. -/
def Consistent : Prop := ∃ a : S.Sentence, ¬ S.Thm a

/-- The reflection principle (local reflection instance) for a sentence `a`:
the sentence `Pr(⌜a⌝) → a`, expressing "if `a` is provable then `a`". -/
def reflection (a : S.Sentence) : S.Sentence := S.imp (S.box a) a

variable {S}

/-- **Löb's theorem**: if the theory proves the reflection instance `Pr(⌜a⌝) → a`,
then it already proves `a`. -/
theorem loeb {a : S.Sentence} (h : S.Thm (S.reflection a)) : S.Thm a := by
  obtain ⟨l, hl₁, hl₂⟩ := S.diagonal a
  -- `⊢ Pr(⌜l⌝) → Pr(⌜Pr(⌜l⌝) → a⌝)`
  have h₁ : S.Thm (S.imp (S.box l) (S.box (S.imp (S.box l) a))) :=
    S.mp S.boxK (S.nec hl₁)
  -- `⊢ Pr(⌜l⌝) → (Pr(⌜Pr(⌜l⌝)⌝) → Pr(⌜a⌝))`
  have h₂ : S.Thm (S.imp (S.box l) (S.imp (S.box (S.box l)) (S.box a))) :=
    S.impTrans h₁ S.boxK
  -- `⊢ Pr(⌜l⌝) → Pr(⌜a⌝)`
  have h₃ : S.Thm (S.imp (S.box l) (S.box a)) := S.impDist h₂ S.boxFour
  -- `⊢ Pr(⌜l⌝) → a`
  have h₄ : S.Thm (S.imp (S.box l) a) := S.impTrans h₃ h
  -- hence `⊢ l`, so `⊢ Pr(⌜l⌝)`, so `⊢ a`
  exact S.mp h₄ (S.nec (S.mp hl₂ h₄))

end ProvabilitySystem

/--
**No self-trust (Löb)**: a theory satisfying the derivability conditions cannot prove
the reflection instance `Pr(⌜a⌝) → a` for any sentence `a` that it does not prove.

In particular the hypothesis `¬ S.Thm a` witnesses that `S` is consistent (in the sense
of `ProvabilitySystem.Consistent`), so this is exactly the statement that a consistent
theory cannot prove its own reflection schema for an unprovable sentence.
-/
theorem loeb_no_self_trust (S : ProvabilitySystem) (a : S.Sentence) (ha : ¬ S.Thm a) :
    ¬ S.Thm (S.reflection a) := fun h => ha (ProvabilitySystem.loeb h)

/-- A consistent theory (satisfying the derivability conditions) cannot prove the full
local reflection schema `Pr(⌜a⌝) → a`. -/
theorem loeb_no_reflection_schema (S : ProvabilitySystem) (hS : S.Consistent) :
    ¬ ∀ a : S.Sentence, S.Thm (S.reflection a) := by
  obtain ⟨a, ha⟩ := hS
  exact fun h => loeb_no_self_trust S a ha (h a)

/-- A sanity check that the axioms of `ProvabilitySystem` are consistent: a two-valued
model in which some sentence is unprovable, so that the hypotheses of
`loeb_no_self_trust` and `loeb_no_reflection_schema` are satisfiable. -/
def boolSystem : ProvabilitySystem where
  Sentence := Bool
  imp a b := (!a || b)
  box _ := true
  Thm a := a = true
  mp {a b} h₁ h₂ := by revert h₁ h₂; revert a b; decide
  impTrans {a b c} h₁ h₂ := by revert h₁ h₂; revert a b c; decide
  impDist {a b c} h₁ h₂ := by revert h₁ h₂; revert a b c; decide
  nec _ := rfl
  boxK := rfl
  boxFour := rfl
  diagonal a := ⟨a, by revert a; decide, by revert a; decide⟩

example : boolSystem.Consistent := ⟨false, by simp [boolSystem]⟩

end Frontier

