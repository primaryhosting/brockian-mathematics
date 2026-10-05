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

/-!
## An abstract formal theory with a provability predicate

We axiomatize the situation of Gödel–Löb: a formal theory `T` whose language contains
an implication connective `imp`, a *provability predicate* `box` (the internal, arithmetized
statement "this sentence is provable in `T`"), and an external predicate `Prov` recording which
sentences are theorems of `T`.

The assumed principles are exactly the standard ones:

* modus ponens, and the implicational Hilbert axioms `K` and `S`
  (so `T` proves every tautology of the implicational fragment and is closed under
  propositional implicational reasoning);
* the Hilbert–Bernays–Löb derivability conditions
  `D1` (necessitation), `D2` (internal modus ponens) and `D3` (internal `D1`);
* the diagonal (fixed point) lemma: every sentence `a` admits a Gödel sentence `L`
  provably equivalent to `box L → a`.
-/

/-- An abstract formal theory equipped with a provability predicate satisfying the
Hilbert–Bernays–Löb derivability conditions and the diagonal lemma. -/
structure ProvabilityTheory where
  /-- The type of sentences of the theory. -/
  Sentence : Type
  /-- Implication between sentences. -/
  imp : Sentence → Sentence → Sentence
  /-- The internal provability predicate: `box a` is the sentence "`a` is provable in `T`". -/
  box : Sentence → Sentence
  /-- `Prov a` holds iff `a` is a theorem of the theory. -/
  Prov : Sentence → Prop
  /-- Modus ponens. -/
  mp : ∀ {a b : Sentence}, Prov (imp a b) → Prov a → Prov b
  /-- The Hilbert axiom scheme `K`: `a → (b → a)`. -/
  axK : ∀ a b : Sentence, Prov (imp a (imp b a))
  /-- The Hilbert axiom scheme `S`: `(a → (b → c)) → ((a → b) → (a → c))`. -/
  axS : ∀ a b c : Sentence, Prov (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- Derivability condition D1 (necessitation): if `a` is provable then so is `box a`. -/
  D1 : ∀ {a : Sentence}, Prov a → Prov (box a)
  /-- Derivability condition D2: `box (a → b) → (box a → box b)`. -/
  D2 : ∀ a b : Sentence, Prov (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Derivability condition D3: `box a → box (box a)`. -/
  D3 : ∀ a : Sentence, Prov (imp (box a) (box (box a)))
  /-- The diagonal lemma: for every `a` there is a sentence `L` with `T ⊢ L ↔ (box L → a)`. -/
  diag : ∀ a : Sentence, ∃ L : Sentence,
    Prov (imp L (imp (box L) a)) ∧ Prov (imp (imp (box L) a) L)

namespace ProvabilityTheory

variable (T : ProvabilityTheory)

/-- A theory is *consistent* (here: nontrivial) if some sentence is not provable in it. -/
def Consistent : Prop := ∃ a : T.Sentence, ¬ T.Prov a

/-- The *local reflection principle* for the sentence `a`: the sentence
"if `a` is provable in `T`, then `a`", i.e. `box a → a`. -/
def Reflection (a : T.Sentence) : T.Sentence := T.imp (T.box a) a

variable {T}

/-- `a → a` is provable. -/
theorem prov_imp_self (a : T.Sentence) : T.Prov (T.imp a a) :=
  T.mp (T.mp (T.axS a (T.imp a a) a) (T.axK a (T.imp a a))) (T.axK a a)

/-- Hypothetical syllogism. -/
theorem prov_imp_trans {a b c : T.Sentence} (hab : T.Prov (T.imp a b))
    (hbc : T.Prov (T.imp b c)) : T.Prov (T.imp a c) :=
  T.mp (T.mp (T.axS a b c) (T.mp (T.axK (T.imp b c) a) hbc)) hab

/-- The `S` axiom in rule form. -/
theorem prov_imp_mp {a b c : T.Sentence} (h : T.Prov (T.imp a (T.imp b c)))
    (hb : T.Prov (T.imp a b)) : T.Prov (T.imp a c) :=
  T.mp (T.mp (T.axS a b c) h) hb

/-- **Löb's theorem.** If the theory proves the reflection principle for `a`,
then it proves `a`. -/
theorem loeb {a : T.Sentence} (h : T.Prov (T.Reflection a)) : T.Prov a := by
  obtain ⟨L, h1, h2⟩ := T.diag a
  -- `box L → box (box L → a)`
  have b2 : T.Prov (T.imp (T.box L) (T.box (T.imp (T.box L) a))) :=
    T.mp (T.D2 L (T.imp (T.box L) a)) (T.D1 h1)
  -- `box L → (box (box L) → box a)`
  have b4 : T.Prov (T.imp (T.box L) (T.imp (T.box (T.box L)) (T.box a))) :=
    prov_imp_trans b2 (T.D2 (T.box L) a)
  -- `box L → box a`
  have b6 : T.Prov (T.imp (T.box L) (T.box a)) := prov_imp_mp b4 (T.D3 L)
  -- `box L → a`
  have b7 : T.Prov (T.imp (T.box L) a) := prov_imp_trans b6 h
  -- hence `L`, hence `box L`, hence `a`
  exact T.mp b7 (T.D1 (T.mp h2 b7))

end ProvabilityTheory

/-- **Löb: no self-trust.** A theory satisfying the derivability conditions and the
diagonal lemma cannot prove the local reflection principle `box a → a` for any sentence `a`
that it does not already prove.

In particular, taking any unprovable `a` (which exists precisely when the theory is
consistent, see `Frontier.loeb_no_self_trust_of_consistent`), the theory cannot prove
that its own proofs of `a` are trustworthy. -/
theorem loeb_no_self_trust {T : ProvabilityTheory} {a : T.Sentence} (ha : ¬ T.Prov a) :
    ¬ T.Prov (T.Reflection a) :=
  fun h => ha (ProvabilityTheory.loeb h)

/-- A consistent theory fails to prove some instance of its own reflection schema:
there is a sentence `a` which is unprovable and whose reflection principle `box a → a`
is unprovable as well. -/
theorem loeb_no_self_trust_of_consistent {T : ProvabilityTheory} (hT : T.Consistent) :
    ∃ a : T.Sentence, ¬ T.Prov a ∧ ¬ T.Prov (T.Reflection a) := by
  obtain ⟨a, ha⟩ := hT
  exact ⟨a, ha, loeb_no_self_trust ha⟩

/-!
## Nonvacuity

The axioms of `ProvabilityTheory` are consistent with the theory being consistent: the
following two-valued example satisfies all of them and has an unprovable sentence, so
`Frontier.loeb_no_self_trust` is not vacuously true.
-/

/-- A two-valued example of a `ProvabilityTheory`: sentences are booleans, `imp` is boolean
implication, `box` is constantly `true`, and the theorems are the sentences equal to `true`. -/
def boolTheory : ProvabilityTheory where
  Sentence := Bool
  imp a b := (!a || b)
  box _ := true
  Prov a := a = true
  mp := by intro a b; revert a b; decide
  axK := by decide
  axS := by decide
  D1 := by intro a; revert a; decide
  D2 := by decide
  D3 := by decide
  diag a := ⟨a, by cases a <;> decide, by cases a <;> decide⟩

/-- The two-valued example theory is consistent. -/
theorem boolTheory_consistent : boolTheory.Consistent :=
  ⟨false, fun h => Bool.noConfusion h⟩

/-- Instance of the main theorem: in the two-valued example theory the reflection principle
for the unprovable sentence `false` is itself unprovable. -/
theorem boolTheory_no_self_trust :
    ¬ boolTheory.Prov (boolTheory.Reflection false) :=
  loeb_no_self_trust (fun h => Bool.noConfusion h)

/-!
## Consistency as a sentence, and Gödel's second incompleteness theorem

If the language additionally has a falsum `bot` (with ex falso available in the theory),
then consistency in the usual sense is `¬ Prov bot`, the *consistency sentence* of the theory
is the reflection principle for `bot`, namely `box bot → bot`, and the main theorem specializes
to Gödel's second incompleteness theorem.
-/

/-- A `ProvabilityTheory` whose language also has a falsum constant `bot`, with ex falso
available inside the theory. -/
structure ProvabilityTheoryWithBot extends ProvabilityTheory where
  /-- The falsum sentence. -/
  bot : Sentence
  /-- Ex falso quodlibet: `bot → a` is provable for every `a`. -/
  exFalso : ∀ a : Sentence, Prov (imp bot a)

namespace ProvabilityTheoryWithBot

variable (T : ProvabilityTheoryWithBot)

/-- Consistency in the usual sense: the theory does not prove `bot`. -/
def ConsistentBot : Prop := ¬ T.toProvabilityTheory.Prov T.bot

/-- The consistency sentence `Con(T) = box bot → bot` of the theory, i.e. the reflection
principle for `bot`. -/
def Con : T.Sentence := T.toProvabilityTheory.Reflection T.bot

variable {T}

/-- Consistency in the sense of not proving `bot` implies nontriviality. -/
theorem consistent_of_consistentBot (h : T.ConsistentBot) :
    T.toProvabilityTheory.Consistent :=
  ⟨T.bot, h⟩

/-- **Gödel's second incompleteness theorem**, as an instance of `Frontier.loeb_no_self_trust`:
a consistent theory does not prove its own consistency sentence `box bot → bot`. -/
theorem not_prov_con (h : T.ConsistentBot) : ¬ T.toProvabilityTheory.Prov T.Con :=
  loeb_no_self_trust h

end ProvabilityTheoryWithBot

/-- The two-valued example, with `bot := false`, satisfies the extra axioms as well. -/
def boolTheoryWithBot : ProvabilityTheoryWithBot where
  toProvabilityTheory := boolTheory
  bot := false
  exFalso := fun _ => rfl

/-- The two-valued example theory does not prove `bot`. -/
theorem boolTheoryWithBot_consistentBot : boolTheoryWithBot.ConsistentBot :=
  fun h => Bool.noConfusion h

/-- Non-vacuous instance of Gödel's second incompleteness theorem in the two-valued example. -/
theorem boolTheoryWithBot_not_prov_con :
    ¬ boolTheoryWithBot.toProvabilityTheory.Prov boolTheoryWithBot.Con :=
  ProvabilityTheoryWithBot.not_prov_con boolTheoryWithBot_consistentBot

end Frontier

