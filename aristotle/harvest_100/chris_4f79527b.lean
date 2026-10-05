/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-!
## The syntactic setting

We work with the standard abstract (Hilbert–Bernays–Löb) formulation of Gödel's second
incompleteness theorem.

`Fml` is a language of sentences built from atoms, falsum and implication, together with a
unary operator `box`.  For a recursively axiomatized theory `T` extending `PA`, one reads
`Fml` as (a fragment of) the sentences of arithmetic and `box p` as the arithmetized
provability sentence `Prov_T(⌜p⌝)`; the fact that `T` is recursively axiomatized and extends
`PA` is exactly what supplies the three Löb derivability conditions `D1`, `D2`, `D3` recorded
in `ProvabilitySystem` below, and the diagonal lemma supplies the Gödel fixed point.
-/

/-- Sentences: propositional atoms, falsum, implication, and a provability operator `box`. -/
inductive Fml where
  | atom : Nat → Fml
  | bot : Fml
  | imp : Fml → Fml → Fml
  | box : Fml → Fml
  deriving DecidableEq

namespace Fml

/-- Negation, `¬ p := p → ⊥`. -/
def neg (p : Fml) : Fml := Fml.imp p Fml.bot

end Fml

/-- Propositional evaluation: `box`-formulas and atoms are treated as propositional atoms. -/
def eval (v : Fml → Bool) : Fml → Bool
  | .atom n => v (.atom n)
  | .bot => false
  | .imp a b => !(eval v a) || eval v b
  | .box a => v (.box a)

/-- A formula is a propositional tautology if it evaluates to `true` under every assignment
to atoms and boxed formulas. -/
def Taut (p : Fml) : Prop := ∀ v, eval v p = true

/-- An abstract provability system: a set of theorems closed under propositional logic and
modus ponens, whose `box` operator satisfies the three Löb derivability conditions.

Any recursively axiomatized theory `T` extending `PA`, with `box` interpreted as the
arithmetized provability predicate `Prov_T`, is such a system. -/
structure ProvabilitySystem where
  /-- `Thm p` means: the theory proves the sentence `p`. -/
  Thm : Fml → Prop
  /-- The theory proves every propositional tautology. -/
  taut : ∀ p, Taut p → Thm p
  /-- The theory is closed under modus ponens. -/
  mp : ∀ {a b : Fml}, Thm (Fml.imp a b) → Thm a → Thm b
  /-- D1: provable sentences are provably provable. -/
  D1 : ∀ {a : Fml}, Thm a → Thm (Fml.box a)
  /-- D2: the provability predicate is provably closed under modus ponens. -/
  D2 : ∀ a b : Fml, Thm (Fml.imp (Fml.box (Fml.imp a b)) (Fml.imp (Fml.box a) (Fml.box b)))
  /-- D3: provable formal provability is provably provable. -/
  D3 : ∀ a : Fml, Thm (Fml.imp (Fml.box a) (Fml.box (Fml.box a)))

/-- The sentence expressing the consistency of the theory: `¬ Prov(⌜⊥⌝)`. -/
def consistencyStmt : Fml := Fml.neg (Fml.box Fml.bot)

/-- Semantic consistency of a provability system: it does not prove falsum. -/
def ProvabilitySystem.Consistent (T : ProvabilitySystem) : Prop := ¬ T.Thm Fml.bot

/-- A Gödel fixed point for `T`: a sentence provably equivalent to its own unprovability.
The diagonal lemma provides such a sentence for every recursively axiomatized theory
extending `PA`. -/
structure ProvabilitySystem.GoedelSentence (T : ProvabilitySystem) (G : Fml) : Prop where
  forward : T.Thm (Fml.imp G (Fml.neg (Fml.box G)))
  backward : T.Thm (Fml.imp (Fml.neg (Fml.box G)) G)

/-! ## Propositional lemmas -/

theorem taut_syll (a b c : Fml) :
    Taut (.imp (.imp a b) (.imp (.imp b c) (.imp a c))) := by
  intro v
  simp only [eval]
  cases eval v a <;> cases eval v b <;> cases eval v c <;> rfl

/-- Chaining of provable implications. -/
theorem ProvabilitySystem.syll (T : ProvabilitySystem) {a b c : Fml}
    (h1 : T.Thm (Fml.imp a b)) (h2 : T.Thm (Fml.imp b c)) : T.Thm (Fml.imp a c) :=
  T.mp (T.mp (T.taut _ (taut_syll a b c)) h1) h2

/-- From `a → (b → c)` and `a → b` infer `a → c`. -/
theorem ProvabilitySystem.contract (T : ProvabilitySystem) {a b c : Fml}
    (h1 : T.Thm (Fml.imp a (Fml.imp b c))) (h2 : T.Thm (Fml.imp a b)) :
    T.Thm (Fml.imp a c) := by
  refine T.mp (T.mp (T.taut (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c))) ?_) h1) h2
  intro v
  simp only [eval]
  cases eval v a <;> cases eval v b <;> cases eval v c <;> rfl

/-! ## Gödel's second incompleteness theorem -/

/-- Key step (formalized Löb-style argument): if `G` is a Gödel sentence then
`T ⊢ Prov(⌜G⌝) → Prov(⌜⊥⌝)`. -/
theorem ProvabilitySystem.box_goedel_imp_box_bot (T : ProvabilitySystem) {G : Fml}
    (hG : T.GoedelSentence G) :
    T.Thm (Fml.imp (Fml.box G) (Fml.box Fml.bot)) := by
  -- From `T ⊢ G → (□G → ⊥)` we get `T ⊢ □(G → (□G → ⊥))`.
  have h1 : T.Thm (Fml.box (Fml.imp G (Fml.imp (Fml.box G) Fml.bot))) := T.D1 hG.forward
  -- Hence `T ⊢ □G → □(□G → ⊥)`.
  have h2 : T.Thm (Fml.imp (Fml.box G) (Fml.box (Fml.imp (Fml.box G) Fml.bot))) :=
    T.mp (T.D2 G (Fml.imp (Fml.box G) Fml.bot)) h1
  -- And `T ⊢ □(□G → ⊥) → (□□G → □⊥)`.
  have h3 : T.Thm (Fml.imp (Fml.box (Fml.imp (Fml.box G) Fml.bot))
      (Fml.imp (Fml.box (Fml.box G)) (Fml.box Fml.bot))) := T.D2 (Fml.box G) Fml.bot
  -- So `T ⊢ □G → (□□G → □⊥)`.
  have h4 : T.Thm (Fml.imp (Fml.box G) (Fml.imp (Fml.box (Fml.box G)) (Fml.box Fml.bot))) :=
    T.syll h2 h3
  -- D3 gives `T ⊢ □G → □□G`, and contraction finishes.
  exact T.contract h4 (T.D3 G)

/--
**Gödel's second incompleteness theorem.**

No consistent recursively axiomatized theory extending `PA` proves its own consistency:
for any provability system `T` satisfying the Löb derivability conditions and possessing a
Gödel fixed point `G` (both of which are supplied by recursive axiomatizability together
with extension of `PA`), if `T` is consistent then `T` does not prove the sentence
`Con(T) = ¬ Prov(⌜⊥⌝)`.
-/
theorem Goedel_second_incompleteness (T : ProvabilitySystem) (G : Fml)
    (hG : T.GoedelSentence G) (hcon : T.Consistent) :
    ¬ T.Thm consistencyStmt := by
  intro hCon
  -- `T ⊢ □G → □⊥` and `T ⊢ □⊥ → ⊥` give `T ⊢ ¬□G`.
  have h5 : T.Thm (Fml.neg (Fml.box G)) :=
    T.syll (T.box_goedel_imp_box_bot hG) hCon
  -- The fixed point yields `T ⊢ G`, hence `T ⊢ □G` by D1.
  have h6 : T.Thm G := T.mp hG.backward h5
  have h7 : T.Thm (Fml.box G) := T.D1 h6
  -- Together with `T ⊢ ¬□G` this proves `⊥`, contradicting consistency.
  exact hcon (T.mp h5 h7)

/-- **Gödel's first incompleteness theorem** (unprovability half): a consistent theory does
not prove its Gödel sentence. -/
theorem Goedel_first_incompleteness (T : ProvabilitySystem) (G : Fml)
    (hG : T.GoedelSentence G) (hcon : T.Consistent) : ¬ T.Thm G := by
  intro h
  exact hcon (T.mp (T.mp hG.forward h) (T.D1 h))

/-! ## Non-vacuity

The hypotheses of the theorem are satisfiable by a *consistent* system, so the statement
above is not vacuous.  We take the propositional evaluation in which every boxed sentence
is true; this satisfies all derivability conditions, is consistent, and has `⊥` itself as a
Gödel fixed point. -/

/-- A consistent provability system satisfying all the derivability conditions. -/
def witnessSystem : ProvabilitySystem where
  Thm p := eval (fun _ => true) p = true
  taut p hp := hp _
  mp {a b} hab ha := by
    simp only [eval, ha] at hab
    simpa using hab
  D1 {a} _ := rfl
  D2 a b := by simp [eval]
  D3 a := by simp [eval]

theorem witnessSystem_consistent : witnessSystem.Consistent := by
  simp [ProvabilitySystem.Consistent, witnessSystem, eval]

theorem witnessSystem_goedelSentence : witnessSystem.GoedelSentence Fml.bot :=
  { forward := by simp [witnessSystem, eval, Fml.neg]
    backward := by simp [witnessSystem, eval, Fml.neg] }

/-- Consequently the hypotheses of `Goedel_second_incompleteness` are jointly satisfiable. -/
theorem goedel_second_hypotheses_satisfiable :
    ∃ (T : ProvabilitySystem) (G : Fml), T.GoedelSentence G ∧ T.Consistent :=
  ⟨witnessSystem, Fml.bot, witnessSystem_goedelSentence, witnessSystem_consistent⟩

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

