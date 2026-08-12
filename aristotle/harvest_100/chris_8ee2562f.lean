/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalize Gödel's second incompleteness theorem in its standard abstract
(Hilbert–Bernays–Löb) form: *no consistent theory `T` whose provability predicate
satisfies the derivability conditions proves its own consistency*.

The arithmetization of syntax is packaged in the usual way.  For a recursively
axiomatized theory `T` extending `PA`, Gödel numbering yields a provability
formula `Pr_T(⌜·⌝)` in the language of `T`, and the Hilbert–Bernays–Löb
derivability conditions hold:

* `D1` : `T ⊢ φ  ⟹  T ⊢ Pr_T(⌜φ⌝)`               (formalized soundness of proofs)
* `D2` : `T ⊢ Pr_T(⌜φ → ψ⌝) → (Pr_T(⌜φ⌝) → Pr_T(⌜ψ⌝))`   (internal modus ponens)
* `D3` : `T ⊢ Pr_T(⌜φ⌝) → Pr_T(⌜Pr_T(⌜φ⌝)⌝)`     (formalized `D1`)

together with closure of `T ⊢ ·` under propositional logic, and the diagonal
lemma, which produces a Gödel sentence `G` with `T ⊢ G ↔ ¬Pr_T(⌜G⌝)`.

`ProvabilitySystem` below is exactly this data: a language of formulas built from
`⊥`, `→` and the unary provability operator `box` (`box φ` denotes
`Pr_T(⌜φ⌝)`), a deducibility predicate `Thm` closed under propositional
tautologies and modus ponens, and the three derivability conditions.  The
consistency statement of `T` is the formula `Con := ¬ box ⊥`, i.e.
`¬Pr_T(⌜0=1⌝)`.

The main theorem `Frontier.Goedel_second_incompleteness` states: if `T` is
consistent and `G` is a Gödel fixed point, then `T ⊬ Con`.  We also record the
first incompleteness theorem `Frontier.Goedel_first_incompleteness`
(`T ⊬ G`) and Löb's theorem, from which the second incompleteness theorem
follows as well.
-/

namespace Frontier

/-- Formulas of the language of a theory, presented in the modal (provability
logic) signature: propositional atoms, falsity, implication, and the unary
provability operator `box p`, which stands for the arithmetized statement
"`p` is provable in `T`". -/
inductive Formula : Type
  | atom : Nat → Formula
  | bot : Formula
  | imp : Formula → Formula → Formula
  | box : Formula → Formula
  deriving DecidableEq

namespace Formula

/-- Negation, `¬p := p → ⊥`. -/
def neg (p : Formula) : Formula := imp p bot

/-- Truth value of a formula under a propositional valuation `v`, where atoms
and boxed formulas are treated as propositional atoms. -/
def eval (v : Formula → Prop) : Formula → Prop
  | atom n => v (atom n)
  | bot => False
  | imp p q => eval v p → eval v q
  | box p => v (box p)

/-- A formula is a propositional tautology if it is true under every valuation
(with boxed subformulas read as atoms). -/
def Tautology (p : Formula) : Prop := ∀ v : Formula → Prop, eval v p

end Formula

open Formula

/-- An abstract provability system: a deducibility predicate `Thm` (read
`T ⊢ ·`) that contains all propositional tautologies, is closed under modus
ponens, and whose provability operator `box` satisfies the three
Hilbert–Bernays–Löb derivability conditions.  Any recursively axiomatized
theory extending `PA`, with `box` interpreted as its arithmetized provability
predicate, gives rise to such a system. -/
structure ProvabilitySystem where
  /-- `Thm p` means that the theory proves the formula `p`. -/
  Thm : Formula → Prop
  /-- The theory proves every propositional tautology. -/
  taut : ∀ {p : Formula}, Tautology p → Thm p
  /-- The theory is closed under modus ponens. -/
  mp : ∀ {p q : Formula}, Thm (imp p q) → Thm p → Thm q
  /-- First derivability condition: provable formulas are provably provable. -/
  D1 : ∀ {p : Formula}, Thm p → Thm (box p)
  /-- Second derivability condition: internal modus ponens. -/
  D2 : ∀ p q : Formula, Thm (imp (box (imp p q)) (imp (box p) (box q)))
  /-- Third derivability condition: internalized `D1`. -/
  D3 : ∀ p : Formula, Thm (imp (box p) (box (box p)))

namespace ProvabilitySystem

variable (T : ProvabilitySystem)

/-- The theory is consistent when it does not prove `⊥`. -/
def Consistent : Prop := ¬ T.Thm bot

end ProvabilitySystem

/-- The consistency statement `Con_T := ¬ Pr_T(⌜⊥⌝)` of the theory. -/
def Con : Formula := neg (box bot)

variable {T : ProvabilitySystem}

/-- Transitivity of provable implication (a propositional consequence). -/
theorem Thm.trans {p q r : Formula} (h₁ : T.Thm (imp p q)) (h₂ : T.Thm (imp q r)) :
    T.Thm (imp p r) := by
  refine T.mp (T.mp (T.taut (p := imp (imp p q) (imp (imp q r) (imp p r))) ?_) h₁) h₂
  intro v
  simp only [eval]
  intro hpq hqr hp
  exact hqr (hpq hp)

/-- Key lemma behind the second incompleteness theorem: for a Gödel fixed point
`G` (satisfying `T ⊢ G → ¬box G`), the theory proves `box G → box ⊥`. -/
theorem box_goedel_imp_box_bot {G : Formula} (hG : T.Thm (imp G (neg (box G)))) :
    T.Thm (imp (box G) (box bot)) := by
  have h1 : T.Thm (imp (box G) (box (neg (box G)))) :=
    T.mp (T.D2 G (neg (box G))) (T.D1 hG)
  have h2 : T.Thm (imp (box (neg (box G))) (imp (box (box G)) (box bot))) :=
    T.D2 (box G) bot
  have h3 : T.Thm (imp (box G) (box (box G))) := T.D3 G
  refine T.mp (T.mp (T.mp (T.taut (p := imp (imp (box G) (box (neg (box G))))
    (imp (imp (box (neg (box G))) (imp (box (box G)) (box bot)))
      (imp (imp (box G) (box (box G))) (imp (box G) (box bot))))) ?_) h1) h2) h3
  intro v
  simp only [eval, neg]
  intro k1 k2 k3 hbG
  exact k2 (k1 hbG) (k3 hbG)

/-- **Gödel's first incompleteness theorem** (the unprovability half): a
consistent theory satisfying the derivability conditions does not prove its
Gödel sentence `G`. -/
theorem Goedel_first_incompleteness (hcon : T.Consistent) {G : Formula}
    (hG : T.Thm (imp G (neg (box G)))) : ¬ T.Thm G := fun hGthm =>
  hcon (T.mp (T.mp hG hGthm) (T.D1 hGthm))

/-- **Gödel's second incompleteness theorem.**

No consistent theory `T` that is recursively axiomatized and extends `PA` proves
its own consistency: writing `box` for the arithmetized provability predicate of
`T` (so that the Hilbert–Bernays–Löb derivability conditions `D1`, `D2`, `D3`
hold) and `Con = ¬ box ⊥` for the consistency statement of `T`, if `T` is
consistent and `G` is a Gödel sentence for `T` (a fixed point of `¬ box ·`,
supplied by the diagonal lemma), then `T ⊬ Con`. -/
theorem Goedel_second_incompleteness (T : ProvabilitySystem) (hcon : T.Consistent)
    (G : Formula) (hG1 : T.Thm (imp G (neg (box G)))) (hG2 : T.Thm (imp (neg (box G)) G)) :
    ¬ T.Thm Con := by
  intro hC
  have key : T.Thm (imp (box G) (box bot)) := box_goedel_imp_box_bot hG1
  have h4 : T.Thm (neg (box G)) := by
    refine T.mp (T.mp (T.taut (p := imp (imp (box G) (box bot))
      (imp (neg (box bot)) (neg (box G)))) ?_) key) hC
    intro v
    simp only [eval, neg]
    intro hbb hnb hbG
    exact hnb (hbb hbG)
  exact Goedel_first_incompleteness hcon hG1 (T.mp hG2 h4)

/-- The second incompleteness theorem, stated with the diagonal lemma as an
existential hypothesis: if the theory is consistent and admits a Gödel fixed
point, it does not prove its own consistency. -/
theorem Goedel_second_incompleteness_of_diagonal (T : ProvabilitySystem) (hcon : T.Consistent)
    (hdiag : ∃ G : Formula, T.Thm (imp G (neg (box G))) ∧ T.Thm (imp (neg (box G)) G)) :
    ¬ T.Thm Con := by
  obtain ⟨G, hG1, hG2⟩ := hdiag
  exact Goedel_second_incompleteness T hcon G hG1 hG2

/-- **Löb's theorem**: if for every formula the diagonal lemma supplies a fixed
point of `box · → p`, and `T ⊢ box p → p`, then `T ⊢ p`. -/
theorem Loeb (T : ProvabilitySystem)
    (hdiag : ∀ p : Formula, ∃ L : Formula,
      T.Thm (imp L (imp (box L) p)) ∧ T.Thm (imp (imp (box L) p) L))
    {p : Formula} (hp : T.Thm (imp (box p) p)) : T.Thm p := by
  obtain ⟨L, hL1, hL2⟩ := hdiag p
  have h1 : T.Thm (imp (box L) (box (imp (box L) p))) :=
    T.mp (T.D2 L (imp (box L) p)) (T.D1 hL1)
  have h2 : T.Thm (imp (box (imp (box L) p)) (imp (box (box L)) (box p))) :=
    T.D2 (box L) p
  have h3 : T.Thm (imp (box L) (box (box L))) := T.D3 L
  have h4 : T.Thm (imp (box L) (box p)) := by
    refine T.mp (T.mp (T.mp (T.taut (p := imp (imp (box L) (box (imp (box L) p)))
      (imp (imp (box (imp (box L) p)) (imp (box (box L)) (box p)))
        (imp (imp (box L) (box (box L))) (imp (box L) (box p))))) ?_) h1) h2) h3
    intro v
    simp only [eval]
    intro k1 k2 k3 hbL
    exact k2 (k1 hbL) (k3 hbL)
  have h5 : T.Thm (imp (box L) p) := Thm.trans h4 hp
  have h6 : T.Thm L := T.mp hL2 h5
  exact T.mp h5 (T.D1 h6)

/-!
## Non-vacuity

The hypotheses of the main theorem are satisfiable: the "everything is provable
according to `box`" system, in which `Thm p` means that `p` is true under the
valuation sending every atom and every boxed formula to `True`, is a consistent
provability system possessing a Gödel fixed point.  (This is the one-world
Kripke model with no accessible worlds.)  Hence the theorem below is not
vacuously true.
-/

/-- A consistent provability system: truth under the valuation making every
atomic and boxed formula true. -/
def trivialSystem : ProvabilitySystem where
  Thm p := eval (fun _ => True) p
  taut h := h _
  mp h₁ h₂ := h₁ h₂
  D1 _ := trivial
  D2 _ _ := fun _ _ => trivial
  D3 _ := fun _ => trivial

theorem trivialSystem_consistent : trivialSystem.Consistent := id

/-- `⊥` is a Gödel fixed point for `trivialSystem`, so the hypotheses of the
second incompleteness theorem are jointly satisfiable. -/
theorem trivialSystem_hasFixedPoint :
    ∃ G : Formula, trivialSystem.Thm (imp G (neg (box G))) ∧
      trivialSystem.Thm (imp (neg (box G)) G) :=
  ⟨bot, fun h => h.elim, fun h => h trivial⟩

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

