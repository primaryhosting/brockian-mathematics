/-!
# Loeb Theorem
Category: Frontier — Set Theory
Target: Frontier.Loeb_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Löb's theorem: if `PA ⊢ (□φ → φ)` then `PA ⊢ φ`, where `□φ` denotes the arithmetized
provability statement `Prov_PA(⌜φ⌝)`.

The theorem is a consequence of exactly the following features of `PA` together with its
canonical provability predicate (this is the standard, and the only informative, way to
formalize it: the arithmetization of syntax plays no role in the argument beyond supplying
these facts):

* the provable sentences are closed under modus ponens and contain the axioms `K` and `S`
  of the implicational fragment of propositional logic;
* the Hilbert–Bernays–Löb derivability conditions:
  - `⊢ φ` implies `⊢ □φ` (necessitation / D1),
  - `⊢ □(φ → ψ) → (□φ → □ψ)` (D2),
  - `⊢ □φ → □□φ` (D3);
* the Gödel–Carnap diagonal lemma: for every sentence `φ` there is a sentence `ψ` with
  `⊢ ψ ↔ (□ψ → φ)`.

`Frontier.ProvabilitySystem` below packages precisely these data, and
`Frontier.Loeb_theorem` is Löb's theorem for any such system.

To show that the axioms are not vacuous, the second half of the file constructs a concrete,
consistent system `Frontier.Form` / `Frontier.Derivable` satisfying all of them (Section
`Concrete`), and derives from Löb's theorem the corresponding form of Gödel's second
incompleteness theorem.
-/

namespace Frontier

/-- A *provability system*: an abstract rendering of a theory such as `PA` together with its
provability predicate `□`.  The fields are the closure properties of `PA`-provability used in
Löb's argument: propositional logic (in the implicational fragment), the three
Hilbert–Bernays–Löb derivability conditions, and the diagonal lemma. -/
structure ProvabilitySystem where
  /-- The type of sentences of the theory. -/
  Sent : Type
  /-- Implication between sentences. -/
  imp : Sent → Sent → Sent
  /-- The provability operator: `box φ` is the arithmetized statement "`φ` is provable". -/
  box : Sent → Sent
  /-- `Prov φ` says that the theory proves `φ`. -/
  Prov : Sent → Prop
  /-- Axiom `K` of propositional logic. -/
  ax_k : ∀ a b, Prov (imp a (imp b a))
  /-- Axiom `S` of propositional logic. -/
  ax_s : ∀ a b c, Prov (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- Modus ponens. -/
  mp : ∀ {a b}, Prov (imp a b) → Prov a → Prov b
  /-- Derivability condition D1 (necessitation). -/
  nec : ∀ {a}, Prov a → Prov (box a)
  /-- Derivability condition D2 (distribution of `box` over implication). -/
  dist : ∀ a b, Prov (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Derivability condition D3 (provable `Σ₁`-completeness for provability statements). -/
  four : ∀ a, Prov (imp (box a) (box (box a)))
  /-- The diagonal lemma: for every `f` there is a sentence `p` provably equivalent to
  `box p → f`. -/
  diag : ∀ f, ∃ p, Prov (imp p (imp (box p) f)) ∧ Prov (imp (imp (box p) f) p)

namespace ProvabilitySystem

variable (S : ProvabilitySystem) {a b c : S.Sent}

/-- From `⊢ b` infer `⊢ a → b`. -/
theorem imp_const (h : S.Prov b) : S.Prov (S.imp a b) :=
  S.mp (S.ax_k b a) h

/-- From `⊢ a → (b → c)` and `⊢ a → b` infer `⊢ a → c`. -/
theorem imp_mp2 (h1 : S.Prov (S.imp a (S.imp b c))) (h2 : S.Prov (S.imp a b)) :
    S.Prov (S.imp a c) :=
  S.mp (S.mp (S.ax_s a b c) h1) h2

/-- Transitivity of provable implication. -/
theorem imp_trans (h1 : S.Prov (S.imp a b)) (h2 : S.Prov (S.imp b c)) : S.Prov (S.imp a c) :=
  S.imp_mp2 (S.imp_const h2) h1

end ProvabilitySystem

/-- **Löb's theorem.**  In any theory (such as `PA`) whose provability predicate `□` satisfies
the Hilbert–Bernays–Löb derivability conditions and for which the diagonal lemma holds:
if the theory proves `□φ → φ`, then it proves `φ`. -/
theorem Loeb_theorem (S : ProvabilitySystem) (f : S.Sent)
    (hf : S.Prov (S.imp (S.box f) f)) : S.Prov f := by
  obtain ⟨p, hp1, hp2⟩ := S.diag f
  -- `⊢ □p → □(□p → f)`
  have h3 : S.Prov (S.imp (S.box p) (S.box (S.imp (S.box p) f))) :=
    S.mp (S.dist p (S.imp (S.box p) f)) (S.nec hp1)
  -- `⊢ □p → (□□p → □f)`
  have h5 : S.Prov (S.imp (S.box p) (S.imp (S.box (S.box p)) (S.box f))) :=
    S.imp_trans h3 (S.dist (S.box p) f)
  -- `⊢ □p → □f`, using D3
  have h7 : S.Prov (S.imp (S.box p) (S.box f)) := S.imp_mp2 h5 (S.four p)
  -- `⊢ □p → f`
  have h8 : S.Prov (S.imp (S.box p) f) := S.imp_trans h7 hf
  -- hence `⊢ p`, hence `⊢ □p`, hence `⊢ f`
  exact S.mp h8 (S.nec (S.mp hp2 h8))

/-!
## A concrete consistent system satisfying all the hypotheses

The following inductive syntax and derivability relation form a system satisfying every axiom
of `ProvabilitySystem`; the constructor `fixL` provides the Gödel fixed points that the
diagonal lemma supplies in `PA`.  Theorem `Derivable_consistent` shows the system is
consistent, so the hypotheses of `Loeb_theorem` are not vacuous.
-/

namespace Concrete

/-- Formulas: propositional atoms, falsum, implication, the provability operator `box`, and a
designated Gödel fixed point `fixL f` (intended: a sentence saying "if I am provable, then
`f`"). -/
inductive Form : Type
  | atom : Nat → Form
  | bot : Form
  | imp : Form → Form → Form
  | box : Form → Form
  | fixL : Form → Form
  deriving DecidableEq

/-- Derivability in the concrete system. -/
inductive Derivable : Form → Prop
  | ax_k (a b) : Derivable (.imp a (.imp b a))
  | ax_s (a b c) :
      Derivable (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c)))
  | mp {a b} : Derivable (.imp a b) → Derivable a → Derivable b
  | nec {a} : Derivable a → Derivable (.box a)
  | dist (a b) : Derivable (.imp (.box (.imp a b)) (.imp (.box a) (.box b)))
  | four (a) : Derivable (.imp (.box a) (.box (.box a)))
  | fix_left (f) : Derivable (.imp (.fixL f) (.imp (.box (.fixL f)) f))
  | fix_right (f) : Derivable (.imp (.imp (.box (.fixL f)) f) (.fixL f))

/-- A one-point reflexive-free model: `box` is interpreted as truth, atoms as falsity, and a
fixed point `fixL f` as `f` itself. -/
def eval : Form → Prop
  | .atom _ => False
  | .bot => False
  | .imp a b => eval a → eval b
  | .box _ => True
  | .fixL a => eval a

/-- Soundness of `Derivable` with respect to `eval`. -/
theorem eval_of_derivable {a : Form} (h : Derivable a) : eval a := by
  induction h with
  | ax_k a b => intro ha _; exact ha
  | ax_s a b c => intro h1 h2 ha; exact h1 ha (h2 ha)
  | mp _ _ ih1 ih2 => exact ih1 ih2
  | nec _ _ => trivial
  | dist a b => intro _ _; trivial
  | four a => intro _; trivial
  | fix_left f => intro hf _; exact hf
  | fix_right f => intro h; exact h trivial

/-- The concrete system is consistent. -/
theorem Derivable_consistent : ¬ Derivable Form.bot := fun h => eval_of_derivable h

/-- The concrete system, packaged as a `ProvabilitySystem`. -/
def system : ProvabilitySystem where
  Sent := Form
  imp := Form.imp
  box := Form.box
  Prov := Derivable
  ax_k := Derivable.ax_k
  ax_s := Derivable.ax_s
  mp := Derivable.mp
  nec := Derivable.nec
  dist := Derivable.dist
  four := Derivable.four
  diag f := ⟨Form.fixL f, Derivable.fix_left f, Derivable.fix_right f⟩

/-- Löb's theorem for the concrete system. -/
theorem loeb (f : Form) (h : Derivable (.imp (.box f) f)) : Derivable f :=
  Loeb_theorem system f h

/-- **Gödel's second incompleteness theorem** for the concrete system: a consistent system of
this kind cannot prove its own consistency statement `□⊥ → ⊥`. -/
theorem not_derivable_consistency : ¬ Derivable (.imp (.box .bot) .bot) := fun h =>
  Derivable_consistent (loeb Form.bot h)

end Concrete

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

