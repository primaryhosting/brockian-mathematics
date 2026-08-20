/-!
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: a Lean module doc comment (`/-! ... -/`) must precede any `import`
command, so this module is deliberately self-contained and uses no imports.  The
`Escalates` relation below is the reflexive-transitive closure of the one-step
escalation relation; it is the analogue of Mathlib's `Relation.ReflTransGen`, and
`PCA.Isolation.Escalates.mono` is the analogue of `Relation.ReflTransGen.mono`,
which is the Mathlib lemma that does the essential work of the target theorem.
-/

namespace PCA.Isolation

universe u

/-- `Escalates g a b` : starting from privilege `a`, the isolation engine's
one-step escalation relation `g` allows reaching privilege `b` in finitely many
steps.  This is the reflexive-transitive closure of `g`. -/
inductive Escalates {P : Type u} (g : P → P → Prop) : P → P → Prop
  | refl (a : P) : Escalates g a a
  | tail {a b c : P} : Escalates g a b → g b c → Escalates g a c

namespace Escalates

theorem mono {P : Type u} {g h : P → P → Prop} (hgh : ∀ x y, g x y → h x y)
    {a b : P} (hab : Escalates g a b) : Escalates h a b := by
  induction hab with
  | refl => exact Escalates.refl _
  | tail _ hstep ih => exact ih.tail (hgh _ _ hstep)

end Escalates

/-- `escape g S` is the set of privileges an attacker can obtain (i.e. escape to)
from the initial privilege set `S`, using the escalation relation `g`. -/

def escape {P : Type u} (g : P → P → Prop) (S : P → Prop) : P → Prop :=
  fun q => ∃ p, S p ∧ Escalates g p q

/-- Soundness of the model, part 1: the initial privileges are escapable. -/

theorem priv_escape_monotone {P : Type u} {g h : P → P → Prop} {S T : P → Prop}
    (hgh : ∀ x y, g x y → h x y) (hST : ∀ p, S p → T p) :
    ∀ q, escape g S q → escape h T q := by
  rintro q ⟨p, hp, hchain⟩
  exact ⟨p, hST p hp, hchain.mono hgh⟩

end PCA.Isolation

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
