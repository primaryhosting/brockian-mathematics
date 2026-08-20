/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u v w

/-- A regulator `ρ : S → R` chooses, for each state `s` of the system, a regulatory action
`ρ s`.  The outcome of state `s` under action `r` is `φ s r`, and the regulator is *good*
(perfectly regulating) when the outcome is always the target value `z₀`. -/
def GoodRegulator {S : Type u} {R : Type v} {Z : Type w}
    (phi : S → R → Z) (z₀ : Z) (rho : S → R) : Prop :=
  ∀ s, phi s (rho s) = z₀

/-- A good regulator is injective on system states, provided that no single action achieves the
target outcome for two different states. -/
theorem goodRegulator_injective {S : Type u} {R : Type v} {Z : Type w}
    (phi : S → R → Z) (z₀ : Z)
    (hdist : ∀ s s' r, phi s r = z₀ → phi s' r = z₀ → s = s')
    (rho : S → R) (hgood : GoodRegulator phi z₀ rho) :
    Function.Injective rho := by
  intro s s' h
  exact hdist s s' (rho s) (hgood s) (h ▸ hgood s')

/-- **Conant–Ashby good regulator theorem** (deterministic, perfect-regulation case).

Assume that no single action succeeds for two different system states (`hdist`: the actions
achieving the target outcome discriminate between states).  Then any good regulator `rho`
*contains a model of the system*: `rho` is injective, and there is a map `m : R → S` recovering
the system state from the regulator's action (`m ∘ rho = id`), which moreover simulates every
dynamics `d` of the system (`m (rho (d s)) = d (m (rho s))`).  In other words, the regulator's
internal repertoire of actions carries an isomorphic copy — a model — of the system's states,
and this copy is a homomorphic image of the system's dynamics. -/
theorem good_regulator {S : Type u} {R : Type v} {Z : Type w} [Nonempty S]
    (phi : S → R → Z) (z₀ : Z)
    (hdist : ∀ s s' r, phi s r = z₀ → phi s' r = z₀ → s = s')
    (rho : S → R) (hgood : GoodRegulator phi z₀ rho) :
    Function.Injective rho ∧
      ∃ m : R → S, (∀ s, m (rho s) = s) ∧
        ∀ (d : S → S) (s : S), m (rho (d s)) = d (m (rho s)) := by
  have hinj : Function.Injective rho := goodRegulator_injective phi z₀ hdist rho hgood
  have key : ∀ r : R, ∃ s : S, ∀ t : S, rho t = r → s = t := by
    intro r
    by_cases h : ∃ t : S, rho t = r
    · obtain ⟨t, ht⟩ := h
      exact ⟨t, fun u hu => hinj (ht.trans hu.symm)⟩
    · exact ⟨Classical.choice inferInstance, fun t ht => absurd ⟨t, ht⟩ h⟩
  refine ⟨hinj, fun r => (key r).choose, ?_, ?_⟩
  · intro s
    show (key (rho s)).choose = s
    exact (key (rho s)).choose_spec s rfl
  · intro d s
    show (key (rho (d s))).choose = d ((key (rho s)).choose)
    rw [(key (rho (d s))).choose_spec (d s) rfl, (key (rho s)).choose_spec s rfl]

/-- Under the stronger hypothesis that for each state the successful action is unique, the good
regulator is unique: it *is* the model of the system, not merely one of many. -/
theorem good_regulator_unique {S : Type u} {R : Type v} {Z : Type w}
    (phi : S → R → Z) (z₀ : Z)
    (huniq : ∀ s r r', phi s r = z₀ → phi s r' = z₀ → r = r')
    (rho rho' : S → R) (h : GoodRegulator phi z₀ rho) (h' : GoodRegulator phi z₀ rho') :
    rho = rho' :=
  funext fun s => huniq s (rho s) (rho' s) (h s) (h' s)

/-- Sanity check: the hypotheses of `good_regulator` are satisfiable (the theorem is not
vacuous).  Here the system has two states, the regulator must match the state, and the target
outcome `true` is achieved exactly by the matching action. -/
example : Function.Injective (id : Bool → Bool) ∧
    ∃ m : Bool → Bool, (∀ s, m (id s) = s) ∧
      ∀ (d : Bool → Bool) (s : Bool), m (id (d s)) = d (m (id s)) :=
  good_regulator (fun s r => (s == r)) true
    (fun s s' r hs hs' => by
      simp only [beq_iff_eq] at hs hs'
      exact hs.trans hs'.symm)
    id (fun s => by simp)

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

