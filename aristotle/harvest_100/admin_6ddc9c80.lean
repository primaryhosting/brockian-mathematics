import Mathlib

/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
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

/-- A *regulated system* in the sense of Conant–Ashby.

`S` is the set of states of the system (the disturbances acting on the regulator),
`R` is the set of states (actions) available to the regulator, and `Z` is the set of
outcomes.  The outcome is jointly determined by the system state and the regulator's
action via `outcome`, and `goal` is the single outcome the regulator is trying to
enforce. -/
structure RegulatedSystem (S R Z : Type*) where
  /-- The outcome produced by a system state together with a regulator action. -/
  outcome : S → R → Z
  /-- The outcome the regulator must enforce. -/
  goal : Z

variable {S R Z : Type*}

/-- A regulator `ρ`, i.e. a rule assigning an action to each system state, is *good*
(perfectly regulating) when it always enforces the goal outcome. -/
def IsGoodRegulator (sys : RegulatedSystem S R Z) (ρ : S → R) : Prop :=
  ∀ s : S, sys.outcome s (ρ s) = sys.goal

/-- The system is *tight* (has no regulatory slack) when for every system state at most
one regulator action enforces the goal.  This is Conant–Ashby's standing assumption that
the regulator carries no superfluous variety: the good outcome is not reachable in two
different ways from the same system state. -/
def Tight (sys : RegulatedSystem S R Z) : Prop :=
  ∀ (s : S) (r r' : R), sys.outcome s r = sys.goal → sys.outcome s r' = sys.goal → r = r'

/-- The set of system states that the regulator state `r` is a correct response to.
This is the *model* of the system carried by the regulator. -/
def modelOf (sys : RegulatedSystem S R Z) (r : R) : Set S :=
  {s : S | sys.outcome s r = sys.goal}

/-!
## The Good Regulator Theorem (Conant–Ashby)

Every good regulator of a system is (contains) a model of that system.

In the deterministic base case formalized here, a good regulator `ρ` of a tight system
is shown to be:

* **unique** — it is the only rule that perfectly regulates the system, so it is forced
  by the system itself rather than chosen freely;
* **a homomorphic image of the system** — the regulator's state `ρ s` determines exactly
  which actions succeed against `s`, i.e. it determines the system's requirement; two
  system states mapped to the same regulator state are indistinguishable in what they
  demand of the regulator;
* **a model** — there is a map `model : R → Set S` from regulator states to sets of
  system states such that every state is in the model of its own regulator state, every
  state in the model of `r` is correctly handled by `r`, and the models of distinct
  regulator states are disjoint.  Thus the regulator's internal state is an isomorphic
  copy (a model) of the relevant structure of the system.
-/
theorem good_regulator (sys : RegulatedSystem S R Z) (ρ : S → R)
    (hgood : IsGoodRegulator sys ρ) (htight : Tight sys) :
    (∀ ρ' : S → R, IsGoodRegulator sys ρ' → ρ' = ρ) ∧
    (∀ s s' : S, ρ s = ρ s' → ∀ r : R,
      (sys.outcome s r = sys.goal ↔ sys.outcome s' r = sys.goal)) ∧
    (∃ model : R → Set S,
      (∀ s : S, s ∈ model (ρ s)) ∧
      (∀ (r : R) (s : S), s ∈ model r → sys.outcome s r = sys.goal) ∧
      (∀ (r r' : R) (s : S), s ∈ model r → s ∈ model r' → r = r')) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ρ' hρ'
    funext s
    exact htight s (ρ' s) (ρ s) (hρ' s) (hgood s)
  · intro s s' hss' r
    constructor
    · intro h
      have : r = ρ s := htight s r (ρ s) h (hgood s)
      subst this
      rw [hss']
      exact hgood s'
    · intro h
      have : r = ρ s' := htight s' r (ρ s') h (hgood s')
      subst this
      rw [← hss']
      exact hgood s
  · refine ⟨modelOf sys, ?_, ?_, ?_⟩
    · intro s
      exact hgood s
    · intro r s hs
      exact hs
    · intro r r' s hs hs'
      exact htight s r r' hs hs'

/-- Two system states are *behaviourally equivalent* when they demand exactly the same
regulator actions.  The system is *faithful* (irredundantly presented) when distinct
system states are behaviourally distinct. -/
def Faithful (sys : RegulatedSystem S R Z) : Prop :=
  ∀ s s' : S, (∀ r : R, (sys.outcome s r = sys.goal ↔ sys.outcome s' r = sys.goal)) → s = s'

/-- **The regulator is an isomorphic model of the system.**  For a faithful, tight
system, a good regulator `ρ` is injective, and hence induces an equivalence between the
system's state space `S` and the set of regulator states actually used, which sends each
system state to the action the regulator takes on it.  This is the sharpest form of
"every good regulator is a model of the system": the regulator's internal state space is
an isomorphic copy of the system's state space. -/
theorem good_regulator_isomorphic_model (sys : RegulatedSystem S R Z) (ρ : S → R)
    (hgood : IsGoodRegulator sys ρ) (htight : Tight sys) (hfaithful : Faithful sys) :
    Function.Injective ρ ∧ ∃ e : S ≃ Set.range ρ, ∀ s : S, (e s : R) = ρ s := by
  have hinj : Function.Injective ρ := by
    intro s s' hss'
    exact hfaithful s s' ((good_regulator sys ρ hgood htight).2.1 s s' hss')
  exact ⟨hinj, Equiv.ofInjective ρ hinj, fun _ => rfl⟩

/-- **Requisite variety.**  A faithful, tight system can only be perfectly regulated by a
regulator with at least as many states as the system has. -/
theorem requisite_variety [Fintype S] [Fintype R] (sys : RegulatedSystem S R Z)
    (ρ : S → R) (hgood : IsGoodRegulator sys ρ) (htight : Tight sys)
    (hfaithful : Faithful sys) :
    Fintype.card S ≤ Fintype.card R :=
  Fintype.card_le_of_injective ρ (good_regulator_isomorphic_model sys ρ hgood htight hfaithful).1

/-- The hypotheses of `good_regulator` are non-vacuous, and in the exemplary case the
regulator is forced to be a faithful copy of the system: for the system whose good
outcome requires the regulator to match the disturbance, the unique good regulator is a
bijection `S ≃ R`, i.e. literally an isomorphic model of the system. -/
theorem good_regulator_nonvacuous :
    ∃ (sys : RegulatedSystem Bool Bool Bool) (ρ : Bool → Bool),
      IsGoodRegulator sys ρ ∧ Tight sys ∧ Function.Bijective ρ := by
  refine ⟨⟨fun s r => decide (s = r), true⟩, id, ?_, ?_, ?_⟩
  · intro s
    simp
  · intro s r r' h h'
    simp only [decide_eq_true_eq] at h h'
    exact h.symm.trans h'
  · exact Function.bijective_id

end Frontier

