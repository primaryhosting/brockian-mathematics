/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-!
## Setting

We formalise the deterministic (base) case of the Conant–Ashby "Good Regulator"
theorem: *every good regulator of a system is (contains) a model of that system*.

The set‑up is Conant and Ashby's:

* `S` is the set of disturbances / states of the regulated system,
* `R` is the set of actions available to the regulator,
* `Z` is the set of outcomes,
* `sys : S → R → Z` is the system: it maps a disturbance and a regulatory action
  to an outcome,
* `goal : Z` is the single acceptable ("good") outcome.

A regulator is a map `ρ : S → R` (it observes the disturbance and picks an
action). It is *good* when the outcome is always acceptable, i.e. the outcome
variable is constant — the deterministic form of "the entropy of the outcome is
minimal".

The system is *regular* at `goal` when for each disturbance exactly one action
achieves the goal; this is Conant and Ashby's standing assumption that the
optimal response is well defined.

The conclusion is that a good regulator *is* a model of the system: its mapping
is uniquely determined by the system, `ρ s` being exactly the system's optimal
response to `s`; equivalently, from `ρ` alone one can read off, for every
disturbance and action, whether that action is the successful one. Any two good
regulators therefore coincide.

No Mathlib result states this theorem; the argument is elementary and the only
library lemma it needs is function extensionality (`funext`), used to pass from
pointwise agreement of two good regulators to equality of the two mappings.
The file therefore has no imports and is axiom-clean.

Finally, "contains a model": a regulator whose action is computed through an
internal representation, `ρ = act ∘ rep`, must have an internal representation
`rep` which already distinguishes disturbances at least as finely as the model
does, and through which the model factors.
-/

section

universe u v w x

variable {S : Type u} {R : Type v} {Z : Type w}

/-- A regulator `ρ` is **good** for the system `sys` with target outcome `goal`
when every disturbance is met with an action producing the target outcome. -/
def IsGoodRegulator (sys : S → R → Z) (goal : Z) (ρ : S → R) : Prop :=
  ∀ s, sys s (ρ s) = goal

/-- The system `sys` is **regular** at `goal` when every disturbance admits a
unique successful action. -/
def RegularAt (sys : S → R → Z) (goal : Z) : Prop :=
  ∀ s, ∃ r, sys s r = goal ∧ ∀ r', sys s r' = goal → r' = r

/-- A map `m : S → R` is a **model** of the system `sys` (relative to `goal`)
when it captures the whole success relation of the system: an action succeeds
against a disturbance exactly when it is the one prescribed by `m`. -/
def IsModelOf (sys : S → R → Z) (goal : Z) (m : S → R) : Prop :=
  ∀ s r, sys s r = goal ↔ r = m s

/-- **Good Regulator Theorem** (Conant–Ashby, deterministic base case).

If the system `sys` has a well-defined optimal response to each disturbance
(`RegularAt`), then every good regulator is a model of the system: the
regulator's mapping reproduces the system's success relation exactly. -/
theorem good_regulator {sys : S → R → Z} {goal : Z} (hreg : RegularAt sys goal)
    {ρ : S → R} (hgood : IsGoodRegulator sys goal ρ) :
    IsModelOf sys goal ρ := by
  intro s r
  obtain ⟨r₀, hr₀, huniq⟩ := hreg s
  constructor
  · intro hr
    rw [huniq r hr, huniq (ρ s) (hgood s)]
  · intro hr
    rw [hr]
    exact hgood s

/-- A good regulator is uniquely determined by the system: any two good
regulators are the same mapping. Hence the regulator's structure is not an
arbitrary choice but is forced by — is a model of — the system. -/
theorem good_regulator_unique {sys : S → R → Z} {goal : Z} (hreg : RegularAt sys goal)
    {ρ σ : S → R} (hρ : IsGoodRegulator sys goal ρ) (hσ : IsGoodRegulator sys goal σ) :
    ρ = σ := by
  funext s
  exact ((good_regulator hreg hσ) s (ρ s)).1 (hρ s)

/-- Conversely, a model of the system is a good regulator, so "good regulator"
and "model" are the same notion here. -/
theorem isGoodRegulator_of_isModelOf {sys : S → R → Z} {goal : Z}
    {m : S → R} (hm : IsModelOf sys goal m) :
    IsGoodRegulator sys goal m := fun s => (hm s (m s)).2 rfl

/-- **The regulator contains a model.**

Suppose the regulator acts through an internal representation: it maps the
disturbance `s` to an internal state `rep s`, and its action is a function
`act` of that internal state only. If the resulting regulator is good, then the
model of the system factors through the internal representation: the internal
states already carry all the information of the model. In particular
`rep s₁ = rep s₂` forces the two disturbances to require the same response. -/
theorem model_factors_through_representation {M : Type x} {sys : S → R → Z} {goal : Z}
    (hreg : RegularAt sys goal) (rep : S → M) (act : M → R)
    (hgood : IsGoodRegulator sys goal (act ∘ rep))
    {m : S → R} (hm : IsModelOf sys goal m) :
    m = act ∘ rep :=
  good_regulator_unique hreg (isGoodRegulator_of_isModelOf hm) hgood

/-- The model of a regular system exists (it is the optimal-response map), so
the hypotheses above are not vacuous. -/
theorem exists_isModelOf {sys : S → R → Z} {goal : Z} (hreg : RegularAt sys goal) :
    ∃ m, IsModelOf sys goal m := by
  refine ⟨fun s => Classical.choose (hreg s), fun s r => ?_⟩
  obtain ⟨hr₀, huniq⟩ := Classical.choose_spec (hreg s)
  exact ⟨fun h => huniq r h, fun h => h ▸ hr₀⟩

/-- The model of a regular system is unique. -/
theorem isModelOf_unique {sys : S → R → Z} {goal : Z} (hreg : RegularAt sys goal)
    {m m' : S → R} (hm : IsModelOf sys goal m) (hm' : IsModelOf sys goal m') :
    m = m' :=
  good_regulator_unique hreg (isGoodRegulator_of_isModelOf hm)
    (isGoodRegulator_of_isModelOf hm')

/-- Goodness in the form "the outcome variable is constant", i.e. its entropy is
minimal, without naming the acceptable outcome in advance. -/
def HasConstantOutcome (sys : S → R → Z) (ρ : S → R) : Prop :=
  ∃ z, ∀ s, sys s (ρ s) = z

/-- Good Regulator Theorem, stated with goodness as constancy of the outcome:
if the regulator holds the outcome constant at some value `z` at which the
system is regular, then the regulator is a model of the system relative to `z`. -/
theorem good_regulator_of_constantOutcome {sys : S → R → Z} {ρ : S → R}
    (hconst : HasConstantOutcome sys ρ)
    (hreg : ∀ z, (∀ s, sys s (ρ s) = z) → RegularAt sys z) :
    ∃ z, IsModelOf sys z ρ := by
  obtain ⟨z, hz⟩ := hconst
  exact ⟨z, good_regulator (hreg z hz) hz⟩

end

/-!
## A concrete instance

A two-state system in which the regulator must match the disturbance: the
outcome is acceptable (`true`) exactly when the action equals the disturbance.
Here the unique good regulator is the identity — literally a copy, i.e. a model,
of the disturbance. -/

/-- The matching system on `Bool`: the action succeeds iff it copies the
disturbance. -/
def matchSys : Bool → Bool → Bool := fun s r => (r == s)

theorem matchSys_regularAt : RegularAt matchSys true := by
  intro s
  refine ⟨s, ?_, ?_⟩
  · cases s <;> rfl
  · intro r' h
    cases r' <;> cases s <;> first | rfl | exact absurd h (by decide)

theorem matchSys_isGoodRegulator_id : IsGoodRegulator matchSys true id := by
  intro s; cases s <;> rfl

/-- In the matching system, every good regulator is the identity map: the
regulator is forced to be an exact model of the disturbance. -/
theorem matchSys_good_regulator_eq_id {ρ : Bool → Bool}
    (h : IsGoodRegulator matchSys true ρ) : ρ = id :=
  good_regulator_unique matchSys_regularAt h matchSys_isGoodRegulator_id

end Frontier

#print axioms Frontier.good_regulator
#print axioms Frontier.good_regulator_unique
#print axioms Frontier.model_factors_through_representation
#print axioms Frontier.exists_isModelOf
#print axioms Frontier.good_regulator_of_constantOutcome
#print axioms Frontier.matchSys_good_regulator_eq_id

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

