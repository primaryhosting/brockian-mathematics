/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u v w

namespace Frontier

/-- The canonical *model* extracted from a regulator: given a regulator action `a`,
it returns a system state that the regulator would answer with `a` (an arbitrary
state if there is none). -/
noncomputable def regulatorModel {S : Type u} {A : Type v} [Nonempty S] (reg : S → A) : A → S :=
  fun a =>
    letI := Classical.propDecidable
    if h : ∃ s : S, reg s = a then h.choose else Classical.choice inferInstance

/-- **Conant–Ashby good regulator theorem** (deterministic base case):
*every good regulator of a system is (contains) a model of that system.*

Setting: `S` is the set of system states (disturbances), `A` the set of regulator
actions, `Z` the set of outcomes, and `sys : S → A → Z` the system, whose outcome
depends both on the system state and on the regulator's action.  A (deterministic)
regulator is a map `reg : S → A`.

* `hgood` — the regulator is *good*: regulation is perfect, the outcome is always
  the single acceptable value `z₀`.
* `hdemand` — the system is *demanding*: one action cannot successfully regulate two
  distinct system states.  (Contrapositive form: distinct system states require
  distinct successful actions — this is exactly the situation in which regulation
  carries information about the system.)

Conclusion: the regulator *is a model of the system*.  Its action determines the
system state: `reg` is injective and the explicit map `regulatorModel reg : A → S`
reconstructs the system state from the regulator's action, consistently with the
observed regulation.  Hence the regulator's behaviour contains an isomorphic copy
(a model) of the system. -/
theorem good_regulator {S : Type u} {A : Type v} {Z : Type w} [Nonempty S]
    (sys : S → A → Z) (z₀ : Z) (reg : S → A)
    (hgood : ∀ s : S, sys s (reg s) = z₀)
    (hdemand : ∀ (a : A) (s s' : S), sys s a = z₀ → sys s' a = z₀ → s = s') :
    Function.Injective reg ∧
      (∀ s : S, regulatorModel reg (reg s) = s) ∧
      (∀ s : S, sys (regulatorModel reg (reg s)) (reg s) = z₀) := by
  -- The regulator is injective: two states sharing an action would have to be equal.
  have hinj : Function.Injective reg := by
    intro s s' hss'
    refine hdemand (reg s) s s' (hgood s) ?_
    rw [hss']
    exact hgood s'
  -- The extracted model recovers the system state from the regulator's action.
  have hmodel : ∀ s : S, regulatorModel reg (reg s) = s := by
    intro s
    have hex : ∃ t : S, reg t = reg s := ⟨s, rfl⟩
    have : regulatorModel reg (reg s) = hex.choose := by
      unfold regulatorModel
      exact dif_pos hex
    rw [this]
    exact hinj hex.choose_spec
  refine ⟨hinj, hmodel, ?_⟩
  intro s
  rw [hmodel s]
  exact hgood s

/-- "Containing a model" is *equivalent* to the regulator's action determining the
system state: a left inverse `A → S` for `reg` exists exactly when `reg` is injective. -/
theorem containsModel_iff_injective {S : Type u} {A : Type v} [Nonempty S] (reg : S → A) :
    (∃ model : A → S, ∀ s : S, model (reg s) = s) ↔ Function.Injective reg := by
  constructor
  · rintro ⟨model, hmodel⟩ s s' hss'
    rw [← hmodel s, ← hmodel s', hss']
  · intro hinj
    refine ⟨regulatorModel reg, fun s => ?_⟩
    have hex : ∃ t : S, reg t = reg s := ⟨s, rfl⟩
    have h : regulatorModel reg (reg s) = hex.choose := by
      unfold regulatorModel
      exact dif_pos hex
    rw [h]
    exact hinj hex.choose_spec

/-- Contrapositive form of the good regulator theorem: a regulator that fails to be a
model of the system — two distinct system states receiving the same action — cannot be
a good regulator of a demanding system. -/
theorem not_good_of_not_model {S : Type u} {A : Type v} {Z : Type w}
    (sys : S → A → Z) (z₀ : Z) (reg : S → A)
    (hdemand : ∀ (a : A) (s s' : S), sys s a = z₀ → sys s' a = z₀ → s = s')
    (s s' : S) (hne : s ≠ s') (hsame : reg s = reg s') :
    ¬ (∀ t : S, sys t (reg t) = z₀) := by
  intro hgood
  refine hne (hdemand (reg s) s s' (hgood s) ?_)
  rw [hsame]
  exact hgood s'

end Frontier

