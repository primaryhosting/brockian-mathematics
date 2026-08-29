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
