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

