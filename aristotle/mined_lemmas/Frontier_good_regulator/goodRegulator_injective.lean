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
