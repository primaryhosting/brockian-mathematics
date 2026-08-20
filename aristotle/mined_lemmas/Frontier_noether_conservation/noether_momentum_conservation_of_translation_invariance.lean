/-
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- **Noether's theorem, one-dimensional (single degree of freedom) case.**

Setting: a Lagrangian `L : ℝ → ℝ → ℝ`, written `L q v` (position `q`, velocity `v`), and a
path `q : ℝ → ℝ`.  Along the path we write

* the *canonical momentum*  `p t = ∂L/∂v (q t, q' t) = deriv (fun w => L (q t) w) (deriv q t)`,
* the *generalized force*   `F t = ∂L/∂q (q t, q' t) = deriv (fun x => L x (deriv q t)) (q t)`.

Hypotheses:

* `hEL` is the **Euler–Lagrange equation** `d/dt p t = F t` (stated as `HasDerivAt`, which
  also encodes differentiability of the momentum along the path);
* `hsym` says that the infinitesimal variation `δq = φ` is a **symmetry of the action**:
  the first-order variation of the Lagrangian vanishes pointwise,
  `∂L/∂q · φ + ∂L/∂v · φ' = 0`.

Conclusion: the **Noether current** `J t = p t * φ t` is conserved, i.e. it takes the same
value at any two times.

The proof is the standard two-line computation: `J' = p' φ + p φ' = F φ + p φ' = 0` by the
product rule (`HasDerivAt.mul`), and a function on `ℝ` with vanishing derivative is constant
(`is_const_of_deriv_eq_zero`). -/

theorem noether_momentum_conservation_of_translation_invariance
    (L : ℝ → ℝ → ℝ) (q : ℝ → ℝ)
    (hinv : ∀ x y v : ℝ, L x v = L y v)
    (hEL : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => deriv (fun w : ℝ => L (q s) w) (deriv q s))
        (deriv (fun x : ℝ => L x (deriv q t)) (q t)) t) :
    ∀ t₀ t₁ : ℝ,
      deriv (fun w : ℝ => L (q t₀) w) (deriv q t₀)
        = deriv (fun w : ℝ => L (q t₁) w) (deriv q t₁) := by
  have hforce : ∀ t : ℝ, deriv (fun x : ℝ => L x (deriv q t)) (q t) = 0 := by
    intro t
    have : (fun x : ℝ => L x (deriv q t)) = fun _ : ℝ => L 0 (deriv q t) := by
      funext x; exact hinv x 0 (deriv q t)
    rw [this, deriv_const]
  have := noether_conservation L q (fun _ => 1) (differentiable_const 1) hEL (by
    intro t
    simp [hforce t])
  intro t₀ t₁
  simpa using this t₀ t₁

/-- Sanity check that the hypotheses of `Frontier.noether_conservation` are satisfiable
(the theorem is not vacuous): for the free particle `L q v = v ^ 2 / 2` on the straight-line
path `q t = t`, the Euler–Lagrange equation holds and the conserved momentum is `1`. -/
