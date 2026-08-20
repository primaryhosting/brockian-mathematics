import Mathlib

/-!
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
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

set_option grind.warning false

namespace Frontier

open Complex Metric

/-- The off-diagonal entry of the Bloch Hamiltonian of the Su-Schrieffer-Heeger (SSH) chain
with intracell hopping `v` and intercell hopping `w`:
`h(k) = v + w e^{i k}`.  Chiral (sublattice) symmetry forces the Bloch Hamiltonian to be
off-diagonal, so the whole topological content of the model is carried by this loop
`k ↦ h(k)` in the complex plane. -/

lemma sshWinding_trivial (v w : ℝ) (hw : 0 ≤ w) (h : w < |v|) : sshWinding v w = 0 := by
  have hne : ∀ z ∈ closedBall ((v : ℂ)) w, z ≠ 0 := by
    intro z hz hz0
    rw [mem_closedBall, Complex.dist_eq] at hz
    rw [hz0] at hz
    simp only [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs] at hz
    exact absurd hz (not_le.2 h)
  have hcont : ContinuousOn (fun z : ℂ => z⁻¹) (closedBall ((v : ℂ)) w) := by
    intro z hz
    exact (continuousAt_inv₀ (hne z hz)).continuousWithinAt
  have hdiff : ∀ z ∈ ball ((v : ℂ)) w \ (∅ : Set ℂ), DifferentiableAt ℂ (fun z : ℂ => z⁻¹) z := by
    intro z hz
    exact differentiableAt_inv (hne z (ball_subset_closedBall hz.1))
  have := circleIntegral_eq_zero_of_differentiable_on_off_countable hw
    (Set.countable_empty) hcont hdiff
  rw [sshWinding_eq, this, mul_zero]

/-- **The SSH topological invariant.**

For the Su-Schrieffer-Heeger chain with hoppings `v` (intracell) and `w > 0` (intercell),
the winding number of the Bloch off-diagonal element `h(k) = v + w e^{ik}` around the origin,
`W = (2πi)⁻¹ ∫_0^{2π} h'(k)/h(k) dk`, is an integer, and it classifies the two phases:
it equals `1` in the topological phase `|v| < w` and `0` in the trivial phase `|v| > w`.

The key Mathlib inputs are `circleIntegral.integral_sub_inv_of_mem_ball`
(Cauchy's integral formula for `(z - w)⁻¹` on a circle around an interior point) and
`circleIntegral_eq_zero_of_differentiable_on_off_countable` (Cauchy's theorem). -/
