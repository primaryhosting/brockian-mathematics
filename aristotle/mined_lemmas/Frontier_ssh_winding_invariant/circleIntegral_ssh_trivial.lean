/-
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Complex

/-!
## The Su–Schrieffer–Heeger (SSH) chain

The SSH model is a one-dimensional two-band tight-binding chain with alternating
intracell hopping `v` and intercell hopping `w`.  Its Bloch Hamiltonian is

`H(k) = Re(h k) • σₓ + Im(h k) • σ_y`,  where  `h k = v + w * exp (i k)`,

i.e. `H(k)` is purely off-diagonal (chiral / sublattice symmetry).  The spectrum is
`± |h k|`, so the chain is gapped exactly when `h k ≠ 0` for all `k`, which happens
precisely when `|v| ≠ |w|`.

The topological invariant is the winding number of the complex-valued loop
`k ↦ h k`, `k ∈ [0, 2π]`, around the origin:

`ν = (1 / (2 π i)) ∫₀^{2π} (d/dk) log (h k) dk = (1 / (2 π i)) ∫₀^{2π} h'(k) / h(k) dk`.
-/

/-- The off-diagonal entry of the SSH Bloch Hamiltonian:
`h(k) = v + w·e^{i k}`, for intracell hopping `v` and intercell hopping `w`. -/

theorem circleIntegral_ssh_trivial (v w : ℝ) (h : |w| < |v|) :
    (∮ z in C(0, 1), (w : ℂ) / ((v : ℂ) + (w : ℂ) * z)) = 0 := by
  have hvpos : (0 : ℝ) < |v| := lt_of_le_of_lt (abs_nonneg w) h
  have hne : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, (v : ℂ) + (w : ℂ) * z ≠ 0 := by
    intro z hz hcon
    have hz1 : ‖z‖ ≤ 1 := by simpa using hz
    have hval : (w : ℂ) * z = -(v : ℂ) := by linear_combination hcon
    have h1 : ‖(w : ℂ) * z‖ ≤ |w| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |w| * ‖z‖ ≤ |w| * 1 := mul_le_mul_of_nonneg_left hz1 (abs_nonneg w)
        _ = |w| := by ring
    rw [hval] at h1
    simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs] at h1
    linarith
  refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable (by norm_num)
    Set.countable_empty (ContinuousOn.div continuousOn_const (by fun_prop) hne) ?_
  intro z hz
  exact DifferentiableAt.div (differentiableAt_const _) (by fun_prop)
    (hne z (Metric.ball_subset_closedBall hz.1))

/-- In the topological phase `|v| < |w|` the SSH winding number equals `1`. -/
