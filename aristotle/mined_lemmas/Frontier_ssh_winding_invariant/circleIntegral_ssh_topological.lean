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

theorem circleIntegral_ssh_topological (v w : ℝ) (h : |v| < |w|) :
    (∮ z in C(0, 1), (w : ℂ) / ((v : ℂ) + (w : ℂ) * z)) = 2 * (Real.pi : ℂ) * Complex.I := by
  have hwpos : (0 : ℝ) < |w| := lt_of_le_of_lt (abs_nonneg v) h
  have hw : w ≠ 0 := by
    intro hw0; rw [hw0] at hwpos; simp at hwpos
  have hw' : (w : ℂ) ≠ 0 := by exact_mod_cast hw
  have key : ∀ z : ℂ, (w : ℂ) / ((v : ℂ) + (w : ℂ) * z) = (1 : ℂ) / (z - (-(v : ℂ) / (w : ℂ))) := by
    intro z
    rcases eq_or_ne (z - (-(v : ℂ) / (w : ℂ))) 0 with h0 | h0
    · have hz : z = -(v : ℂ) / (w : ℂ) := by linear_combination h0
      have hzero : (v : ℂ) + (w : ℂ) * z = 0 := by rw [hz]; field_simp; ring
      simp [hzero, h0]
    · field_simp; ring
  simp_rw [key]
  have hmem : (-(v : ℂ) / (w : ℂ)) ∈ Metric.ball (0 : ℂ) 1 := by
    simp only [Metric.mem_ball, dist_zero_right, norm_div, norm_neg, Complex.norm_real,
      Real.norm_eq_abs]
    exact (div_lt_one hwpos).mpr h
  have := circleIntegral_div_sub_of_differentiable_on_off_countable (R := 1) (c := 0)
    (w := -(v : ℂ) / (w : ℂ)) (s := ∅) Set.countable_empty hmem (f := fun _ => (1 : ℂ))
    continuousOn_const (fun z _ => differentiableAt_const _)
  simpa using this

/-- Trivial phase: the contour integral vanishes when `|w| < |v|`. -/
