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
noncomputable def sshOffDiag (v w : ℝ) (k : ℝ) : ℂ :=
  (v : ℂ) + (w : ℂ) * Complex.exp (k * Complex.I)

/-- The SSH winding number

`ν(v, w) = (2 π i)⁻¹ ∫₀^{2π} h'(k) / h(k) dk`,

the winding number about the origin of the loop `k ↦ h(k) = v + w e^{ik}`. -/
noncomputable def sshWinding (v w : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ k in (0 : ℝ)..(2 * Real.pi),
      (Complex.I * (w : ℂ) * Complex.exp (k * Complex.I)) /
        ((v : ℂ) + (w : ℂ) * Complex.exp (k * Complex.I))

/-- `k ↦ i w e^{ik}` really is the derivative of the SSH off-diagonal entry
`k ↦ v + w e^{ik}`, so `sshWinding` is the winding number of `sshOffDiag`. -/
theorem deriv_sshOffDiag (v w : ℝ) (k : ℝ) :
    deriv (fun t : ℝ => sshOffDiag v w t) k =
      Complex.I * (w : ℂ) * Complex.exp (k * Complex.I) := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I)
      (Complex.I) k := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := k)).mul_const Complex.I)
  have h2 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((k : ℂ) * Complex.I) * Complex.I) k := h1.cexp
  have h3 : HasDerivAt (fun t : ℝ => sshOffDiag v w t)
      ((w : ℂ) * (Complex.exp ((k : ℂ) * Complex.I) * Complex.I)) k := by
    simpa [sshOffDiag] using (h2.const_mul (w : ℂ)).const_add ((v : ℂ))
  rw [h3.deriv]; ring

/-- The defining `[0, 2π]`-integral of `sshWinding` is the contour integral of
`z ↦ w / (v + w z)` over the unit circle. -/
theorem sshWinding_integral_eq_circleIntegral (v w : ℝ) :
    (∫ k in (0 : ℝ)..(2 * Real.pi),
        (Complex.I * (w : ℂ) * Complex.exp (k * Complex.I)) /
          ((v : ℂ) + (w : ℂ) * Complex.exp (k * Complex.I)))
      = ∮ z in C(0, 1), (w : ℂ) / ((v : ℂ) + (w : ℂ) * z) := by
  rw [circleIntegral]
  refine intervalIntegral.integral_congr ?_
  intro θ _
  simp [deriv_circleMap, circleMap, smul_eq_mul]
  ring

/-- Topological phase: the contour integral evaluates to `2π i` when `|v| < |w|`. -/
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
theorem sshWinding_eq_one (v w : ℝ) (h : |v| < |w|) : sshWinding v w = 1 := by
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Complex.ext_iff, Real.pi_ne_zero]
  rw [sshWinding, sshWinding_integral_eq_circleIntegral, circleIntegral_ssh_topological v w h]
  field_simp

/-- In the trivial phase `|w| < |v|` the SSH winding number equals `0`. -/
theorem sshWinding_eq_zero (v w : ℝ) (h : |w| < |v|) : sshWinding v w = 0 := by
  rw [sshWinding, sshWinding_integral_eq_circleIntegral, circleIntegral_ssh_trivial v w h]
  ring

/--
**SSH winding invariant.**

For the SSH chain with hoppings `v, w`, whenever the bulk gap is open (`|v| ≠ |w|`)
the winding number of the Bloch off-diagonal `k ↦ v + w e^{ik}` is a well-defined
*integer*, and it classifies the two phases:

* it equals `1` in the topological phase `|v| < |w|`;
* it equals `0` in the trivial phase `|w| < |v|`;
* it is an integer for every gapped configuration;
* it is *invariant* within each phase: two gapped configurations lying in the same
  phase have the same winding number.
-/
theorem ssh_winding_invariant :
    (∀ v w : ℝ, |v| < |w| → sshWinding v w = 1) ∧
    (∀ v w : ℝ, |w| < |v| → sshWinding v w = 0) ∧
    (∀ v w : ℝ, |v| ≠ |w| → ∃ n : ℤ, sshWinding v w = (n : ℂ)) ∧
    (∀ v₁ w₁ v₂ w₂ : ℝ, |v₁| < |w₁| → |v₂| < |w₂| → sshWinding v₁ w₁ = sshWinding v₂ w₂) ∧
    (∀ v₁ w₁ v₂ w₂ : ℝ, |w₁| < |v₁| → |w₂| < |v₂| → sshWinding v₁ w₁ = sshWinding v₂ w₂) := by
  refine ⟨sshWinding_eq_one, sshWinding_eq_zero, ?_, ?_, ?_⟩
  · intro v w hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨1, by rw [sshWinding_eq_one v w h]; norm_num⟩
    · exact ⟨0, by rw [sshWinding_eq_zero v w h]; norm_num⟩
  · intro v₁ w₁ v₂ w₂ h₁ h₂
    rw [sshWinding_eq_one v₁ w₁ h₁, sshWinding_eq_one v₂ w₂ h₂]
  · intro v₁ w₁ v₂ w₂ h₁ h₂
    rw [sshWinding_eq_zero v₁ w₁ h₁, sshWinding_eq_zero v₂ w₂ h₂]

end Frontier

#print axioms Frontier.ssh_winding_invariant

