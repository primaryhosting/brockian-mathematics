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

open Complex Metric intervalIntegral

/-- The off-diagonal entry of the Bloch Hamiltonian of the SSH (Su–Schrieffer–Heeger)
model with intracell hopping `v` and intercell hopping `w`:
`h v w k = v + w * exp (i k)`.  Chiral symmetry forces the Bloch Hamiltonian to have the
form `![![0, h k], ![conj (h k), 0]]`, so the spectral gap is open exactly when `h k ≠ 0`
for all `k`. -/
noncomputable def sshOffDiag (v w : ℝ) (k : ℝ) : ℂ :=
  (v : ℂ) + (w : ℂ) * Complex.exp (k * Complex.I)

/-- The winding number of the SSH off-diagonal element around the origin,
`(2πi)⁻¹ ∫₀^{2π} h'(k) / h(k) dk`, where `h = sshOffDiag v w`. -/
noncomputable def sshWinding (v w : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ k in (0 : ℝ)..(2 * Real.pi),
      (Complex.I * (w : ℂ) * Complex.exp (k * Complex.I)) / sshOffDiag v w k

/-- The derivative of the SSH off-diagonal element in the quasimomentum `k`. -/
lemma hasDerivAt_sshOffDiag (v w : ℝ) (k : ℝ) :
    HasDerivAt (fun t : ℝ => sshOffDiag v w t)
      (Complex.I * (w : ℂ) * Complex.exp (k * Complex.I)) k := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I k := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := k)).mul_const Complex.I
  have h2 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((k : ℂ) * Complex.I) * Complex.I) k := h1.cexp
  have h3 := (h2.const_mul (w : ℂ)).const_add ((v : ℝ) : ℂ)
  simpa [sshOffDiag, mul_comm, mul_left_comm, mul_assoc] using h3

/-- The defining integral of the winding number is the contour integral of `z⁻¹`
over the circle traced out by `k ↦ v + w e^{ik}`. -/
lemma sshWinding_eq_circleIntegral (v w : ℝ) :
    sshWinding v w = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∮ z in C((v : ℂ), w), z⁻¹ := by
  unfold sshWinding
  congr 1
  rw [circleIntegral]
  refine intervalIntegral.integral_congr ?_
  intro k _
  simp only [deriv_circleMap, circleMap, sshOffDiag, smul_eq_mul, zero_add]
  rw [div_eq_mul_inv]
  ring_nf

/-- Topological phase: if `|v| < w` the origin lies inside the circle and the winding
number is `1`. -/
lemma sshWinding_of_abs_lt (v w : ℝ) (h : |v| < w) : sshWinding v w = 1 := by
  have hmem : (0 : ℂ) ∈ Metric.ball ((v : ℂ)) w := by
    simpa [Complex.dist_eq, Complex.norm_real] using h
  have hint : (∮ z in C((v : ℂ), w), z⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
    simpa using circleIntegral.integral_sub_inv_of_mem_ball hmem
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero, Complex.ofReal_eq_zero]
  rw [sshWinding_eq_circleIntegral, hint, inv_mul_cancel₀ hne]

/-- Trivial phase: if `w < |v|` the origin lies outside the circle and the winding
number is `0`. -/
lemma sshWinding_of_lt_abs (v w : ℝ) (hw : 0 ≤ w) (h : w < |v|) : sshWinding v w = 0 := by
  have hne : ∀ z ∈ Metric.closedBall ((v : ℂ)) w, z ≠ 0 := by
    intro z hz hz0
    rw [Metric.mem_closedBall, Complex.dist_eq, hz0] at hz
    simp only [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs] at hz
    linarith
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => z⁻¹) (closure (Metric.ball ((v : ℂ)) w)) := by
    intro z hz
    exact (differentiableAt_inv (hne z (closure_ball_subset_closedBall hz))).differentiableWithinAt
  have hzero : (∮ z in C((v : ℂ), w), z⁻¹) = 0 :=
    DiffContOnCl.circleIntegral_eq_zero hw hdiff.diffContOnCl
  rw [sshWinding_eq_circleIntegral, hzero, mul_zero]

/-- The winding integrand `h'(k) / h(k)` is `2π`-periodic in the quasimomentum. -/
lemma sshIntegrand_periodic (v w : ℝ) :
    Function.Periodic
      (fun k : ℝ => (Complex.I * (w : ℂ) * Complex.exp (k * Complex.I)) / sshOffDiag v w k)
      (2 * Real.pi) := by
  intro k
  have hexp : Complex.exp (((k + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((k : ℂ) * Complex.I) := by
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  simp only [sshOffDiag, hexp]

/-- Reversing the sign of the intercell hopping `w` amounts to the shift `k ↦ k + π`
of the quasimomentum, so it leaves the winding number unchanged. -/
lemma sshWinding_neg (v w : ℝ) : sshWinding v (-w) = sshWinding v w := by
  unfold sshWinding
  congr 1
  have hshift : ∀ k : ℝ,
      (Complex.I * ((-w : ℝ) : ℂ) * Complex.exp (k * Complex.I)) / sshOffDiag v (-w) k
        = (Complex.I * (w : ℂ) * Complex.exp (((k + Real.pi : ℝ)) * Complex.I))
            / sshOffDiag v w (k + Real.pi) := by
    intro k
    have hexp : Complex.exp (((k + Real.pi : ℝ) : ℂ) * Complex.I)
        = -Complex.exp ((k : ℂ) * Complex.I) := by
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]
    simp only [sshOffDiag, hexp]
    push_cast
    ring_nf
  calc ∫ k in (0 : ℝ)..(2 * Real.pi),
          (Complex.I * ((-w : ℝ) : ℂ) * Complex.exp (k * Complex.I)) / sshOffDiag v (-w) k
      = ∫ k in (0 : ℝ)..(2 * Real.pi),
          (Complex.I * (w : ℂ) * Complex.exp (((k + Real.pi : ℝ)) * Complex.I))
            / sshOffDiag v w (k + Real.pi) :=
        intervalIntegral.integral_congr (fun k _ => hshift k)
    _ = ∫ k in (0 + Real.pi : ℝ)..(2 * Real.pi + Real.pi),
          (Complex.I * (w : ℂ) * Complex.exp (k * Complex.I)) / sshOffDiag v w k :=
        intervalIntegral.integral_comp_add_right
          (fun k : ℝ => (Complex.I * (w : ℂ) * Complex.exp ((k : ℝ) * Complex.I))
            / sshOffDiag v w k) Real.pi
    _ = ∫ k in (0 : ℝ)..(2 * Real.pi),
          (Complex.I * (w : ℂ) * Complex.exp (k * Complex.I)) / sshOffDiag v w k := by
        have h := (sshIntegrand_periodic v w).intervalIntegral_add_eq Real.pi 0
        simpa [add_comm] using h

/-- **SSH winding invariant.**  For the SSH model with hoppings `v` (intracell) and
`w > 0` (intercell) and an open bulk gap (`|v| ≠ w`), the winding number of the
off-diagonal Bloch element around the origin is an *integer* topological invariant:
it equals `1` in the topological phase `|v| < w` and `0` in the trivial phase `w < |v|`. -/
theorem ssh_winding_invariant (v w : ℝ) (hw : 0 < w) (hgap : |v| ≠ w) :
    sshWinding v w = ((if |v| < w then (1 : ℤ) else 0 : ℤ) : ℂ) := by
  rcases lt_or_gt_of_ne hgap with h | h
  · rw [if_pos h, sshWinding_of_abs_lt v w h]
    norm_num
  · rw [if_neg (not_lt.2 h.le), sshWinding_of_lt_abs v w hw.le h]
    norm_num

/-- **SSH winding invariant, general hoppings.**  For any real hoppings with `w ≠ 0` and an
open bulk gap (`|v| ≠ |w|`), the winding number is the integer `1` in the topological phase
`|v| < |w|` and `0` in the trivial phase `|w| < |v|`. -/
theorem ssh_winding_invariant_of_ne_zero (v w : ℝ) (hw : w ≠ 0) (hgap : |v| ≠ |w|) :
    sshWinding v w = ((if |v| < |w| then (1 : ℤ) else 0 : ℤ) : ℂ) := by
  rcases lt_or_gt_of_ne hw with hneg | hpos
  · have habs : |w| = -w := abs_of_neg hneg
    have hpos' : 0 < -w := neg_pos.2 hneg
    have hmain := ssh_winding_invariant v (-w) hpos' (by rwa [← habs])
    have hswap : sshWinding v w = sshWinding v (-w) := by
      simpa using sshWinding_neg v (-w)
    rw [hswap, hmain, habs]
  · have habs : |w| = w := abs_of_pos hpos
    rw [habs]
    exact ssh_winding_invariant v w hpos (by rwa [← habs])

end Frontier

