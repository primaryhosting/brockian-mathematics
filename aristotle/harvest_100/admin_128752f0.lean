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

open Complex intervalIntegral

/-- The off-diagonal entry of the Bloch Hamiltonian of the SSH (Su–Schrieffer–Heeger)
model with intracell hopping `v` and intercell hopping `w`:
`h(k) = v + w e^{i k}`.  The chiral (sublattice) symmetry of the model forces the
Bloch Hamiltonian to be off-diagonal, so the whole topology is carried by `h`. -/
noncomputable def sshBloch (v w : ℝ) (k : ℝ) : ℂ :=
  (v : ℂ) + (w : ℂ) * Complex.exp (k * Complex.I)

/-- The winding number of the SSH off-diagonal element around the origin,
`(2πi)⁻¹ ∫₀^{2π} h'(k)/h(k) dk`. -/
noncomputable def sshWinding (v w : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ k in (0 : ℝ)..(2 * Real.pi), deriv (sshBloch v w) k / sshBloch v w k

/-- The derivative of the SSH Bloch off-diagonal element. -/
lemma hasDerivAt_sshBloch (v w : ℝ) (k : ℝ) :
    HasDerivAt (sshBloch v w) ((w : ℂ) * Complex.I * Complex.exp (k * Complex.I)) k := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 k := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := k))
  have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I k := by
    simpa using h1.mul_const Complex.I
  have h3 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((k : ℂ) * Complex.I) * Complex.I) k := h2.cexp
  have h4 : HasDerivAt (sshBloch v w)
      ((w : ℂ) * (Complex.exp ((k : ℂ) * Complex.I) * Complex.I)) k :=
    (h3.const_mul (w : ℂ)).const_add (v : ℂ)
  have hval : (w : ℂ) * Complex.I * Complex.exp ((k : ℂ) * Complex.I)
      = (w : ℂ) * (Complex.exp ((k : ℂ) * Complex.I) * Complex.I) := by ring
  rw [hval]
  exact h4

lemma deriv_sshBloch (v w : ℝ) (k : ℝ) :
    deriv (sshBloch v w) k = (w : ℂ) * Complex.I * Complex.exp (k * Complex.I) :=
  (hasDerivAt_sshBloch v w k).deriv

/-- The SSH winding integral is the winding number of the unit circle around the
point `-v/w`, i.e. a contour integral of `(z - (-v/w))⁻¹` over the unit circle. -/
lemma sshWinding_eq_circleIntegral (v w : ℝ) (hw : w ≠ 0) :
    sshWinding v w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∮ z in C(0, 1), (z - (-((v : ℂ) / (w : ℂ))))⁻¹ := by
  have hwC : (w : ℂ) ≠ 0 := by exact_mod_cast hw
  unfold sshWinding circleIntegral
  congr 1
  refine intervalIntegral.integral_congr ?_
  intro k _
  show deriv (sshBloch v w) k / sshBloch v w k
      = deriv (circleMap 0 1) k • (circleMap 0 1 k - (-((v : ℂ) / (w : ℂ))))⁻¹
  have hcm : circleMap 0 1 k = Complex.exp (k * Complex.I) := by
    simp [circleMap]
  rw [deriv_sshBloch, deriv_circleMap, hcm]
  have hden : Complex.exp ((k : ℂ) * Complex.I) - (-((v : ℂ) / (w : ℂ)))
      = ((v : ℂ) + (w : ℂ) * Complex.exp ((k : ℂ) * Complex.I)) / (w : ℂ) := by
    field_simp
    ring
  rw [smul_eq_mul, hden, inv_div, sshBloch, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- **Topological classification of the SSH model.**  The winding number of the
off-diagonal Bloch element `h(k) = v + w e^{i k}` around the origin is the integer
`1` in the topological phase `|v| < |w|`, and the integer `0` in the trivial phase
`|w| < |v|`. -/
theorem ssh_winding_invariant (v w : ℝ) :
    (|v| < |w| → sshWinding v w = 1) ∧ (|w| < |v| → sshWinding v w = 0) := by
  constructor
  · intro hvw
    have hw : w ≠ 0 := by
      rintro rfl
      simp only [abs_zero] at hvw
      linarith [abs_nonneg v]
    have hmem : (-((v : ℂ) / (w : ℂ))) ∈ Metric.ball (0 : ℂ) 1 := by
      have : ‖(-((v : ℂ) / (w : ℂ)))‖ = |v| / |w| := by simp
      simp only [Metric.mem_ball, dist_zero_right, this]
      rw [div_lt_one (by positivity [abs_pos.mpr hw])]
      exact hvw
    rw [sshWinding_eq_circleIntegral v w hw,
      circleIntegral.integral_sub_inv_of_mem_ball hmem]
    field_simp
  · intro hwv
    rcases eq_or_ne w 0 with hw | hw
    · subst hw
      simp [sshWinding, deriv_sshBloch]
    · have habs : (1 : ℝ) < |v| / |w| := by
        rw [lt_div_iff₀ (abs_pos.mpr hw)]
        simpa using hwv
      have hzero : ∮ z in C((0 : ℂ), 1), (z - (-((v : ℂ) / (w : ℂ))))⁻¹ = 0 := by
        refine DiffContOnCl.circleIntegral_eq_zero (by norm_num) ?_
        have hne : ∀ z ∈ closure (Metric.ball (0 : ℂ) 1),
            z - (-((v : ℂ) / (w : ℂ))) ≠ 0 := by
          intro z hz hcontra
          rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)] at hz
          have hz1 : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
          have hzeq : z = -((v : ℂ) / (w : ℂ)) := sub_eq_zero.mp hcontra
          rw [hzeq] at hz1
          have : ‖(-((v : ℂ) / (w : ℂ)))‖ = |v| / |w| := by simp
          rw [this] at hz1
          linarith
        constructor
        · intro z hz
          exact ((differentiableAt_id.sub_const _).inv
            (hne z (subset_closure hz))).differentiableWithinAt
        · intro z hz
          exact ((continuousAt_id.sub continuousAt_const).inv₀
            (hne z hz)).continuousWithinAt
      rw [sshWinding_eq_circleIntegral v w hw, hzero, mul_zero]

end Frontier

