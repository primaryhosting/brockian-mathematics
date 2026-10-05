import RequestProject.CLT

/-!
# Convergence of the rescaled walk against smooth test functions

`Math2.walkLaw μ n t` is the law of `S_{⌊n t⌋} / √n`, where `S` is a random walk with step
distribution `μ`.  Here we prove that, for a centered step distribution with unit variance and
finite third absolute moment, the integrals of smooth test functions against `walkLaw μ n t`
converge to the corresponding integrals against the centered Gaussian law of variance `t`, which
is the law of Brownian motion at time `t`.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- The law of `S_p / √n`, the sum of `p` i.i.d. steps with law `μ`, rescaled by `1/√n`. -/

theorem integrable_abs_cube_gaussianReal (v : ℝ≥0) :
    Integrable (fun x : ℝ => |x| ^ 3) (gaussianReal 0 v) := by
  have h2 : MemLp (fun x : ℝ => x) 3 (gaussianReal 0 v) := by
    simpa using (memLp_id_gaussianReal (μ := 0) (v := v) 3)
  have h3 := h2.integrable_norm_rpow (by norm_num) (by norm_num)
  simp only [Real.norm_eq_abs] at h3
  have heq : (fun x : ℝ => |x| ^ (3 : ℝ≥0∞).toReal) = fun x : ℝ => |x| ^ (3 : ℕ) := by
    funext x
    rw [show ((3 : ℝ≥0∞).toReal) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [heq] at h3
  exact h3

