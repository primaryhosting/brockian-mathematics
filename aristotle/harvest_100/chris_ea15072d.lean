import Mathlib

/-!
# Mean Value
Category: Pure Mathematics
Target: Math.mean_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to be the very first commands in a file,
-- so the module documentation header above is placed immediately after `import Mathlib`.

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Math

open Set

/-- **Lagrange's Mean Value Theorem.**  If `a < b`, `f : ℝ → ℝ` is continuous on `[a, b]` and
differentiable at every point of the open interval `(a, b)`, then there is a point `c ∈ (a, b)`
with `deriv f c = (f b - f a) / (b - a)`. -/
theorem mean_value {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b))
    (hfd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_hasDerivAt_eq_slope f (deriv f) hab hfc fun x hx => (hfd x hx).hasDerivAt

/-- Mean Value Theorem for a globally differentiable function: for `a < b` there is
`c ∈ (a, b)` with `deriv f c = (f b - f a) / (b - a)`. -/
theorem mean_value_of_differentiable {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : Differentiable ℝ f) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  mean_value hab (hf.continuous.continuousOn) fun x _ => hf x

end Math

