/-
# Mean Value
Category: Pure Mathematics
Target: Math.mean_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Set

namespace Math

/-- The auxiliary function used in the proof of the Mean Value Theorem: `f` corrected by the
linear function with slope `(f b - f a) / (b - a)`. -/

theorem mvtAux_hasDerivAt {f : ℝ → ℝ} {a b : ℝ} (hfd : DifferentiableOn ℝ f (Ioo a b))
    {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (mvtAux f a b) (deriv f x - (f b - f a) / (b - a)) x := by
  have hf : HasDerivAt f (deriv f x) x :=
    ((hfd x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  simpa using hf.sub (((hasDerivAt_id x).const_mul ((f b - f a) / (b - a))))

/-- **Lagrange's Mean Value Theorem.** If `a < b`, `f` is continuous on `[a, b]` and
differentiable on the open interval `(a, b)`, then there is a point `c ∈ (a, b)` with
`deriv f c = (f b - f a) / (b - a)`.

The proof is the classical one: apply Rolle's theorem to `f` corrected by the linear function
of slope `(f b - f a) / (b - a)`. -/
