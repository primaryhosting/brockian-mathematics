/-
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Every continuous self-map of the closed 2-disk has a fixed point.

Mathlib does not contain Brouwer's fixed point theorem, so it is developed here.  The proof is the
classical degree-theoretic argument, carried out through the homotopy lifting property for
covering maps (`IsCoveringMap.liftHomotopy`) applied to the covering `Circle.exp : ℝ → Circle`:

* `Math.sub_eq_sub_of_circleExp_eq`: two continuous real functions on a preconnected space with
  the same image under `Circle.exp` differ by a constant (lifts are unique up to a constant).
* `Math.lift_endpoint_eq_of_homotopy_from_const`: if a homotopy of loops in the circle starts at
  a constant loop, then any continuous lift of its terminal loop has equal endpoints, i.e. the
  terminal loop has winding number `0`.
* `Math.brouwer_2d_complex`: if a continuous self-map `f` of the closed unit disk in `ℂ` had no
  fixed point, then `v z = (z - f z)/‖z - f z‖` would define a map of the disk into the circle;
  restricted to the boundary circle it is never antipodal to the identity, so it has winding
  number `1`, contradicting the previous lemma applied to the homotopy `(t, s) ↦ v (t e^{2πis})`.
* `Math.brouwer_2d`: transported to `EuclideanSpace ℝ (Fin 2)` along the linear isometry
  equivalence `Complex.orthonormalBasisOneI.repr`.
-/

namespace Math

open Complex Metric Set unitInterval

/-- Two continuous real functions on a preconnected space whose images under `Circle.exp` agree
differ by a constant. -/

theorem mem_slitPlane_of_norm_one {u : ℂ} (h : ‖u‖ = 1) (h2 : u ≠ -1) :
    u ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra hc
  push_neg at hc
  obtain ⟨hre, him⟩ := hc
  apply h2
  have h3 : u.re ^ 2 + u.im ^ 2 = 1 := by
    have h4 : Complex.normSq u = 1 := by rw [Complex.normSq_eq_norm_sq, h]; norm_num
    simpa [Complex.normSq_apply, sq] using h4
  have : u.re = -1 := by nlinarith [him, sq_nonneg u.re]
  apply Complex.ext <;> simp [this, him]

/-- **Brouwer's fixed point theorem in dimension 2**, complex form: every continuous self-map
of the closed unit disk in `ℂ` has a fixed point. -/
