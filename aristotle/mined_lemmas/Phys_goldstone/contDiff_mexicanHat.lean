import Mathlib
/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- **Goldstone's theorem** (classical field-theory / mechanical form).

Setting: `V : E → ℝ` is a potential on a real normed space `E`, invariant under a
one-parameter family `g : ℝ → (E ≃L[ℝ] E)` of continuous linear symmetries
(`hinv : ∀ t x, V (g t x) = V x`).  The vacuum `v` minimises `V` (`hmin`).
The symmetry is *spontaneously broken*: the orbit `t ↦ g t v` of the vacuum moves,
i.e. it has a nonzero velocity `w ≠ 0` at `t = 0`.

Conclusion: the mass matrix, i.e. the Hessian `fderiv ℝ (fderiv ℝ V) v` of the potential
at the vacuum, annihilates the nonzero vector `w`.  Thus there is a massless mode
(a Goldstone boson): a nonzero fluctuation direction with vanishing mass term. -/

lemma contDiff_mexicanHat : ContDiff ℝ 2 mexicanHat := by
  have h : ContDiff ℝ 2 (fun z : ℂ => ‖z‖ ^ 2) := by
    have : (fun z : ℂ => ‖z‖ ^ 2) = fun z : ℂ => z.re ^ 2 + z.im ^ 2 := by
      funext z
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    rw [this]
    exact (Complex.reCLM.contDiff.pow 2).add (Complex.imCLM.contDiff.pow 2)
  exact (h.sub contDiff_const).pow 2

/-- Goldstone's theorem applied to the Mexican-hat potential: the mass matrix at the
vacuum `v = 1` has a nonzero null vector, i.e. there is a massless mode. -/
