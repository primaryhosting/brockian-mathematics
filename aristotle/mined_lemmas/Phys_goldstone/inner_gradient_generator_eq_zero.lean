import Mathlib

/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Noether identity.**  If the potential `V` (with gradient field `G`) is invariant under a
one-parameter flow `Φ` whose infinitesimal generator is `K` (i.e. `Φ 0 = id` and
`(d/dt) Φ t x |_{t=0} = K x`), then the gradient of `V` is everywhere orthogonal to the
direction of the symmetry orbit. -/

theorem inner_gradient_generator_eq_zero
    {V : E → ℝ} {G : E → E} {K : E →L[ℝ] E} {Φ : ℝ → E → E}
    (hV : ∀ x, HasFDerivAt V (innerSL ℝ (G x)) x)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hgen : ∀ x, HasDerivAt (fun t => Φ t x) (K x) 0)
    (hinv : ∀ t x, V (Φ t x) = V x) (x : E) :
    ⟪G x, K x⟫ = 0 := by
  have hVx : HasFDerivAt V (innerSL ℝ (G x)) (Φ 0 x) := by rw [hΦ0 x]; exact hV x
  have hcomp : HasDerivAt (fun t => V (Φ t x)) (⟪G x, K x⟫) 0 := by
    simpa [Function.comp] using hVx.comp_hasDerivAt 0 (hgen x)
  have hconst : HasDerivAt (fun t => V (Φ t x)) 0 0 := by
    simpa [hinv] using (hasDerivAt_const (0 : ℝ) (V x))
  exact hcomp.unique hconst

/-- **Goldstone's theorem.**

Setting: a potential `V` on a real inner product space `E`, with gradient field `G`
(`hV`) and Hessian `H` at the vacuum `v` (`hH`, the derivative of the gradient field);
the Hessian is symmetric (`hHsymm`, Clairaut/Schwarz).  The potential is invariant under a
continuous one-parameter group of symmetries `Φ` with infinitesimal generator `K`
(`hΦ0`, `hgen`, `hinv`).  The point `v` is a vacuum, i.e. a stationary point of `V` (`hvac`),
and the symmetry is *spontaneously broken* at `v`: the vacuum is not invariant, its orbit
direction `K v` is nonzero (`hbroken`).

Conclusion: the mass matrix `H` (the Hessian of the potential at the vacuum) has a nonzero
kernel vector, i.e. there is a massless mode — the Goldstone boson.  Indeed the massless
direction is exactly the broken symmetry direction `K v`. -/
