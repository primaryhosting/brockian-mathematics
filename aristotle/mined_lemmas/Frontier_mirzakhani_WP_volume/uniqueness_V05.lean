import Mathlib
import RequestProject.Kernel
import RequestProject.TwoDim

/-!
# Weil–Petersson volume polynomials in low complexity

We record the Weil–Petersson volume polynomials `V_{0,3}`, `V_{0,4}` and `V_{0,5}`, the
right-hand sides of Mirzakhani's recursion in the cases `(g,n) = (0,4)` and `(0,5)`, and
verify the recursion in both cases, together with the fact that the recursion determines
the volume polynomial.
-/

open scoped BigOperators Real
open MeasureTheory Set Real

namespace Frontier

set_option maxHeartbeats 1000000

/-! ## The volume polynomials -/

/-- `V_{0,3} ≡ 1`: the moduli space of pairs of pants is a point. -/

lemma uniqueness_V05 (W : (Fin 5 → ℝ) → ℝ)
    (hW : ∀ L : Fin 5 → ℝ,
      HasDerivAt (fun x : ℝ => x * W (Function.update L 0 x)) (mirzRHS05 L) (L 0)) :
    ∀ L : Fin 5 → ℝ, L 0 ≠ 0 → W L = V05 L := by
  intro L hL0
  have hg : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y * W (Function.update L 0 y))
      (mirzRHS05 (Function.update L 0 x)) x := by
    intro x
    have h := hW (Function.update L 0 x)
    rw [Function.update_self] at h
    simpa [Function.update_idem] using h
  have hh : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y * V05 (Function.update L 0 y))
      (mirzRHS05 (Function.update L 0 x)) x := by
    intro x
    have h := hasDerivAt_V05 (Function.update L 0 x)
    rw [Function.update_self] at h
    simpa [Function.update_idem] using h
  have hd : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => y * W (Function.update L 0 y) - y * V05 (Function.update L 0 y)) 0 x := by
    intro x
    simpa using (hg x).sub (hh x)
  have hconst := is_const_of_deriv_eq_zero
    (f := fun y : ℝ => y * W (Function.update L 0 y) - y * V05 (Function.update L 0 y))
    (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv)
  have h0 := hconst (L 0) 0
  simp only [zero_mul, sub_self] at h0
  rw [Function.update_eq_self] at h0
  have hcancel : L 0 * W L = L 0 * V05 L := by linarith [h0]
  exact mul_left_cancel₀ hL0 hcancel

end Frontier

import Mathlib
import RequestProject.Kernel

/-!
# The two-dimensional moment identity

Mirzakhani's recursion contains, besides the one-dimensional `B`-terms, two-dimensional
integrals of the shape

`∫₀^∞ ∫₀^∞ x y H(x+y, t) V(x, …) V(y, …) dx dy`.

In the lowest complexity where such a term occurs, `(g,n) = (0,5)`, the volume factors are
the constant `V_{0,3} = 1`, so what is needed is the identity

`∫₀^∞ ∫₀^∞ x y H(x+y, t) dx dy = F₃(t)/6`.

We prove the general statement `∫₀^∞ ∫₀^∞ x y φ(x+y) dx dy = (1/6) ∫₀^∞ u³ φ(u) du`
for any measurable `φ` with an exponential majorant, using Fubini's theorem for the shear
`(x,y) ↦ (x, x+y)` of the plane together with the elementary convolution
`∫₀^u x (u-x) dx = u³/6`, and then specialise to `φ = H(·, t)`.
-/

open scoped Real
open MeasureTheory Set Real

namespace Frontier

set_option maxHeartbeats 1000000

/-! ## The weight `wt x = x · 1_{x>0}` -/

/-- `wt x = x` for `x > 0` and `wt x = 0` otherwise. -/
