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

lemma uniqueness_V04 (W : (Fin 4 → ℝ) → ℝ)
    (hW : ∀ L : Fin 4 → ℝ,
      HasDerivAt (fun x : ℝ => x * W (Function.update L 0 x)) (mirzRHS04 L) (L 0)) :
    ∀ L : Fin 4 → ℝ, L 0 ≠ 0 → W L = V04 L := by
  intro L hL0
  have hg : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y * W (Function.update L 0 y))
      (mirzRHS04 (Function.update L 0 x)) x := by
    intro x
    have h := hW (Function.update L 0 x)
    rw [Function.update_self] at h
    simpa [Function.update_idem] using h
  have hh : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y * V04 (Function.update L 0 y))
      (mirzRHS04 (Function.update L 0 x)) x := by
    intro x
    have h := hasDerivAt_V04 (Function.update L 0 x)
    rw [Function.update_self] at h
    simpa [Function.update_idem] using h
  have hd : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => y * W (Function.update L 0 y) - y * V04 (Function.update L 0 y)) 0 x := by
    intro x
    simpa using (hg x).sub (hh x)
  have hconst := is_const_of_deriv_eq_zero
    (f := fun y : ℝ => y * W (Function.update L 0 y) - y * V04 (Function.update L 0 y))
    (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv)
  have h0 := hconst (L 0) 0
  simp only [zero_mul, sub_self] at h0
  rw [Function.update_eq_self] at h0
  have hcancel : L 0 * W L = L 0 * V04 L := by linarith [h0]
  exact mul_left_cancel₀ hL0 hcancel

/-! ## Mirzakhani's recursion for `(g,n) = (0,5)` -/

/-- The six ordered stable splittings of `{2,3,4,5}` into two pairs. -/
