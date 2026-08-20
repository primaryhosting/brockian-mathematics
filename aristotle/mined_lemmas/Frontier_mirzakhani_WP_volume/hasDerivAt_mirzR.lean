/-
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file formalizes **Mirzakhani's recursion** for the Weil–Petersson volumes
`V_{g,n}(L_1, …, L_n)` of moduli spaces of bordered hyperbolic surfaces of genus `g`
with `n` geodesic boundary components of lengths `L_1, …, L_n`, and proves a
Lean-checked *reduction*: the recursion, together with the two base values
`V_{0,3} = 1` and `V_{1,1}(L) = (L² + 4π²)/48`, determines **all** the volumes.

The recursion is stated in its integrated form, in terms of Mirzakhani's kernels

* `H(x, y) = 1/(1 + e^{(x+y)/2}) + 1/(1 + e^{(x-y)/2})`,
* `D(t, x, y) = 2 log ((e^{t/2} + e^{(x+y)/2}) / (e^{-t/2} + e^{(x+y)/2}))`,
* `R(t, y, x) = t - log ((cosh(y/2) + cosh((t+x)/2)) / (cosh(y/2) + cosh((t-x)/2)))`,

which are the antiderivatives (in the first variable, vanishing at `t = 0`) appearing in
Mirzakhani's integration formula.  We prove the two defining derivative identities
`∂_t D(t, x, y) = H(x + y, t)` and `∂_t R(t, y, x) = ½ (H(x, t+y) + H(x, t-y))`
(`Frontier.hasDerivAt_mirzD`, `Frontier.hasDerivAt_mirzR`), so that the integrated form
stated here is exactly the integral from `0` to `L₁` of the usual differentiated form
`∂_{L₁}(L₁ V_{g,n}) = A^{con} + A^{dcon} + B`.

What is proved here is the *reduction* step: no hyperbolic geometry is developed, and the
geometric fact that the actual Weil–Petersson volume functions satisfy the recursion is
taken as a hypothesis on the family `V`.  The theorem `Frontier.mirzakhani_WP_volume` says
that this hypothesis plus the base cases pins the family down uniquely, i.e. Mirzakhani's
recursion is a complete algorithm computing every `V_{g,n}`.
-/

open Real MeasureTheory

namespace Frontier

/-! ## Mirzakhani's kernels -/

/-- Mirzakhani's kernel `H(x, y) = 1/(1 + e^{(x+y)/2}) + 1/(1 + e^{(x-y)/2})`. -/

theorem hasDerivAt_mirzR (x y t : ℝ) :
    HasDerivAt (fun s => mirzR s y x) ((1 / 2) * (mirzH x (t + y) + mirzH x (t - y))) t := by
  have hc : ∀ u : ℝ, (0 : ℝ) < Real.cosh (y / 2) + Real.cosh u := by
    intro u
    have h1 := Real.one_le_cosh (y / 2)
    have h2 := Real.one_le_cosh u
    linarith
  have key : ∀ s : ℝ, mirzR s y x =
      s - (Real.log (Real.cosh (y / 2) + Real.cosh ((s + x) / 2))
            - Real.log (Real.cosh (y / 2) + Real.cosh ((s - x) / 2))) := by
    intro s
    rw [mirzR, Real.log_div (ne_of_gt (hc _)) (ne_of_gt (hc _))]
  simp only [key]
  have d1 : HasDerivAt (fun s : ℝ => Real.cosh (y / 2) + Real.cosh ((s + x) / 2))
      (Real.sinh ((t + x) / 2) * (1 / 2)) t := by
    have h0 : HasDerivAt (fun s : ℝ => (s + x) / 2) (1 / 2) t := by
      simpa using ((hasDerivAt_id t).add_const x).div_const 2
    simpa using ((Real.hasDerivAt_cosh ((t + x) / 2)).comp t h0).const_add (Real.cosh (y / 2))
  have d2 : HasDerivAt (fun s : ℝ => Real.cosh (y / 2) + Real.cosh ((s - x) / 2))
      (Real.sinh ((t - x) / 2) * (1 / 2)) t := by
    have h0 : HasDerivAt (fun s : ℝ => (s - x) / 2) (1 / 2) t := by
      simpa using ((hasDerivAt_id t).sub_const x).div_const 2
    simpa using ((Real.hasDerivAt_cosh ((t - x) / 2)).comp t h0).const_add (Real.cosh (y / 2))
  have hR := (hasDerivAt_id t).sub ((d1.log (ne_of_gt (hc _))).sub (d2.log (ne_of_gt (hc _))))
  convert hR using 1
  have ha : (0 : ℝ) < Real.exp (t / 2) := Real.exp_pos _
  have hb : (0 : ℝ) < Real.exp (x / 2) := Real.exp_pos _
  have hd : (0 : ℝ) < Real.exp (y / 2) := Real.exp_pos _
  simp only [mirzH, Real.cosh_eq, Real.sinh_eq]
  rw [show (x + (t + y)) / 2 = x / 2 + t / 2 + y / 2 by ring,
     show (x - (t + y)) / 2 = x / 2 - t / 2 - y / 2 by ring,
     show (x + (t - y)) / 2 = x / 2 + t / 2 - y / 2 by ring,
     show (x - (t - y)) / 2 = x / 2 - t / 2 + y / 2 by ring,
     show ((t + x) / 2 : ℝ) = t / 2 + x / 2 by ring,
     show ((t - x) / 2 : ℝ) = t / 2 - x / 2 by ring]
  simp only [Real.exp_add, Real.exp_sub, Real.exp_neg, neg_add_rev, neg_sub]
  have k1 : (0 : ℝ) < (rexp (y / 2) + (rexp (y / 2))⁻¹) / 2 +
      (rexp (t / 2) * rexp (x / 2) + (rexp (x / 2))⁻¹ * (rexp (t / 2))⁻¹) / 2 := by positivity
  have k2 : (0 : ℝ) < (rexp (y / 2) + (rexp (y / 2))⁻¹) / 2 +
      (rexp (t / 2) / rexp (x / 2) + rexp (x / 2) / rexp (t / 2)) / 2 := by positivity
  field_simp
  ring

/-! ## Boundary length vectors

A surface with `n` labelled boundary components carries a length vector, which we model as a
function `L : ℕ → ℝ`; only the values `L 0, …, L (n-1)` are relevant. -/

/-- The length vector of a surface whose first boundary has length `x` and whose remaining
boundaries are the boundaries of the ambient surface listed by `l`. -/
