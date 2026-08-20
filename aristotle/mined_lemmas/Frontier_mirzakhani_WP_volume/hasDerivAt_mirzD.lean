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

theorem hasDerivAt_mirzD (x y t : ℝ) :
    HasDerivAt (fun s => mirzD s x y) (mirzH (x + y) t) t := by
  have hA : (0 : ℝ) < Real.exp ((x + y) / 2) := Real.exp_pos _
  have h1 : (0 : ℝ) < Real.exp (t / 2) + Real.exp ((x + y) / 2) := by positivity
  have h2 : (0 : ℝ) < Real.exp (-t / 2) + Real.exp ((x + y) / 2) := by positivity
  have key : ∀ s : ℝ, mirzD s x y =
      2 * (Real.log (Real.exp (s / 2) + Real.exp ((x + y) / 2))
            - Real.log (Real.exp (-s / 2) + Real.exp ((x + y) / 2))) := by
    intro s
    have p1 : (0 : ℝ) < Real.exp (s / 2) + Real.exp ((x + y) / 2) := by positivity
    have p2 : (0 : ℝ) < Real.exp (-s / 2) + Real.exp ((x + y) / 2) := by positivity
    rw [mirzD, Real.log_div (ne_of_gt p1) (ne_of_gt p2)]
  simp only [key]
  have d1 : HasDerivAt (fun s : ℝ => Real.exp (s / 2) + Real.exp ((x + y) / 2))
      (Real.exp (t / 2) * (1 / 2)) t := by
    have h := ((hasDerivAt_id t).div_const 2).exp
    simpa using h.add_const (Real.exp ((x + y) / 2))
  have d2 : HasDerivAt (fun s : ℝ => Real.exp (-s / 2) + Real.exp ((x + y) / 2))
      (Real.exp (-t / 2) * (-(1 / 2))) t := by
    have h0 : HasDerivAt (fun s : ℝ => -s / 2) (-(1 / 2)) t := by
      have h := (hasDerivAt_neg t).div_const 2
      norm_num at h ⊢
      exact h
    simpa using (h0.exp).add_const (Real.exp ((x + y) / 2))
  have hD := ((d1.log (ne_of_gt h1)).sub (d2.log (ne_of_gt h2))).const_mul (2 : ℝ)
  convert hD using 1
  rw [mirzH, show ((x + y) + t) / 2 = (x + y) / 2 + t / 2 by ring,
    show ((x + y) - t) / 2 = (x + y) / 2 - t / 2 by ring, Real.exp_add, Real.exp_sub,
    show (-t / 2 : ℝ) = -(t / 2) by ring, Real.exp_neg]
  have ha : (0 : ℝ) < Real.exp (t / 2) := Real.exp_pos _
  field_simp
  ring

/-- `∂_t R(t, y, x) = ½ (H(x, t + y) + H(x, t - y))`. -/
