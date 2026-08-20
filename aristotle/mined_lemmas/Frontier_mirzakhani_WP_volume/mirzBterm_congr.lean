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

theorem mirzBterm_congr (V W : ℕ → ℕ → (ℕ → ℝ) → ℝ) (g n : ℕ) (L : ℕ → ℝ)
    (hn : 1 ≤ n) (hs : 4 ≤ 2 * g + n)
    (h : ∀ g' n' L', 3 * g' + n' < 3 * g + n → 1 ≤ n' → 3 ≤ 2 * g' + n' → 0 < L' 0 →
      V g' n' L' = W g' n' L') :
    mirzBterm V g n L = mirzBterm W g n L := by
  rw [mirzBterm, mirzBterm]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp only [Finset.mem_Ico] at hj
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [h g (n - 1) _ (by omega) (by omega) (by omega) (by simpa [mirzCons] using hx)]

/-! ## The main reduction theorem -/

/-- **Mirzakhani's recursion determines all Weil–Petersson volumes.**

If two families `V` and `W` of volume functions both satisfy Mirzakhani's recursion and both
take the base values `V_{0,3} = 1` and `V_{1,1}(L) = (L² + 4π²)/48`, then they agree on every
stable pair `(g, n)` (`n ≥ 1`, `2g - 2 + n > 0`) and every boundary length vector whose first
entry is positive.

Thus the recursion, whose geometric content is Mirzakhani's integration formula over moduli
space, is a complete recursive scheme: it reduces every Weil–Petersson volume to the two base
cases. -/
