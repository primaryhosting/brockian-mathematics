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

theorem mirzVaux_indep : ∀ c g n : ℕ, 3 * g + n = c → 1 ≤ n → 3 ≤ 2 * g + n →
    ∀ m m' : ℕ, c ≤ m → c ≤ m' → ∀ L : ℕ → ℝ, mirzVaux m g n L = mirzVaux m' g n L := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c IH =>
    intro g n hc hn hstab m m' hm hm' L
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ k', m' = k' + 1 := ⟨m' - 1, by omega⟩
    simp only [mirzVaux]
    by_cases hb1 : g = 0 ∧ n = 3
    · simp only [if_pos hb1]
    by_cases hb2 : g = 1 ∧ n = 1
    · simp only [if_neg hb1, if_pos hb2]
    simp only [if_neg hb1, if_neg hb2]
    by_cases hL : L 0 = 0
    · simp only [if_pos hL]
    simp only [if_neg hL]
    have h4 : 4 ≤ 2 * g + n := by omega
    have hIH : ∀ g' n' L', 3 * g' + n' < 3 * g + n → 1 ≤ n' → 3 ≤ 2 * g' + n' → 0 < L' 0 →
        mirzVaux k g' n' L' = mirzVaux k' g' n' L' := by
      intro g' n' L' hlt hn' hstab' _
      exact IH (3 * g' + n') (by omega) g' n' rfl hn' hstab' k k' (by omega) (by omega) L'
    rw [mirzAcon_congr _ _ g n L hn h4 hIH, mirzAdcon_congr _ _ g n L hn hIH,
      mirzBterm_congr _ _ g n L hn h4 hIH]

/-- A concrete family of functions satisfying Mirzakhani's recursion and its base values. -/
