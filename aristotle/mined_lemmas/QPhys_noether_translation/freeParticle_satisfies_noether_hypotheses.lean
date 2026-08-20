/-
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- If a Lagrangian `L q v` is invariant under translations `q ↦ q + s` of the position
variable, then its partial derivative with respect to position vanishes. -/

theorem freeParticle_satisfies_noether_hypotheses (m q₀ u : ℝ) :
    (∀ x y : ℝ, HasDerivAt (fun _ : ℝ => m * y ^ 2 / 2) ((fun _ _ : ℝ => (0 : ℝ)) x y) x) ∧
      (∀ x y : ℝ, HasDerivAt (fun w : ℝ => m * w ^ 2 / 2) ((fun _ w : ℝ => m * w) x y) y) ∧
      (∀ _s _x y : ℝ, m * y ^ 2 / 2 = m * y ^ 2 / 2) ∧
      (∀ t : ℝ, HasDerivAt (fun t : ℝ => q₀ + u * t) u t) ∧
      (∀ t : ℝ, HasDerivAt (fun _ : ℝ => m * u) ((fun _ _ : ℝ => (0 : ℝ)) (q₀ + u * t) u) t) := by
  refine ⟨fun x y => by simpa using hasDerivAt_const x (m * y ^ 2 / 2), fun x y => ?_,
    fun _s _x _y => rfl, fun t => by simpa using ((hasDerivAt_id t).const_mul u).const_add q₀,
    fun t => by simpa using hasDerivAt_const t (m * u)⟩
  have h : HasDerivAt (fun w : ℝ => w ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y)
  have := (h.const_mul m).div_const 2
  convert this using 1
  ring

/-- Conservation of momentum for the free particle, obtained from `noether_translation_momentum`:
along uniform motion `q t = q₀ + u * t`, the momentum `m * u` is the same at all times. -/
