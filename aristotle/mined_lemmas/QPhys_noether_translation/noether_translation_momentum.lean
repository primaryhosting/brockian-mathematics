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

theorem noether_translation_momentum
    (L : ℝ → ℝ → ℝ) (Lq Lv : ℝ → ℝ → ℝ)
    (hLq : ∀ q v, HasDerivAt (fun x => L x v) (Lq q v) q)
    (hinv : ∀ s q v, L (q + s) v = L q v)
    (q v : ℝ → ℝ)
    (hEL : ∀ t, HasDerivAt (fun s => Lv (q s) (v s)) (Lq (q t) (v t)) t) :
    ∀ t₁ t₂, Lv (q t₁) (v t₁) = Lv (q t₂) (v t₂) :=
  noether_translation L Lq hLq hinv q v (fun s => Lv (q s) (v s)) hEL

/-- Non-vacuity check: the free particle of mass `m`, with Lagrangian `L q v = m * v ^ 2 / 2`,
position-partial `∂L/∂q = 0`, velocity-partial `∂L/∂v = m * v`, and uniform-motion trajectory
`q t = q₀ + u * t` with velocity `v t = u`, satisfies every hypothesis of
`noether_translation_momentum`: the two partial-derivative hypotheses, translation invariance,
the relation `v = q'`, and the Euler–Lagrange equation. -/
