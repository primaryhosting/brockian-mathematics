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

/-- Partial derivative `∂L/∂q` of a Lagrangian `L q v t` with respect to the position `q`. -/

def TranslationInvariant (L : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ s q v t, L (q + s) v t = L q v t

/-- The canonical momentum `p t = ∂L/∂v (q t, q̇ t, t)` along a path `q`. -/
