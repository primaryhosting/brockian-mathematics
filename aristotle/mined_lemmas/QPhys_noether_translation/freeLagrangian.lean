/-
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

/-- **Key lemma.** If a Lagrangian `L : ℝ → ℝ → ℝ` (position, velocity) is invariant under
translations of the position variable, then its partial derivative with respect to position
vanishes identically. -/

noncomputable def freeLagrangian (m : ℝ) : ℝ → ℝ → ℝ := fun _ u => m * u ^ 2 / 2

/-- For the free-particle Lagrangian `L x u = m * u ^ 2 / 2`, the canonical momentum is `m * u`. -/
