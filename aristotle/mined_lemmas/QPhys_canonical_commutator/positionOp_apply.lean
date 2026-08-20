/-
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not allow a
-- module docstring to precede `import`; the exact docstring is repeated below.)

import Mathlib

/-!
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace QPhys

open SchwartzMap

/-- The function `x ↦ (x : ℂ)` has temperate growth (it is a continuous linear map). -/

theorem positionOp_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : positionOp f x = (x : ℂ) * f x := by
  simp [positionOp, SchwartzMap.smulLeftCLM_apply_apply ofReal_hasTemperateGrowth,
    smul_eq_mul]

@[simp]
