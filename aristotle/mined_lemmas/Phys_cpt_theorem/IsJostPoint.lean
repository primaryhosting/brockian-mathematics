/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Matrix

namespace Phys

/-! ## Complexified Minkowski space and the complex Lorentz group -/

/-- Real Minkowski space `ℝ^{1,3}`. -/
abbrev Spacetime := Fin 4 → ℝ

/-- Complexified Minkowski space `ℂ^4`, the domain of the analytically continued
Wightman functions. -/
abbrev CSpace := Fin 4 → ℂ

/-- The Minkowski bilinear form on real Minkowski space (signature `+ - - -`). -/

def IsJostPoint {m : ℕ} (x : Fin (m + 1) → Spacetime) : Prop :=
  ∀ lam : Fin m → ℝ, (∀ k, 0 ≤ lam k) → (∃ k, 0 < lam k) →
    mform (∑ k, lam k • (x k.castSucc - x k.succ)) (∑ k, lam k • (x k.castSucc - x k.succ)) < 0

/-- Jost points exist: two points at spacelike separation form one. -/
