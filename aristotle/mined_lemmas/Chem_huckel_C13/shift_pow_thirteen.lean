/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Finset

namespace Chem

/-! ### The cyclic shift operator -/

/-- The cyclic shift endomorphism of `Fin 13 → ℂ`, `f ↦ (i ↦ f (i + 1))`. -/

lemma shift_pow_thirteen : shift ^ 13 = 1 := by
  refine LinearMap.ext fun f => funext fun i => ?_
  rw [shift_pow_apply, show (13 : ℕ) • (1 : Fin 13) = 0 from by decide, add_zero]
  rfl

/-! ### The adjacency operator of the cycle graph -/

/-- The adjacency operator of the cycle graph `C₁₃`, as an endomorphism of `Fin 13 → ℂ`. -/
