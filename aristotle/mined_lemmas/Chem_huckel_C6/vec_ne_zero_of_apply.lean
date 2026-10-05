import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix

/-- The adjacency matrix (over `ℝ`) of the cycle graph `C₆`, i.e. the Hückel matrix of
benzene in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`. -/

lemma vec_ne_zero_of_apply {v : Fin 6 → ℝ} {i : Fin 6} (h : v i ≠ 0) : v ≠ 0 := by
  intro hv
  exact h (by simp [hv])

/-- The values `2 cos (2πk/6)` for `k = 0, …, 5` are exactly `{2, 1, -1, -2}`. -/
