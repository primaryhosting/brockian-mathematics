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

lemma C6_eigen_two : C6adj *ᵥ ![1, 1, 1, 1, 1, 1] = (2 : ℝ) • ![1, 1, 1, 1, 1, 1] := by
  rw [C6adj_eq]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> norm_num

