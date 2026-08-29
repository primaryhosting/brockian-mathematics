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

lemma C6_eigenvalue_root {mu : ℝ} {v : Fin 6 → ℝ} (hv : v ≠ 0) (h : C6adj *ᵥ v = mu • v) :
    mu ^ 4 - 5 * mu ^ 2 + 4 = 0 := by
  have h2 : C6sq *ᵥ v = mu ^ 2 • v := by
    rw [← C6adj_mul_self, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, h, smul_smul]
    ring_nf
  have h4 : (C6sq * C6sq) *ᵥ v = mu ^ 4 • v := by
    rw [← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, h2, smul_smul]
    ring_nf
  rw [C6sq_mul_self] at h4
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, h2, Matrix.one_mulVec,
    smul_smul] at h4
  have hz : (mu ^ 4 - 5 * mu ^ 2 + 4) • v = 0 := by
    linear_combination (norm := module) -h4
  rcases smul_eq_zero.mp hz with h' | h'
  · exact h'
  · exact absurd h' hv

/-- The eigenvalue set of the adjacency matrix of `C₆` is contained in `{2, 1, -1, -2}`. -/
