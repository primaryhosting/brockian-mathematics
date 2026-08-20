import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₈`; this is the Hückel matrix of
cyclooctatetraene in the units where the Coulomb integral is `0` and the resonance
integral is `1`. -/

lemma pow_mulVec_eigen {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {v : Fin n → ℂ} {mu : ℂ}
    (h : M *ᵥ v = mu • v) (m : ℕ) : (M ^ m) *ᵥ v = mu ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]

/-- For each `k`, the vector `i ↦ exp(2πik/8)ⁱ` is an eigenvector of `C8Adj`
with eigenvalue `2 cos (2πk/8)`. -/
