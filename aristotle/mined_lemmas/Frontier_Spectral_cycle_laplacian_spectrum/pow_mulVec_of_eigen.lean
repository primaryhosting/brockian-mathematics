import Mathlib
/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
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

namespace Frontier.Spectral

open Polynomial Matrix Complex

variable (n : ℕ) [NeZero n]

/-- The cyclic shift matrix on `ZMod n`: `(S *ᵥ v) i = v (i + 1)`. -/

lemma pow_mulVec_of_eigen {M : Matrix (ZMod n) (ZMod n) ℂ} {v : ZMod n → ℂ} {μ : ℂ}
    (h : M *ᵥ v = μ • v) (m : ℕ) : M ^ m *ᵥ v = μ ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, pow_succ,
        mul_comm]

end Spectrum

section RootsOfUnity

omit [NeZero n] in
