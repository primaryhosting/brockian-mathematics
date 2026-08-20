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

lemma exists_zeta_eq {z : ℂ} (hz : z ^ n = 1) : ∃ k < n, z = zeta n k := by
  obtain ⟨k, hk, hkz⟩ := (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).eq_pow_of_pow_eq_one hz
  refine ⟨k, hk, ?_⟩
  rw [← hkz, zeta, ← Complex.exp_nat_mul]
  congr 1
  ring

end RootsOfUnity

section Laplacian

omit [NeZero n] in
