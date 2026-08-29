/-
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command; the module docstring below
-- repeats the header verbatim.)
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
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Matrix Polynomial

/-- The cyclic shift matrix on `ZMod n`: `shiftM n a i j = 1` exactly when `i - j = a`. -/

lemma shiftM_neg_one_eigen (hn : 3 ≤ n) (z : ℂ) (hz : z ^ n = 1) :
    z ∈ spectrum ℂ (shiftM n (-1)) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  set v : ZMod n → ℂ := fun j => z ^ j.val with hv
  have hmod : ∀ m : ℕ, z ^ (m % n) = z ^ m := by
    intro m
    conv_rhs => rw [← Nat.div_add_mod m n]
    rw [pow_add, pow_mul, hz, one_pow, one_mul]
  have hvne : v ≠ 0 := by
    intro hc
    have h0 : v 0 = 0 := by rw [hc]; rfl
    simp [hv, ZMod.val_zero] at h0
  refine mem_spectrum_of_mulVec_eq _ z v hvne ?_
  funext i
  rw [shiftM_mulVec, sub_neg_eq_add]
  have hval : (i + 1 : ZMod n).val = (i.val + 1) % n := by
    rw [ZMod.val_add, ZMod.val_one]
  simp only [hv, Pi.smul_apply, smul_eq_mul]
  rw [hval, hmod, pow_succ]
  ring

end Eigen

/-- For `z = exp (2πi/n)`, the value `2 - z^k - (z^k)^(n-1)` equals `2 - 2 cos (2πk/n)`. -/
