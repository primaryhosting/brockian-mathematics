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

variable {n : ℕ} [NeZero n]

/-- The cyclic shift matrix on `ZMod n`: `shift n i j = 1` iff `i - j = 1`. -/

lemma spectrum_shift (hn : 1 < n) : spectrum ℂ (shift n) = {z : ℂ | z ^ n = 1} := by
  have hne : Fact (1 < n) := ⟨hn⟩
  ext μ
  constructor
  · intro hμ
    have h1 : μ ^ n ∈ spectrum ℂ (shift n ^ n) := spectrum.pow_mem_pow _ n hμ
    rw [shift_pow_card, spectrum.one_eq] at h1
    simpa using h1
  · intro (hz : μ ^ n = 1)
    set v : ZMod n → ℂ := fun i => μ ^ (-i).val with hv
    have hvne : v ≠ 0 := by
      intro h
      have h0 := congrFun h 0
      simp [hv] at h0
    have hmul : shift n *ᵥ v = μ • v := by
      rw [shift_mulVec]
      funext i
      have key : (-(i - 1)).val = ((-i).val + 1) % n := by
        have hi : -(i - 1) = -i + 1 := by ring
        rw [hi, ZMod.val_add, ZMod.val_one]
      show v (i - 1) = μ * v i
      simp only [hv]
      rw [key, pow_mod_eq hz, pow_succ]
      ring
    rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hvne⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hmul]

omit [NeZero n] in
