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

theorem cycle_laplacian_spectrum (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    spectrum ℂ (cycleLaplacian n) =
      (fun k : ℕ => ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)) ''
        (Finset.range n : Finset ℕ) := by
  classical
  set S : Matrix (ZMod n) (ZMod n) ℂ := shiftM n (-1) with hS
  set p : ℂ[X] := C 2 - X - X ^ (n - 1) with hp
  have hne : (spectrum ℂ S).Nonempty :=
    spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ S
  have hLp : cycleLaplacian n = (Polynomial.aeval S) p := (cycleLaplacian_eq_aeval hn).symm
  rw [hLp, spectrum.map_polynomial_aeval_of_nonempty S p hne]
  -- the spectrum of the shift is contained in the set of `n`-th roots of unity
  have hroot : ∀ z ∈ spectrum ℂ S, z ^ n = 1 := by
    intro z hz
    have hsub := spectrum.subset_polynomial_aeval S (X ^ n : ℂ[X])
    have hmem : z ^ n ∈ spectrum ℂ ((Polynomial.aeval S) (X ^ n : ℂ[X])) :=
      hsub ⟨z, hz, by simp⟩
    have hSn : (Polynomial.aeval S) (X ^ n : ℂ[X]) = 1 := by
      rw [map_pow, aeval_X, hS, shiftM_neg_one_pow, ZMod.natCast_self, neg_zero, shiftM_zero]
    rw [hSn, spectrum.one_eq] at hmem
    simpa using hmem
  set w : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hw
  have hprim : IsPrimitiveRoot w n := Complex.isPrimitiveRoot_exp n (by omega)
  have heval : ∀ z : ℂ, eval z p = 2 - z - z ^ (n - 1) := by
    intro z; simp [hp]
  ext mu
  simp only [Set.mem_image, Finset.coe_range, Set.mem_Iio]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨k, hk, rfl⟩ := hprim.eq_pow_of_pow_eq_one (hroot z hz)
    exact ⟨k, hk, by rw [heval]; exact eval_at_root n (by omega) k⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨w ^ k, ?_, ?_⟩
    · refine shiftM_neg_one_eigen hn _ ?_
      rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    · rw [heval]
      exact eval_at_root n (by omega) k

end Frontier.Spectral

