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

open Complex Matrix

/-- The graph Laplacian of the cycle graph `C n`, as the `n × n` circulant matrix with
diagonal `2` and `-1` on the two cyclic off-diagonals (indices are taken in `ZMod n`). -/

lemma sum_fourierComp (v : ZMod n → ℂ) (j : ZMod n) :
    ∑ k ∈ Finset.range n, fourierComp (Complex.exp (2 * Real.pi * I / n) ^ k) v j
      = (n : ℂ) * v j := by
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * I / n)) n :=
    Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  set ω := Complex.exp (2 * Real.pi * I / n) with hωdef
  have hωn : ω ^ n = 1 := hprim.pow_eq_one
  simp only [fourierComp]
  rw [Finset.sum_comm]
  have key : ∀ m : ZMod n, (∑ k ∈ Finset.range n, ((ω ^ k) ^ m.val)⁻¹ * v (j + m))
      = if m = 0 then (n : ℂ) * v j else 0 := by
    intro m
    rw [← Finset.sum_mul]
    have hrw : ∀ k : ℕ, ((ω ^ k) ^ m.val)⁻¹ = ((ω ^ m.val)⁻¹) ^ k := by
      intro k; rw [← pow_mul, mul_comm k m.val, pow_mul, inv_pow]
    simp only [hrw]
    by_cases hm : m = 0
    · subst hm; simp
    · have hmv : m.val ≠ 0 := by simpa [ZMod.val_eq_zero] using hm
      have hmlt : m.val < n := ZMod.val_lt m
      have hne1 : ω ^ m.val ≠ 1 := hprim.pow_ne_one_of_pos_of_lt hmv hmlt
      have hinv1 : (ω ^ m.val)⁻¹ ≠ 1 := fun h => hne1 (inv_eq_one.mp h)
      rw [geom_sum_eq hinv1]
      have hp : ((ω ^ m.val)⁻¹) ^ n = 1 := by
        rw [inv_pow, ← pow_mul, mul_comm m.val n, pow_mul, hωn, one_pow, inv_one]
      rw [hp]
      simp [hm]
  rw [Finset.sum_congr rfl fun m _ => key m]
  simp

end

