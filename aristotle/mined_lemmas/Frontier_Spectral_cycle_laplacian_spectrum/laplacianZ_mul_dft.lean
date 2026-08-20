/-
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Matrix Finset

/-- The graph Laplacian of the cycle graph `C n`, as the `n × n` circulant matrix with `2` on the
diagonal and `-1` on the two cyclic off-diagonals. -/

lemma laplacianZ_mul_dft (hn : 3 ≤ n) :
    cycleLaplacianZ n * dftMatrix n = dftMatrix n * Matrix.diagonal (cycleEig n) := by
  have h1 : (1 : ZMod n) ≠ 0 := by
    intro h
    have hd : (n : ℕ) ∣ 1 := (ZMod.natCast_eq_zero_iff 1 n).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd one_pos hd
    omega
  have h2 : (2 : ZMod n) ≠ 0 := by
    intro h
    have hd : (n : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd two_pos hd
    omega
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hA : ¬ ((i : ZMod n) = i - 1) := fun h => h1 (by linear_combination h)
  have hB : ¬ ((i : ZMod n) = i + 1) := fun h => h1 (by linear_combination -h)
  have hD : ¬ ((i : ZMod n) - 1 = i + 1) := fun h => h2 (by linear_combination -h)
  have hA2 : ¬ ((i : ZMod n) - 1 = i) := fun h => hA h.symm
  have hB2 : ¬ ((i : ZMod n) + 1 = i) := fun h => hB h.symm
  have hD2 : ¬ ((i : ZMod n) + 1 = i - 1) := fun h => hD h.symm
  have hs1 : (i : ZMod n) - (i - 1) = 1 := by ring
  have hs2 : (i : ZMod n) - (i + 1) = -1 := by ring
  have hne : (-1 : ZMod n) ≠ 1 := fun h => h2 (by linear_combination -h)
  have hrow : ∀ j : ZMod n, cycleLaplacianZ n i j * dftMatrix n j k
      = (if j = i then 2 * ZMod.stdAddChar (i * k) else 0)
        + (if j = i - 1 then -ZMod.stdAddChar ((i - 1) * k) else 0)
        + (if j = i + 1 then -ZMod.stdAddChar ((i + 1) * k) else 0) := by
    intro j
    simp only [cycleLaplacianZ, dftMatrix, Matrix.of_apply]
    by_cases hji : j = i
    · simp [hji, hA, hB]
    · by_cases hj1 : j = i - 1
      · simp [hj1, hA, hA2, hD, hs1]
      · by_cases hj2 : j = i + 1
        · simp [hj2, hB, hB2, hD2, hs2, hne]
        · have hc1 : ¬ ((i : ZMod n) - j = 1) := fun h => hj1 (by linear_combination -h)
          have hc2 : ¬ ((i : ZMod n) - j = -1) := fun h => hj2 (by linear_combination -h)
          simp [hji, hj1, hj2, hc1, hc2, Ne.symm hji]
  simp only [hrow, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have e1 : ZMod.stdAddChar ((i - 1) * k)
      = ZMod.stdAddChar (i * k) * ZMod.stdAddChar (-k) := by
    rw [← AddChar.map_add_eq_mul]; ring_nf
  have e2 : ZMod.stdAddChar ((i + 1) * k)
      = ZMod.stdAddChar (i * k) * ZMod.stdAddChar k := by
    rw [← AddChar.map_add_eq_mul]; ring_nf
  have e3 := stdAddChar_add_neg (n := n) k
  simp only [dftMatrix, Matrix.of_apply, cycleEig]
  rw [e1, e2]
  linear_combination -(ZMod.stdAddChar (i * k) : ℂ) * e3

