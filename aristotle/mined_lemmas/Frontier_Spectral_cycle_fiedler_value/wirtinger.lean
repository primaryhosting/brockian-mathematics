import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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

open Finset Matrix

namespace CycleAux

variable (m : ℕ)

/-- The primitive `(m+3)`-rd root of unity. -/

lemma wirtinger (x : Fin (m + 3) → ℝ) (hx : ∑ i : Fin (m + 3), x i = 0) :
    fied m * ∑ i : Fin (m + 3), (x i) ^ 2 ≤ ∑ i : Fin (m + 3), (x i - x (i + 1)) ^ 2 := by
  set y : Fin (m + 3) → ℂ := fun j => (x j : ℂ) with hy
  have hy0 : dft m y 0 = 0 := by
    rw [dft]
    have h2 : ∀ j : Fin (m + 3), y j * ee m (j * 0) = y j := by
      intro j; rw [mul_zero, ee_zero, mul_one]
    rw [Finset.sum_congr rfl (fun j _ => h2 j), hy]
    rw [← Complex.ofReal_sum, hx, Complex.ofReal_zero]
  have hterm : ∀ k : Fin (m + 3),
      fied m * Complex.normSq (dft m y k)
        ≤ Complex.normSq (dft m (fun j => y j - y (j + 1)) k) := by
    intro k
    rw [dft_shift, Complex.normSq_mul]
    by_cases hk : k = 0
    · subst hk; rw [hy0]; simp
    · have h1 : fied m ≤ Complex.normSq (1 - ee m (-k)) :=
        fied_le_normSq m (-k) (neg_ne_zero.2 hk)
      nlinarith [Complex.normSq_nonneg (dft m y k), Complex.normSq_nonneg (1 - ee m (-k))]
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hterm k)
  rw [← Finset.mul_sum, parseval, parseval] at hsum
  have hN : (0:ℝ) < ((m + 3 : ℕ) : ℝ) := by positivity
  have e1 : ∀ j : Fin (m + 3), Complex.normSq (y j) = (x j) ^ 2 := by
    intro j; rw [hy]; simp [Complex.normSq_ofReal]; ring
  have e2 : ∀ j : Fin (m + 3), Complex.normSq (y j - y (j + 1)) = (x j - x (j + 1)) ^ 2 := by
    intro j
    have h3 : y j - y (j + 1) = ((x j - x (j + 1) : ℝ) : ℂ) := by rw [hy]; push_cast; ring
    rw [h3, Complex.normSq_ofReal]; ring
  rw [Finset.sum_congr rfl (fun j _ => e1 j), Finset.sum_congr rfl (fun j _ => e2 j)] at hsum
  nlinarith [hsum]

