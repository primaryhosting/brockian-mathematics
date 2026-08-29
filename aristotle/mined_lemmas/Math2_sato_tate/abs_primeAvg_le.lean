import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
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

namespace Math2

open Filter Topology Set Polynomial

/-- The Sato–Tate density `(2/π) sin²θ` on the interval `[0, π]`. -/

lemma abs_primeAvg_le {θ : ℕ → ℝ} {f : ℝ → ℝ} {C : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hθ : ∀ p, θ p ∈ Icc (0:ℝ) π) (h : ∀ t ∈ Icc (0:ℝ) π, |f t| ≤ C) :
    |primeAvg θ f N| ≤ C := by
  have hcard : 0 < ((primesUpTo N).card : ℝ) := by
    exact_mod_cast card_primesUpTo_pos hN
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (h 0 ⟨le_refl 0, Real.pi_pos.le⟩)
  unfold primeAvg
  rw [abs_div, abs_of_nonneg hcard.le, div_le_iff₀ hcard]
  calc |∑ p ∈ primesUpTo N, f (θ p)| ≤ ∑ p ∈ primesUpTo N, |f (θ p)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ primesUpTo N, C := Finset.sum_le_sum fun p _ => h _ (hθ p)
    _ = C * (primesUpTo N).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-! ### Density of the span of the Weyl test functions -/

