/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
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

namespace Chem

open Finset SimpleGraph

/-- A primitive 15-th root of unity. -/

lemma dft_eigen (v : Fin 15 → ℂ) (μ : ℂ) (h : ∀ i : Fin 15, v (i - 1) + v (i + 1) = μ * v i)
    (k : Fin 15) :
    μ * (∑ i : Fin 15, chi (-((k : ℕ) : ℤ)) i * v i)
      = (W ((k : ℕ) : ℤ) + W (-((k : ℕ) : ℤ))) * (∑ i : Fin 15, chi (-((k : ℕ) : ℤ)) i * v i) := by
  set m : ℤ := -((k : ℕ) : ℤ) with hm
  set c : ℂ := ∑ i : Fin 15, chi m i * v i with hcdef
  have hS2 : ∑ i : Fin 15, chi m i * v (i - 1) = W m * c := by
    have := (sum_shift (fun i => chi m i * v (i - 1))).symm
    rw [this]
    rw [hcdef, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [chi_step]
    simp only [add_sub_cancel_right]
    ring
  have hS1 : ∑ i : Fin 15, chi m i * v (i + 1) = W (-m) * c := by
    have hg := sum_shift (fun i => (W (-m) * chi m i) * v i)
    have hlhs : ∀ i : Fin 15, (W (-m) * chi m (i + 1)) * v (i + 1) = chi m i * v (i + 1) := by
      intro i
      rw [chi_step]
      have : W (-m) * (chi m i * W m) = chi m i * (W m * W (-m)) := by ring
      rw [this, W_mul_neg, mul_one]
    calc ∑ i : Fin 15, chi m i * v (i + 1)
        = ∑ i : Fin 15, (W (-m) * chi m (i + 1)) * v (i + 1) :=
          Finset.sum_congr rfl (fun i _ => (hlhs i).symm)
      _ = ∑ i : Fin 15, (W (-m) * chi m i) * v i := hg
      _ = W (-m) * c := by
            rw [hcdef, Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _ => by ring)
  have : μ * c = ∑ i : Fin 15, chi m i * (v (i - 1) + v (i + 1)) := by
    rw [hcdef, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h i]; ring
  rw [this]
  have hsplit : ∑ i : Fin 15, chi m i * (v (i - 1) + v (i + 1))
      = (∑ i : Fin 15, chi m i * v (i - 1)) + ∑ i : Fin 15, chi m i * v (i + 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsplit, hS1, hS2, hm]
  simp only [neg_neg]
  ring

