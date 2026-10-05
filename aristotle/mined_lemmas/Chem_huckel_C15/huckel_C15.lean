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

theorem huckel_C15 (μ : ℂ) :
    (∃ v : Fin 15 → ℂ, v ≠ 0 ∧
        ((cycleGraph 15).adjMatrix ℂ).mulVec v = μ • v) ↔
      ∃ k : Fin 15, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 15) := by
  constructor
  · rintro ⟨v, hv, hA⟩
    have heig : ∀ i : Fin 15, v (i - 1) + v (i + 1) = μ * v i := by
      intro i
      have h := congrFun hA i
      rw [adj_mulVec] at h
      simpa using h
    have hex : ∃ k : Fin 15, (∑ i : Fin 15, chi (-((k : ℕ) : ℤ)) i * v i) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hv
      funext j
      have hinv := dft_inversion v j
      rw [Finset.sum_congr rfl (fun k _ => by rw [hcon k, mul_zero])] at hinv
      simp only [Finset.sum_const, smul_zero] at hinv
      have : (15 : ℂ) * v j = 0 := hinv.symm
      simpa using this
    obtain ⟨k, hk⟩ := hex
    refine ⟨k, ?_⟩
    have key := dft_eigen v μ heig k
    have hμ : μ = W ((k : ℕ) : ℤ) + W (-((k : ℕ) : ℤ)) := mul_right_cancel₀ hk key
    rw [hμ, W_val_add_neg]
  · rintro ⟨k, rfl⟩
    refine ⟨fun j => chi ((k : ℕ) : ℤ) j, ?_, ?_⟩
    · intro hzero
      have h0 : chi ((k : ℕ) : ℤ) 0 = 0 := congrFun hzero 0
      rw [chi_zero] at h0
      exact one_ne_zero h0
    · funext j
      rw [adj_mulVec]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← W_val_add_neg k]
      have hj : j = (j - 1) + 1 := by simp
      set i : Fin 15 := j - 1 with hi
      rw [hj]
      simp only [chi_step]
      have h1 : W ((k : ℕ) : ℤ) * W (-((k : ℕ) : ℤ)) = 1 := W_mul_neg _
      linear_combination (-(chi ((k : ℕ) : ℤ) i)) * h1

end Chem

