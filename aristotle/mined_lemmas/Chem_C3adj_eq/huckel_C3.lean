/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Polynomial

/-- The Hückel (adjacency) matrix of the cycle graph `C₃`: the π-system connectivity
matrix of a three-membered carbon ring, in units where the Coulomb integral is `α = 0`
and the resonance integral is `β = 1`. -/

theorem huckel_C3 :
    C3adj.charpoly
        = ∏ k ∈ Finset.range 3, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 3))) ∧
      ∀ μ : ℝ, (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ C3adj.mulVec v = μ • v) ↔
        ∃ k ∈ Finset.range 3, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 3) := by
  refine ⟨by rw [C3adj_charpoly, C3_spectral_prod], fun μ => ?_⟩
  rw [eigen_iff_det, ← Matrix.eval_charpoly, C3adj_charpoly]
  have hfac : (X ^ 3 - 3 * X - 2 : ℝ[X]).eval μ = (μ - 2) * (μ + 1) ^ 2 := by
    simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_ofNat]
    ring
  rw [hfac]
  simp only [Finset.mem_range]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact ⟨0, by norm_num, by rw [huckel_val_zero]; linarith⟩
    · have h3 : μ + 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
      exact ⟨1, by norm_num, by rw [huckel_val_one]; linarith⟩
  · rintro ⟨k, hk3, hk⟩
    interval_cases k
    · rw [huckel_val_zero] at hk; rw [hk]; ring
    · rw [huckel_val_one] at hk; rw [hk]; ring
    · rw [huckel_val_two] at hk; rw [hk]; ring

end Chem

