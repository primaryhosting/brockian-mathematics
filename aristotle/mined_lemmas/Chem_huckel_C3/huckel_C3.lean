import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Polynomial

/-- Adjacency matrix of the cycle graph `C₃` (the Hückel matrix of cyclopropenyl,
in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`). -/

theorem huckel_C3 :
    C3adj.charpoly = ∏ k : Fin 3, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 3))) ∧
      (∀ μ : ℝ, (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ C3adj.mulVec v = μ • v) ↔
        ∃ k : Fin 3, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 3)) ∧
      ∀ k : Fin 3, blochMO k ≠ 0 ∧
        C3adjC.mulVec (blochMO k)
          = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 3) : ℝ) : ℂ) • blochMO k := by
  refine ⟨by rw [C3_charpoly, C3_prod_factors], fun μ => ?_,
    fun k => ⟨blochMO_ne_zero k, C3adjC_mulVec_blochMO k⟩⟩
  rw [C3_eigenvalue_iff]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num [C3_cos_zero]⟩
    · exact ⟨1, by norm_num [C3_cos_one]⟩
  · rintro ⟨k, rfl⟩
    fin_cases k
    · left; norm_num [C3_cos_zero]
    · right; norm_num [C3_cos_one]
    · right; norm_num [C3_cos_two]

end Chem

import Mathlib

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

