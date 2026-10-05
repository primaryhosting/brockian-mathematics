import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The adjacency matrix of the cycle graph `C₁₃`, with vertices indexed by `ZMod 13`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`. -/

theorem huckel_C13 (lam : ℂ) :
    (∃ v : ZMod 13 → ℂ, v ≠ 0 ∧ adjC13 *ᵥ v = lam • v) ↔
      ∃ k : ℕ, k < 13 ∧ lam = 2 * Real.cos (2 * Real.pi * k / 13) := by
  have hiff : ∀ v : ZMod 13 → ℂ,
      adjC13 *ᵥ v = lam • v ↔ (adjC13 - lam • (1 : Matrix (ZMod 13) (ZMod 13) ℂ)) *ᵥ v = 0 := by
    intro v
    rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.smul_mulVec, Matrix.one_mulVec]
  constructor
  · rintro ⟨v, hv, hveq⟩
    have hdet : (adjC13 - lam • (1 : Matrix (ZMod 13) (ZMod 13) ℂ)).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, (hiff v).mp hveq⟩
    rw [det_adj_sub] at hdet
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hdet
    rw [sub_eq_zero] at hk
    exact ⟨k.val, ZMod.val_lt k, by rw [← hk, mu_eq]⟩
  · rintro ⟨k, hk, rfl⟩
    have hmu : mu (k : ZMod 13) = 2 * (Real.cos (2 * Real.pi * k / 13) : ℂ) := by
      rw [mu_eq, ZMod.val_cast_of_lt hk]
    have hdet : (adjC13 -
        (2 * (Real.cos (2 * Real.pi * k / 13) : ℂ)) • (1 : Matrix (ZMod 13) (ZMod 13) ℂ)).det
        = 0 := by
      rw [det_adj_sub]
      exact Finset.prod_eq_zero (Finset.mem_univ (k : ZMod 13)) (by rw [sub_eq_zero, hmu])
    obtain ⟨v, hv, hveq⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    exact ⟨v, hv, (hiff v).mpr hveq⟩

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

