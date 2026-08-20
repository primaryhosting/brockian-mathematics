import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
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

open scoped Matrix

/-! ### A primitive 14-th root of unity and the associated character -/

/-- A primitive 14-th root of unity. -/

theorem Fm_mul_Gm : Fm * Gm = 1 := by
  ext j l
  simp only [Matrix.mul_apply, Fm, Gm]
  have hterm : ∀ k : Fin 14,
      ee (((j : ℕ) : ℤ) * ((k : ℕ) : ℤ)) *
          ((14 : ℂ)⁻¹ * ee (-(((k : ℕ) : ℤ) * ((l : ℕ) : ℤ)))) =
        (14 : ℂ)⁻¹ * ee (((k : ℕ) : ℤ) * (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ))) := by
    intro k
    rw [show ((k : ℕ) : ℤ) * (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ))
        = ((j : ℕ) : ℤ) * ((k : ℕ) : ℤ) + -(((k : ℕ) : ℤ) * ((l : ℕ) : ℤ)) by ring, ee_add]
    ring
  simp only [hterm, ← Finset.mul_sum]
  by_cases h : j = l
  · subst h
    rw [show ((j : ℕ) : ℤ) - ((j : ℕ) : ℤ) = 0 by ring]
    simp only [mul_zero]
    rw [sum_ee_zero, Matrix.one_apply_eq]
    norm_num
  · have hd : ¬ (14 : ℤ) ∣ (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ)) := by
      have hj := j.isLt
      have hl := l.isLt
      have hne : ((j : ℕ) : ℤ) ≠ ((l : ℕ) : ℤ) := by
        simpa [Fin.ext_iff] using h
      omega
    rw [sum_ee _ hd, mul_zero, Matrix.one_apply_ne h]

