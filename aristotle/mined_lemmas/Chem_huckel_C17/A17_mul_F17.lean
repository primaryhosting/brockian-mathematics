/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
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

namespace Chem

open Matrix Polynomial

/-- A primitive 17-th root of unity. -/

lemma A17_mul_F17 : A17 * F17 = F17 * D17 := by
  ext i k
  have hne : (i - 1 : Fin 17) ≠ i + 1 := by
    intro h
    rw [sub_eq_add_neg] at h
    have h2 : (-1 : Fin 17) = 1 := add_left_cancel h
    exact absurd h2 (by decide)
  rw [Matrix.mul_apply]
  have hsum : ∀ j : Fin 17, A17 i j * F17 j k
      = (if j = i - 1 then F17 j k else 0) + (if j = i + 1 then F17 j k else 0) := by
    intro j
    rw [A17_apply]
    by_cases h1 : j = i - 1 <;> by_cases h2 : j = i + 1 <;>
      simp [h1, h2, hne, Ne.symm hne]
  rw [Finset.sum_congr rfl (fun j _ => hsum j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (i - 1) (fun j => F17 j k),
    Finset.sum_ite_eq' Finset.univ (i + 1) (fun j => F17 j k)]
  simp only [Finset.mem_univ, if_true]
  rw [D17, Matrix.mul_diagonal, F17_apply, F17_apply, F17_apply, ← zeta_add_zeta_neg]
  have e1 : (i - 1) * k = i * k + (-k) := by rw [sub_mul, one_mul, sub_eq_add_neg]
  have e2 : (i + 1) * k = i * k + k := by rw [add_mul, one_mul]
  rw [e1, e2, zeta_add, zeta_add]
  ring

