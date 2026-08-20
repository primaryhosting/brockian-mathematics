import Mathlib

/-!
# Dft Inversion
Category: Characters
Target: Brockian.Characters5.dft_inversion
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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/

lemma sum_e_univ : ∑ b : ZMod 5, e b = 0 := by
  have h : ∑ b : ZMod 5, e b = ∑ j ∈ Finset.range 5, omega ^ j := by
    simp only [e]
    apply Finset.sum_nbij' (fun b : ZMod 5 => b.val) (fun j : ℕ => (j : ZMod 5)) <;>
      intros <;> simp_all [ZMod.val_lt]
  rw [h]
  exact isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)

