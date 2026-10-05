import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
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

open Complex Matrix SimpleGraph

/-- A primitive 20-th root of unity. -/

lemma F_shift_sub (j k : Fin 20) : F (j - 1) k = F j k * w ^ (19 * (k : ℕ)) := by
  have hneg : (-1 : Fin 20) = 19 := rfl
  have hj : (j : Fin 20) - 1 = j + 19 := by rw [sub_eq_add_neg, hneg]
  have hv : ((j + 19 : Fin 20) : ℕ) = ((j : ℕ) + 19) % 20 := by
    simp [Fin.val_add]
  have hcong : ((j : ℕ) + 19) % 20 * (k : ℕ) ≡ ((j : ℕ) + 19) * (k : ℕ) [MOD 20] :=
    Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
  rw [hj, F, F, hv, w_pow_congr hcong, ← pow_add]
  congr 1
  ring

/-- The adjacency matrix of `C₂₀` is diagonalized by the Fourier matrix. -/
