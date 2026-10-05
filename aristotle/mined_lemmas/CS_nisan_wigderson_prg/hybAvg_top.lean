import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
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

namespace CS

open Finset

variable {n m : ℕ}

/-- The real value of a boolean: `1` for `true`, `0` for `false`. -/

lemma hybAvg_top (f : Fin m → (Fin n → Bool) → Bool) (T : (Fin m → Bool) → Bool) :
    hybAvg f T m = unifAvg (fun x : Fin n → Bool => bval (T (nwGen f x))) := by
  have h : ∀ (x : Fin n → Bool) (u : Fin m → Bool), hyb f m x u = nwGen f x := by
    intro x u; funext j; simp [hyb, nwGen, j.isLt]
  simp only [hybAvg, unifAvg, h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat, ← Finset.mul_sum]
  rw [mul_comm ((2:ℝ)^n) ((2:ℝ)^m), mul_div_mul_left]
  positivity

