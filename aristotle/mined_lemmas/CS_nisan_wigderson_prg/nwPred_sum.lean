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

lemma nwPred_sum (f : Fin m → (Fin n → Bool) → Bool) (T : (Fin m → Bool) → Bool)
    (S : Finset (Fin n)) (i : Fin m)
    (hf : ∀ x y : Fin n → Bool, (∀ j ∈ S, x j = y j) → f i x = f i y) :
    (∑ ui : Bool, ∑ tail : Fin m → Bool, ∑ z : Fin n → Bool, ∑ x : Fin n → Bool,
        bval (nwPred f T i S ui tail z x == f i x))
      = 2 ^ n * ((2 : ℝ) ^ m * 2 ^ n
          + 2 * (∑ x : Fin n → Bool, ∑ u : Fin m → Bool, bval (T (hyb f ((i : ℕ) + 1) x u)))
          - 2 * (∑ x : Fin n → Bool, ∑ u : Fin m → Bool, bval (T (hyb f (i : ℕ) x u)))) := by
  have hmask : ∀ (ui : Bool) (tail : Fin m → Bool) (z x : Fin n → Bool),
      bval (nwPred f T i S ui tail z x == f i x)
        = (fun x' : Fin n → Bool =>
            bval ((if T (nwStr f i x' tail ui) then ui else !ui) == f i x')) (maskMerge S x z) := by
    intro ui tail z x
    have h1 : f i x = f i (maskMerge S x z) := hf _ _ (fun j hj => by simp [maskMerge, hj])
    simp only [nwPred]
    rw [h1]
  have stepA : ∀ (ui : Bool) (tail : Fin m → Bool),
      (∑ z : Fin n → Bool, ∑ x : Fin n → Bool, bval (nwPred f T i S ui tail z x == f i x))
        = 2 ^ n * ∑ x' : Fin n → Bool,
            bval ((if T (nwStr f i x' tail ui) then ui else !ui) == f i x') := by
    intro ui tail
    rw [Finset.sum_comm]
    simp only [hmask]
    exact sum_maskMerge S (fun x' : Fin n → Bool =>
      bval ((if T (nwStr f i x' tail ui) then ui else !ui) == f i x'))
  have stepB : ∀ (tail : Fin m → Bool) (x' : Fin n → Bool),
      (∑ ui : Bool, bval ((if T (nwStr f i x' tail ui) then ui else !ui) == f i x'))
        = 1 + 2 * bval (T (hyb f ((i : ℕ) + 1) x' tail))
            - ∑ v : Bool, bval (T (hyb f (i : ℕ) x' (Function.update tail i v))) := by
    intro tail x'
    have h := bool_pred_sum (fun v => T (nwStr f i x' tail v)) (f i x')
    have h2 : (∑ v : Bool, bval (T (nwStr f i x' tail v)))
        = ∑ v : Bool, bval (T (hyb f (i : ℕ) x' (Function.update tail i v))) :=
      Finset.sum_congr rfl (fun v _ => by rw [nwStr_eq_hyb])
    rw [nwStr_eq_hyb_succ, h2] at h
    exact h
  have stepC : ∀ tail : Fin m → Bool,
      (∑ ui : Bool, ∑ x' : Fin n → Bool,
          bval ((if T (nwStr f i x' tail ui) then ui else !ui) == f i x'))
        = ∑ x' : Fin n → Bool, (1 + 2 * bval (T (hyb f ((i : ℕ) + 1) x' tail))
            - ∑ v : Bool, bval (T (hyb f (i : ℕ) x' (Function.update tail i v)))) := by
    intro tail
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun x' _ => stepB tail x')
  have expand : ∀ tail : Fin m → Bool,
      (∑ x' : Fin n → Bool, (1 + 2 * bval (T (hyb f ((i : ℕ) + 1) x' tail))
          - ∑ v : Bool, bval (T (hyb f (i : ℕ) x' (Function.update tail i v)))))
        = 2 ^ n + 2 * (∑ x' : Fin n → Bool, bval (T (hyb f ((i : ℕ) + 1) x' tail)))
            - ∑ x' : Fin n → Bool, ∑ v : Bool,
                bval (T (hyb f (i : ℕ) x' (Function.update tail i v))) := by
    intro tail
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have h1 : (∑ ui : Bool, ∑ tail : Fin m → Bool, ∑ z : Fin n → Bool, ∑ x : Fin n → Bool,
      bval (nwPred f T i S ui tail z x == f i x))
      = ∑ ui : Bool, ∑ tail : Fin m → Bool, 2 ^ n * ∑ x' : Fin n → Bool,
          bval ((if T (nwStr f i x' tail ui) then ui else !ui) == f i x') :=
    Finset.sum_congr rfl (fun ui _ => Finset.sum_congr rfl (fun tail _ => stepA ui tail))
  rw [h1, Finset.sum_comm]
  simp only [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_congr rfl (fun tail _ => stepC tail),
    Finset.sum_congr rfl (fun tail _ => expand tail),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hswap : (∑ tail : Fin m → Bool, ∑ x' : Fin n → Bool,
      bval (T (hyb f ((i : ℕ) + 1) x' tail)))
      = ∑ x : Fin n → Bool, ∑ u : Fin m → Bool, bval (T (hyb f ((i : ℕ) + 1) x u)) :=
    Finset.sum_comm
  have hswap2 : (∑ tail : Fin m → Bool, ∑ x' : Fin n → Bool, ∑ v : Bool,
      bval (T (hyb f (i : ℕ) x' (Function.update tail i v))))
      = 2 * ∑ x : Fin n → Bool, ∑ u : Fin m → Bool, bval (T (hyb f (i : ℕ) x u)) := by
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x' _ => sum_update_bool i (fun u => bval (T (hyb f (i : ℕ) x' u))))
  rw [hswap, hswap2]
  simp

