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

/-
Isolation (Valiant–Vazirani) lemma over `GF(2)`, in the counting form needed for
Toda's theorem.
-/
import Mathlib

namespace CS.Toda

open Finset

/-- Bit vectors of length `m`, as vectors over `GF(2)`. -/
abbrev Vec (m : ℕ) := Fin m → ZMod 2

/-- The standard `GF(2)`-bilinear form. -/

lemma card_surv_single {m k : ℕ} (hk : k ≤ m+1) (y : Vec m) :
    2^k * (univ.filter (fun h : Hsp m => survives h k y)).card = (2^(m+1))^(m+1) := by
  classical
  have hset : (univ.filter (fun h : Hsp m => survives h k y))
      = Fintype.piFinset (fun i : Fin (m+1) =>
          if (i:ℕ) < k then univ.filter (fun p : Vec m × ZMod 2 => ip p.1 y = p.2) else univ) := by
    ext h
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, survives]
    constructor
    · intro hh i
      by_cases hi : (i:ℕ) < k <;> simp [hi, hh i]
    · intro hh i hi
      have := hh i
      simp [hi] at this
      exact this
  rw [hset, Fintype.card_piFinset]
  rw [show (∏ i : Fin (m+1),
      (if (i:ℕ) < k then univ.filter (fun p : Vec m × ZMod 2 => ip p.1 y = p.2) else univ).card)
      = ∏ i : Fin (m+1), (if (i:ℕ) < k then 2^m else 2^(m+1)) from ?_]
  · rw [prod_ite_lt hk]
    rw [← mul_assoc]
    rw [show (2:ℕ)^k * (2^m)^k = (2^(m+1))^k by rw [← mul_pow, ← pow_succ']]
    rw [← pow_add]
    congr 1
    omega
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    by_cases hi : (i:ℕ) < k <;> simp [hi, card_pair_single y, pow_succ]

/-- The number of hashes under which two distinct `y, y'` both survive. -/
