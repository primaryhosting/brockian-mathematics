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

lemma card_surv_double {m k : ℕ} (hk : k ≤ m+1) {y y' : Vec m} (hne : y ≠ y') :
    4^k * (univ.filter (fun h : Hsp m => survives h k y ∧ survives h k y')).card
      = (2^(m+1))^(m+1) := by
  classical
  set c := (univ.filter (fun p : Vec m × ZMod 2 => ip p.1 y = p.2 ∧ ip p.1 y' = p.2)).card with hc
  have hc2 : 2 * c = 2^m := card_pair_double hne
  have hset : (univ.filter (fun h : Hsp m => survives h k y ∧ survives h k y'))
      = Fintype.piFinset (fun i : Fin (m+1) =>
          if (i:ℕ) < k then
            univ.filter (fun p : Vec m × ZMod 2 => ip p.1 y = p.2 ∧ ip p.1 y' = p.2)
          else univ) := by
    ext h
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, survives]
    constructor
    · intro hh i
      by_cases hi : (i:ℕ) < k <;> simp [hi, hh.1 i, hh.2 i]
    · intro hh
      constructor <;>
      · intro i hi
        have := hh i
        simp [hi] at this
        tauto
  rw [hset, Fintype.card_piFinset]
  rw [show (∏ i : Fin (m+1),
      (if (i:ℕ) < k then
        univ.filter (fun p : Vec m × ZMod 2 => ip p.1 y = p.2 ∧ ip p.1 y' = p.2)
       else univ).card)
      = ∏ i : Fin (m+1), (if (i:ℕ) < k then c else 2^(m+1)) from ?_]
  · rw [prod_ite_lt hk]
    rw [← mul_assoc]
    rw [show (4:ℕ)^k * c^k = (2^(m+1))^k by
      rw [← mul_pow]
      congr 1
      have h4 : (4:ℕ) * c = 2 * (2 * c) := by ring
      rw [h4, hc2, pow_succ]
      ring]
    rw [← pow_add]
    congr 1
    omega
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    by_cases hi : (i:ℕ) < k <;> simp [hi, hc, pow_succ]

/-- Isolation for a fixed, well chosen number `k` of hash rows. -/
