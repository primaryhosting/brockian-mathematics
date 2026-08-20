import Mathlib

set_option maxHeartbeats 200000

example (r : ZMod 2) (h0 : (0 : ZMod 2) ≠ r) (h1 : (1 : ZMod 2) ≠ r) : False := by
  fin_cases r <;> simp_all

example : ({2, 5, 29} : Finset ℕ).erase 2 = {5, 29} := by
  rw [Finset.erase_insert (by simp)]

example : (∏ p ∈ ({5, 29} : Finset ℕ), (((p : ℚ) - 1) / ((p : ℚ) - 2))) = 112 / 81 := by
  rw [Finset.prod_insert (by simp), Finset.prod_singleton]
  norm_num

example (g : ℕ) (hmod : g % 2 = 1) : (((g : ℤ)) : ZMod 2) = 1 := by
  push_cast
  rw [← ZMod.natCast_mod g 2, hmod]
  norm_num

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

namespace Brockian

/-- A finite set `H` of integers is *admissible* (in the sense of Hardy–Littlewood
prime constellations) if for every prime `p` the reductions of the elements of `H`
mod `p` do not cover all residue classes mod `p`. -/

theorem one_le_singularSeriesFactor (g : ℕ) : 1 ≤ singularSeriesFactor g := by
  rw [singularSeriesFactor]
  calc (1 : ℚ) = ∏ _p ∈ (Nat.primeFactors g).erase 2, (1 : ℚ) := by simp
  _ ≤ ∏ p ∈ (Nat.primeFactors g).erase 2, ((p : ℚ) - 1) / ((p : ℚ) - 2) := by
      refine Finset.prod_le_prod (fun i _ => by norm_num) (fun p hp => ?_)
      have hp2 : p ≠ 2 := Finset.ne_of_mem_erase hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
      have h3 : 3 ≤ p := by have := hpp.two_le; omega
      have h3' : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h3
      rw [le_div_iff₀ (by linarith)]
      linarith

