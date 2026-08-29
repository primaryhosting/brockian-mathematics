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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Finset

namespace Brockian.ZumkellerNumbers

/-- A natural number `n` is a *Zumkeller number* if its set of divisors can be split into two
parts of equal sum, i.e. there is a set `S` of divisors of `n` whose sum is half of `σ(n)`. -/

lemma disjoint_three_split (a : ℕ) :
    Disjoint (945 : ℕ).divisors (((3:ℕ) ^ a * 35).divisors.image (fun d => 81 * d)) := by
  rw [Finset.disjoint_left]
  rintro x hx hx'
  simp only [Finset.mem_image] at hx'
  obtain ⟨y, -, rfl⟩ := hx'
  have h1 : (81 : ℕ) ∣ 945 := dvd_trans ⟨y, rfl⟩ (Nat.mem_divisors.1 hx).1
  norm_num at h1

