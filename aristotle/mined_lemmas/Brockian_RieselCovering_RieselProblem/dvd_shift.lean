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

import Mathlib
import Brockian.RieselCovering

/-!
# Riesel Problem — Mathlib interface

Companion to `Brockian.RieselCovering` (which is import-free): the same result phrased with
Mathlib's `Nat.Prime`.
-/

namespace Brockian
namespace RieselCovering

/-- `509203 * 2 ^ n - 1` is not prime for any `n ≥ 1`, stated with `Nat.Prime`. -/

theorem dvd_shift {p n : Nat} (h24 : p ∣ 16777215) (h : p ∣ k * 2 ^ n - 1) :
    p ∣ k * 2 ^ (n + 24) - 1 := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h24
  have hx : 0 < k * 2 ^ n := Nat.mul_pos (by decide) (Nat.two_pow_pos n)
  have hp : (2 : Nat) ^ (n + 24) = 2 ^ n * 16777216 := by rw [Nat.pow_add]
  refine ⟨16777216 * a + b, ?_⟩
  have key : p * (16777216 * a + b) = 16777216 * (p * a) + p * b := by
    rw [Nat.mul_add, Nat.mul_left_comm]
  rw [hp, key, ← ha, ← hb]
  unfold k at *
  omega

/-- Iterated form of `dvd_shift`. -/
