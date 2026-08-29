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


theorem hasPrimeIn_spec {a b : Nat} (h : hasPrimeIn a b = true) :
    ∃ p : Nat, IsPrimeNat p ∧ a < p ∧ p < b := by
  simp only [hasPrimeIn, List.any_eq_true, List.mem_range'_1] at h
  obtain ⟨p, ⟨hp1, hp2⟩, hpp⟩ := h
  exact ⟨p, (isPrimeB_iff p).mp hpp, by omega, by omega⟩

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 4000000 in
/-- Kernel verification of both prime intervals for every `n ≤ 200`. -/
