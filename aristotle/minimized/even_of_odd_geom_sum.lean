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

set_option grind.warning false

lemma even_of_odd_geom_sum {p e : ℕ} (hp : Odd p)
    (h : Odd (∑ k ∈ Finset.range (e + 1), p ^ k)) : Even e := by
  rw [Nat.odd_iff, Finset.sum_nat_mod] at h
  have hk : ∀ k ∈ Finset.range (e + 1), p ^ k % 2 = 1 := fun k _ => Nat.odd_iff.mp hp.pow
  rw [Finset.sum_congr rfl hk] at h
  simp at h
  rw [Nat.even_iff]
  omega

/-- A positive natural number all of whose prime exponents are even is a square. -/
