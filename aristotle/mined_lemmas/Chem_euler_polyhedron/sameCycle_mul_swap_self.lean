import Mathlib

/-!
# Counting the orbits of a permutation, and how a transposition changes the count

This file develops the basic combinatorial tool behind Euler's polyhedron formula:
for a permutation `f` of a finite type, multiplying by a transposition `swap x y`
either *merges* two orbits (if `x` and `y` lie in different orbits of `f`) or
*splits* one orbit into two (if `x` and `y` lie in the same orbit of `f`).
-/

open Equiv Equiv.Perm Function

namespace Polyhedron

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of orbits (cycles, including fixed points) of a permutation of a finite type. -/

lemma sameCycle_mul_swap_self {f : Perm ι} {x y : ι} (h : ¬ f.SameCycle x y) :
    (f * swap x y).SameCycle x y := by
  classical
  have hex : ∃ n, 0 < n ∧ (f ^ n) y = y :=
    ⟨orderOf f, orderOf_pos f, by rw [pow_orderOf_eq_one]; rfl⟩
  set k := Nat.find hex with hk
  obtain ⟨hkpos, hky⟩ := Nat.find_spec hex
  have hnx : ∀ j : ℕ, (f ^ j) y ≠ x := by
    intro j hj
    exact h (SameCycle.symm ⟨(j : ℤ), by simpa using hj⟩)
  have hstep : ∀ j, 0 < j → j < k → (f ^ j) y ≠ x ∧ (f ^ j) y ≠ y := by
    intro j hj hjk
    exact ⟨hnx j, fun hjy => absurd ⟨hj, hjy⟩ (Nat.find_min hex hjk)⟩
  exact ⟨(k : ℤ), by rw [zpow_natCast, pow_mul_swap_apply hstep k hkpos le_rfl, hky]⟩

/-- If `x` and `y` are in the same orbit of `f` and are distinct, then they are in different
orbits of `f * swap x y`: the orbit gets split. -/
