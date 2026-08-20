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

lemma pow_mul_swap_apply {f : Perm ι} {x y : ι} {k : ℕ}
    (hstep : ∀ j, 0 < j → j < k → (f ^ j) y ≠ x ∧ (f ^ j) y ≠ y) :
    ∀ j, 0 < j → j ≤ k → ((f * swap x y) ^ j) x = (f ^ j) y := by
  intro j
  induction j with
  | zero => omega
  | succ n ih =>
    intro _ hle
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [pow_one, Perm.mul_apply, swap_apply_left]
    · have h1 : ((f * swap x y) ^ n) x = (f ^ n) y := ih hn (by omega)
      obtain ⟨h2, h3⟩ := hstep n hn (by omega)
      calc ((f * swap x y) ^ (n + 1)) x = (f * swap x y) (((f * swap x y) ^ n) x) := by
            rw [pow_succ']; rfl
        _ = (f * swap x y) ((f ^ n) y) := by rw [h1]
        _ = f ((f ^ n) y) := by simp [Perm.mul_apply, swap_apply_of_ne_of_ne h2 h3]
        _ = (f ^ (n + 1)) y := by rw [pow_succ']; rfl

/-- If `x` and `y` are in different orbits of `f`, then they are in the same orbit of
`f * swap x y`: the two orbits get merged. -/
