/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The requested header is reproduced above as a plain block comment: Lean 4 does not allow a
-- module docstring `/-! ... -/` to precede the `import` lines.)

import Mathlib

/-!
## Simon's problem

Simon's problem: a function `f` on `n`-bit strings is promised to be two-to-one with
`f x = f y ↔ y = x ∨ y = x + s` for a hidden nonzero secret `s`; the task is to find `s`.

This file formalises the two information-theoretic facts behind the statement
"Simon's problem takes `O(n)` quantum queries but `Ω(2^(n/2))` classical queries":

* **Quantum side.** Each run of Simon's quantum subroutine returns a uniformly random
  vector `y` in the hyperplane `s^⊥`. We show that `n` such vectors always suffice:
  for every nonzero `s` there is a set `Y` of at most `n` vectors orthogonal to `s`
  such that `s` is the unique nonzero vector orthogonal to all of `Y`. Hence `O(n)`
  quantum queries pin down the secret.

* **Classical side.** A classical algorithm only learns something about `s` when two of
  its queries collide. We show that a query set `Q` that is guaranteed to contain a
  collision for *every* possible secret must satisfy `2 ^ n ≤ Q.card ^ 2`, i.e.
  `Q.card ≥ 2 ^ (n / 2)`. Moreover, if `Q.card ^ 2 + 3 ≤ 2 ^ n`, then there are two
  *different* secrets whose Simon functions agree on `Q` up to a global relabelling of
  the output values, so no classical algorithm making those queries can tell them apart.
-/

namespace QI

open Finset

/-- `n`-bit strings, viewed as vectors over the field with two elements. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The mod-2 inner product of two bit strings. -/

theorem simon_quantum_queries {n : ℕ} {s : Bits n} (hs : s ≠ 0) :
    ∃ Y : Finset (Bits n), Y.card ≤ n ∧ (∀ y ∈ Y, dotp y s = 0) ∧
      ∀ t : Bits n, (∀ y ∈ Y, dotp y t = 0) → t = 0 ∨ t = s := by
  classical
  obtain ⟨j, hj⟩ := exists_pivot hs
  set v : Fin n → Bits n :=
    fun i k => (if k = i then 1 else 0) + s i * (if k = j then 1 else 0) with hv
  have hdot : ∀ (i : Fin n) (t : Bits n), dotp (v i) t = t i + s i * t j := by
    intro i t
    simp [hv, dotp, add_mul, Finset.sum_add_distrib, ite_mul]
  refine ⟨(Finset.univ.erase j).image v, ?_, ?_, ?_⟩
  · refine le_trans Finset.card_image_le ?_
    simp [Finset.card_erase_of_mem]
  · intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨i, -, rfl⟩ := hy
    rw [hdot, hj, mul_one, zmod2_add_self]
  · intro t ht
    have key : ∀ i : Fin n, i ≠ j → t i = s i * t j := by
      intro i hi
      have := ht (v i) (Finset.mem_image_of_mem v (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩))
      rw [hdot] at this
      exact zmod2_eq_of_add_eq_zero this
    rcases zmod2_cases (t j) with h0 | h1
    · left
      funext i
      by_cases hi : i = j
      · subst hi; simpa using h0
      · simpa [h0] using key i hi
    · right
      funext i
      by_cases hi : i = j
      · subst hi; rw [h1, hj]
      · simpa [h1] using key i hi

/-! ### Classical side -/

