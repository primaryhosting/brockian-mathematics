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
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace QI

/-! ## Basic setup: the group `(ZMod 2)^n` -/

/-- The domain of Simon's problem: bit strings of length `n`, viewed as the
elementary abelian group `(ZMod 2)^n` under bitwise XOR (= addition). -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}


theorem amp_of_dot_eq_zero {Y : Type*} [DecidableEq Y] {s : Vec n} {f : Vec n → Y}
    (h : IsSimon s f) {y : Vec n} (hy : dot s y = 0) (x₀ : Vec n) :
    amp f y (f x₀) = (1 / 2 ^ n) * (2 * chi (dot x₀ y)) := by
  classical
  have hne : x₀ ≠ x₀ + s := by
    intro e
    apply h.1
    have h5 : x₀ + x₀ = s := vec_eq_iff_add.mpr e
    rw [vec_add_self] at h5
    exact h5.symm
  have hfib : ∀ x : Vec n, chi (dot x y) * (if f x = f x₀ then (1 : ℂ) else 0)
      = if x ∈ ({x₀, x₀ + s} : Finset (Vec n)) then chi (dot x y) else 0 := by
    intro x
    by_cases hx : f x = f x₀
    · rcases (h.2 x x₀).1 hx with h1 | h1
      · simp [h1]
      · have h2 : x = x₀ + s := vec_eq_iff_add.mp (by rw [add_comm]; exact h1)
        rw [if_pos hx, if_pos (show x ∈ ({x₀, x₀ + s} : Finset (Vec n)) by simp [h2]), mul_one]
    · have hx1 : x ≠ x₀ := fun e => hx (by rw [e])
      have hx2 : x ≠ x₀ + s := by
        intro e
        exact hx (by rw [e]; exact h.period x₀)
      simp [hx, hx1, hx2]
  have hsum : ∑ x : Vec n, chi (dot x y) * (if f x = f x₀ then (1 : ℂ) else 0)
      = 2 * chi (dot x₀ y) := by
    simp only [hfib]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair hne]
    rw [dot_add_left, chi_add, show chi (dot s y) = 1 by simp [chi, hy]]
    ring
  rw [amp, hsum]

/-! ### `n - 1` well chosen outcomes determine the secret -/

/-- The vectors used in the analysis: for `i ≠ j` (where `s j = 1`),
`simonBasis s j i = e_i + s_i · e_j` is orthogonal to `s`. -/
