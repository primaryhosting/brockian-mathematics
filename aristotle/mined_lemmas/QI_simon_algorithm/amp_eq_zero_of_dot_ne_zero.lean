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


theorem amp_eq_zero_of_dot_ne_zero {Y : Type*} [DecidableEq Y] {s : Vec n} {f : Vec n → Y}
    (h : IsSimon s f) {y : Vec n} (hy : dot s y ≠ 0) (z : Y) : amp f y z = 0 := by
  have key : ∑ x : Vec n, chi (dot x y) * (if f x = z then (1 : ℂ) else 0) = 0 := by
    set F : Vec n → ℂ := fun x => chi (dot x y) * (if f x = z then (1 : ℂ) else 0) with hF
    have hshift : ∑ x : Vec n, F (x + s) = ∑ x : Vec n, F x :=
      Fintype.sum_equiv (Equiv.addRight s) (fun x => F (x + s)) F (fun _ => rfl)
    have hneg : ∀ x : Vec n, F (x + s) = -F x := by
      intro x
      have h1 : chi (dot (x + s) y) = -chi (dot x y) := by
        rw [dot_add_left, chi_add, show chi (dot s y) = -1 by simp [chi, hy]]
        ring
      have h2 : f (x + s) = f x := h.period x
      simp only [hF, h1, h2]
      ring
    have h2 : ∑ x : Vec n, F x = -∑ x : Vec n, F x := by
      calc ∑ x : Vec n, F x = ∑ x : Vec n, F (x + s) := hshift.symm
        _ = ∑ x : Vec n, -F x := Finset.sum_congr rfl fun x _ => hneg x
        _ = -∑ x : Vec n, F x := by rw [Finset.sum_neg_distrib]
    have h4 : ∑ x : Vec n, F x + ∑ x : Vec n, F x = 0 := add_eq_zero_iff_eq_neg.mpr h2
    have h5 : (2 : ℂ) * ∑ x : Vec n, F x = 0 := by rw [two_mul]; exact h4
    simpa using h5
  rw [amp, key, mul_zero]

/-- If `y` is orthogonal to the secret, the amplitude of `(y, f x₀)` is
`2·(-1)^{x₀·y}/2^n`; in particular it is nonzero, so every `y ⊥ s` is a possible
measurement outcome. -/
