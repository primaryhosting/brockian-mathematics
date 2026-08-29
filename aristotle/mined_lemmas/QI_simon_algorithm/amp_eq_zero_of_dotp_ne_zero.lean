/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- repeated as a module docstring immediately after the import.)

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Bit vectors -/

/-- `n`-bit strings, as a vector space over `ZMod 2`. -/
abbrev BV (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}


theorem amp_eq_zero_of_dotp_ne_zero {f : BV n → BV n} {s : BV n} (h : IsSimon f s)
    (y v : BV n) (hy : dotp s y = 1) : amp f y v = 0 := by
  set g : BV n → ℂ := fun x => if f x = v then chi (dotp x y) else 0 with hg
  have hstep : ∀ x, g (x + s) = - g x := by
    intro x
    simp only [hg, h.shift x, dotp_add_left, hy, chi_add, chi_one]
    split <;> ring
  have h1 : ∑ x : BV n, g (x + s) = ∑ x : BV n, g x :=
    Equiv.sum_comp (Equiv.addRight s) g
  have h2 : ∑ x : BV n, g (x + s) = - ∑ x : BV n, g x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun x _ => hstep x)
  have hS : (∑ x : BV n, g x) = - ∑ x : BV n, g x := h1.symm.trans h2
  show (∑ x : BV n, g x) = 0
  linear_combination (1 / 2 : ℂ) * hS

