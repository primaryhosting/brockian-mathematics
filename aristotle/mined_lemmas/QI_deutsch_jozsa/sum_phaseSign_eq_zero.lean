import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
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

namespace QI

variable {n : ℕ}

/-- The computational basis of `n` qubits, indexed by bit strings `Fin n → Bool`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- The all-zeros bit string. -/

theorem sum_phaseSign_eq_zero {y : Bits n} (hy : y ≠ zeros n) :
    ∑ x : Bits n, phaseSign x y = (0 : ℂ) := by
  have hfac : ∑ x : Bits n, phaseSign x y
      = ∏ i, ∑ b : Bool, (if b && y i then (-1 : ℂ) else 1) :=
    (Fintype.prod_sum (fun i b => if b && y i then (-1 : ℂ) else 1)).symm
  rw [hfac]
  obtain ⟨i, hi⟩ : ∃ i, y i = true := by
    by_contra h
    push_neg at h
    exact hy (funext fun i => by simpa using h i)
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp [hi]

/-- The character sum of `f` in terms of the number of `true` values. -/
