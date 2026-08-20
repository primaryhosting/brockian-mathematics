import Mathlib
/-!
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to be the very first command in a file, so the header
comment appears immediately after it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace QPhys

open Finset

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The degree-`N` homogeneous component of the product `exp a * exp b`. -/

theorem bcH_special_heisenberg :
    ∃ a b : Matrix (Fin 3) (Fin 3) ℚ,
      IsNilpotent a ∧ IsNilpotent b ∧ Commute a (a * b - b * a) ∧ Commute b (a * b - b * a) ∧
        a * b - b * a ≠ 0 ∧
        IsNilpotent.exp a * IsNilpotent.exp b
          = IsNilpotent.exp (a + b + (2⁻¹ : ℚ) • (a * b - b * a)) := by
  refine ⟨!![0,1,0;0,0,0;0,0,0], !![0,0,0;0,0,1;0,0,0], ⟨2, ?_⟩, ⟨2, ?_⟩, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two]
  · show _ * _ = _ * _
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · show _ * _ = _ * _
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · intro h
    have h2 := congrFun (congrFun h 0) 2
    simp at h2
  · exact bcH_special ⟨2, by ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two]⟩
      ⟨2, by ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two]⟩
      (by show _ * _ = _ * _; ext i j; fin_cases i <;> fin_cases j <;> simp)
      (by show _ * _ = _ * _; ext i j; fin_cases i <;> fin_cases j <;> simp)

end QPhys

