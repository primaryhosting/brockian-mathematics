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


theorem exists_small_divisor (p : Nat) :
    ∀ b m, m ≤ b → 2 ≤ m → m ∣ p → m < p → ∃ d, 2 ≤ d ∧ d ∣ p ∧ d * d ≤ p := by
  intro b
  induction b with
  | zero => intro m hmb h2; omega
  | succ b ih =>
    intro m hmb h2 hdvd hmp
    by_cases hsq : m * m ≤ p
    · exact ⟨m, h2, hdvd, hsq⟩
    · obtain ⟨e, he⟩ := hdvd
      have he0 : e ≠ 0 := by rintro rfl; simp at he; omega
      have he1 : e ≠ 1 := by rintro rfl; simp at he; omega
      have hlt : m * e < m * m := by rw [← he]; omega
      have hem : e < m := Nat.lt_of_mul_lt_mul_left hlt
      have hedvd : e ∣ p := ⟨m, by rw [he]; exact Nat.mul_comm m e⟩
      exact ih e (by omega) (by omega) hedvd (by omega)

