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


theorem noDivFrom_spec (p : Nat) :
    ∀ fuel k, 0 < k → (noDivFrom p k fuel = true ↔
      ∀ m, k ≤ m → m < k + fuel → m * m ≤ p → p % m ≠ 0) := by
  intro fuel
  induction fuel with
  | zero => intro k hk; simp [noDivFrom]; omega
  | succ fuel ih =>
    intro k hk
    rw [show noDivFrom p k (fuel + 1) =
        (if p < k * k then true
         else if p % k == 0 then false
         else noDivFrom p (k + 1) fuel) from rfl]
    by_cases hlt : p < k * k
    · simp only [hlt, if_pos]
      constructor
      · intro _ m hm _ hmm
        exfalso
        have : k * k ≤ m * m := Nat.mul_le_mul hm hm
        omega
      · intro _; trivial
    · simp only [hlt, if_false]
      by_cases hmod : p % k = 0
      · simp only [hmod, beq_self_eq_true, if_pos]
        constructor
        · intro h; exact absurd h (by simp)
        · intro h
          exact absurd hmod (h k (Nat.le_refl _) (by omega) (by omega))
      · simp only [beq_iff_eq]
        rw [if_neg hmod, ih (k + 1) (by omega)]
        constructor
        · intro h m hm hm2 hmm
          rcases Nat.eq_or_lt_of_le hm with rfl | h1
          · exact hmod
          · exact h m (by omega) (by omega) hmm
        · intro h m hm hm2 hmm
          exact h m (by omega) (by omega) hmm

/-- If a number has a nontrivial divisor, it has one that is at most its square root. -/
