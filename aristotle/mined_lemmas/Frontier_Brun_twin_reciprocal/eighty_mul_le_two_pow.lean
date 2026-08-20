import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

lemma eighty_mul_le_two_pow {l : ℕ} (hl : 10 ≤ l) : 80 * l ≤ 2 ^ l := by
  induction l with
  | zero => omega
  | succ l ih =>
      rcases Nat.lt_or_ge l 10 with h | h
      · have hl9 : l = 9 := by omega
        subst hl9
        norm_num
      · have hih := ih h
        have h2 : (80 : ℕ) ≤ 2 ^ l := by
          calc (80 : ℕ) ≤ 2 ^ 7 := by norm_num
            _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) (by omega)
        calc 80 * (l + 1) = 80 * l + 80 := by ring
          _ ≤ 2 ^ l + 2 ^ l := by omega
          _ = 2 ^ (l + 1) := by ring

