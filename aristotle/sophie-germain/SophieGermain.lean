import Mathlib
namespace Brockian.SophieGermain
/-- Sophie Germain's identity in action: a⁴ + 4b⁴ is composite for a,b > 1
    (it factors as (a²−2ab+2b²)(a²+2ab+2b²)). -/
theorem a4_add_4b4_not_prime (a b : ℕ) (ha : 1 < a) (hb : 1 < b) :
    ¬ (a ^ 4 + 4 * b ^ 4).Prime := by
  sorry
end Brockian.SophieGermain
