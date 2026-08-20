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

set_option grind.warning false

namespace CS

/-- `(b^k)^(log_b a) = a^k`. -/

theorem master_theorem_case1_isTheta
    (a : ℝ) (b : ℕ) (eps C : ℝ) (f T : ℕ → ℝ)
    (ha : 1 ≤ a) (hb : 2 ≤ b) (heps : 0 < eps) (hC : 0 < C)
    (hfnonneg : ∀ n, 0 ≤ f n)
    (hf : ∀ n : ℕ, 1 ≤ n → f n ≤ C * (n : ℝ) ^ (Real.logb b a - eps))
    (hT1 : 0 < T 1)
    (hrec : ∀ k : ℕ, T (b ^ (k + 1)) = a * T (b ^ k) + f (b ^ (k + 1))) :
    (fun k : ℕ => T (b ^ k)) =Θ[Filter.atTop]
      (fun k : ℕ => ((b : ℝ) ^ k) ^ (Real.logb b a)) := by
  obtain ⟨c₁, c₂, hc₁, _hc₂, h⟩ :=
    master_theorem_case1 a b eps C f T ha hb heps hC hfnonneg hf hT1 hrec
  have hb0 : (0:ℝ) < (b:ℝ) := by
    have : (0:ℕ) < b := by omega
    exact_mod_cast this
  refine isTheta_of_two_sided_bounds _ _ c₁ c₂ hc₁
    (fun k => Real.rpow_pos_of_pos (pow_pos hb0 k) _) (fun k => ?_)
  have := h (b ^ k) ⟨k, rfl⟩
  rwa [Nat.cast_pow] at this

end CS

