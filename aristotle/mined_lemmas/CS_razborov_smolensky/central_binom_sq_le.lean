import RequestProject.Circuits
import RequestProject.LowDegree

/-!
# MOD_p is not approximable by low degree functions over a field of characteristic q

This is the second half of Smolensky's argument: if the function `x ↦ ζ^{|x|}`
(`ζ` a primitive `p`-th root of unity in a field `F` of characteristic `q`) agrees
with a function of degree `D` on a set `G` of inputs, then `G` is small.
-/

namespace CS

open Finset

open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

/-- The monomial `∏_{i ∈ S} ζ^{x_i}` in the transformed variables. -/

theorem central_binom_sq_le (m : ℕ) : (3 * m + 1) * ((2 * m).choose m) ^ 2 ≤ 16 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hrec : (m + 1) * ((2 * (m + 1)).choose (m + 1)) = 2 * (2 * m + 1) * ((2 * m).choose m) :=
        Nat.succ_mul_centralBinom_succ m
      set c := (2 * m).choose m with hc
      set c' := (2 * (m + 1)).choose (m + 1) with hc'
      -- multiply the goal by `(m+1)^2`
      have key : (m + 1) ^ 2 * ((3 * (m + 1) + 1) * c' ^ 2)
          ≤ (m + 1) ^ 2 * 16 ^ (m + 1) := by
        have h1 : (m + 1) ^ 2 * ((3 * (m + 1) + 1) * c' ^ 2)
            = (3 * m + 4) * ((m + 1) * c') ^ 2 := by ring
        rw [h1, hrec]
        have h2 : (3 * m + 4) * (2 * (2 * m + 1) * c) ^ 2
            = ((2 * m + 1) ^ 2 * (3 * m + 4)) * (4 * c ^ 2) := by ring
        rw [h2]
        have h3 : (2 * m + 1) ^ 2 * (3 * m + 4) ≤ 4 * (m + 1) ^ 2 * (3 * m + 1) := by nlinarith
        calc ((2 * m + 1) ^ 2 * (3 * m + 4)) * (4 * c ^ 2)
            ≤ (4 * (m + 1) ^ 2 * (3 * m + 1)) * (4 * c ^ 2) :=
              Nat.mul_le_mul_right _ h3
          _ = 16 * (m + 1) ^ 2 * ((3 * m + 1) * c ^ 2) := by ring
          _ ≤ 16 * (m + 1) ^ 2 * 16 ^ m := Nat.mul_le_mul_left _ ih
          _ = (m + 1) ^ 2 * 16 ^ (m + 1) := by ring
      exact Nat.le_of_mul_le_mul_left key (by positivity)

/-- Exactly half of the binomial mass lies off the middle coefficient. -/
