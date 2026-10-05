import Mathlib
/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
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

set_option grind.warning false

/-!
## The cap set problem

We prove the Croot–Lev–Pach / Ellenberg–Gijswijt bound: a subset of `𝔽₃ⁿ` containing no
non-trivial three-term arithmetic progression has size `o(3ⁿ)`.
-/

namespace CapSet

open Finset

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Points of `𝔽₃ⁿ`. -/
abbrev Pt (n : ℕ) := Fin n → ZMod 3

/-- Exponent vectors of reduced monomials (each exponent is `0`, `1` or `2`). -/
abbrev Exp (n : ℕ) := Fin n → Fin 3

/-- The monomial function `x ↦ ∏ i, x i ^ α i` on `𝔽₃ⁿ`. -/

lemma mcount_le (n e : ℕ) : (mcount n e : ℝ) ≤ 2 ^ e * (7 / 4) ^ n := by
  have key : (mcount n e : ℝ) * (1 / 2) ^ e ≤ (7 / 4) ^ n := by
    rw [← sum_half_pow_edeg n]
    calc (mcount n e : ℝ) * (1 / 2) ^ e = ∑ _α ∈ Dset n e, (1 / 2 : ℝ) ^ e := by
          rw [Finset.sum_const, mcount]; simp [mul_comm]
      _ ≤ ∑ α ∈ Dset n e, (1 / 2 : ℝ) ^ (edeg α) :=
          Finset.sum_le_sum fun α hα =>
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (mem_Dset.1 hα)
      _ ≤ ∑ α : Exp n, (1 / 2 : ℝ) ^ (edeg α) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
          intros; positivity
  have h2 : (0 : ℝ) < (1 / 2) ^ e := by positivity
  rw [← le_div_iff₀ h2] at key
  calc (mcount n e : ℝ) ≤ (7 / 4) ^ n / (1 / 2) ^ e := key
    _ = 2 ^ e * (7 / 4) ^ n := by
        rw [eq_comm, mul_comm, eq_div_iff (ne_of_gt h2), mul_assoc, ← mul_pow]
        norm_num

/-! ### Asymptotics -/

/-- The base `2^(2/3) * 7/4 ≈ 2.7756 < 3` of the exponential bound we obtain. -/
