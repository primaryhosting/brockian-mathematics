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

lemma eventually_le_eps {f : ℕ → ℝ} (H : ∀ n : ℕ, 1 ≤ n → f n ≤ 3 * cbase ^ n)
    {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f n ≤ ε * 3 ^ n := by
  have hq : |cbase / 3| < 1 := by
    rw [abs_of_nonneg (div_nonneg cbase_nonneg (by norm_num))]
    linarith [cbase_lt_three]
  have hlim : Filter.Tendsto (fun n : ℕ => 3 * (cbase / 3) ^ n) Filter.atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq
    simpa using h.const_mul (3 : ℝ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlim.eventually_le_const hε)
  refine ⟨max N 1, fun n hn => ?_⟩
  have h1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have h2 : N ≤ n := le_trans (le_max_left N 1) hn
  have key : 3 * cbase ^ n = (3 * (cbase / 3) ^ n) * 3 ^ n := by
    rw [div_pow]; field_simp
  calc f n ≤ 3 * cbase ^ n := H n h1
    _ = (3 * (cbase / 3) ^ n) * 3 ^ n := key
    _ ≤ ε * 3 ^ n := mul_le_mul_of_nonneg_right (hN n h2) (by positivity)

/-- A sanity check: the four-element cap in `𝔽₃²`, showing the hypothesis is satisfiable. -/
example : ThreeAPFree (({![0, 0], ![0, 1], ![1, 0], ![1, 1]} : Finset (Pt 2)) : Set (Pt 2)) := by
  decide

end CapSet

namespace Math2

/-- **Cap set theorem** (Croot–Lev–Pach, Ellenberg–Gijswijt): subsets of `𝔽₃ⁿ` containing no
non-trivial three-term arithmetic progression have size `o(3ⁿ)`. -/
