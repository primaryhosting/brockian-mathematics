/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The cap-set bound: subsets of `𝔽₃ⁿ` with no three-term arithmetic progression have size
`o(3ⁿ)`.  This is the Croot–Lev–Pach / Ellenberg–Gijswijt theorem, proved here by the
polynomial method.
-/

open Finset

namespace Math2
namespace CapSet

instance factThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The field `𝔽₃`. -/
abbrev F := ZMod 3

/-- The vector space `𝔽₃ⁿ`. -/
abbrev V (n : ℕ) := Fin n → F

/-- Exponent vectors of reduced monomials: each exponent is `0`, `1` or `2`. -/
abbrev E (n : ℕ) := Fin n → Fin 3

/-- Total degree of a reduced monomial. -/

theorem capSetMax_div_tendsto :
    Tendsto (fun n : ℕ => (capSetMax n : ℝ) / 3 ^ n) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hr : Tendsto (fun n : ℕ => (27 : ℝ) * (1372 / 1728 : ℝ) ^ n) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1372 / 1728 : ℝ))
      (by norm_num) (by norm_num)
    simpa using h.const_mul (27 : ℝ)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hr) (ε ^ 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hnn : 0 ≤ (capSetMax n : ℝ) / 3 ^ n := by positivity
  have hlt : ((capSetMax n : ℝ) / 3 ^ n) ^ 3 < ε ^ 3 := by
    refine lt_of_le_of_lt (capSetMax_div_cube_le n) ?_
    have h := hN n hn
    rw [Real.dist_eq, sub_zero] at h
    calc (27 : ℝ) * (1372 / 1728 : ℝ) ^ n ≤ |(27 : ℝ) * (1372 / 1728 : ℝ) ^ n| :=
          le_abs_self _
      _ < ε ^ 3 := h
  have hfin : (capSetMax n : ℝ) / 3 ^ n < ε := by
    by_contra hge
    push_neg at hge
    exact absurd hlt (not_lt.2 (pow_le_pow_left₀ (le_of_lt hε) hge 3))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  exact hfin

end Asymptotic

end CapSet

/-- **The cap set theorem** (Croot–Lev–Pach, Ellenberg–Gijswijt): subsets of `𝔽₃ⁿ` containing no
three-term arithmetic progression have size `o(3ⁿ)`. -/
