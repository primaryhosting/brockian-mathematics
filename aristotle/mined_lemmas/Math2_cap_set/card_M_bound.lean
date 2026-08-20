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

lemma card_M_bound (n d : ℕ) : ((M n d).card : ℚ) * ((1 : ℚ) / 2) ^ d ≤ (7 / 4) ^ n := by
  rw [← sum_half_pow_deg n]
  calc ((M n d).card : ℚ) * ((1 : ℚ) / 2) ^ d = ∑ _a ∈ M n d, ((1 : ℚ) / 2) ^ d := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ M n d, ((1 : ℚ) / 2) ^ (deg a) := by
        refine Finset.sum_le_sum (fun a ha => ?_)
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) ((mem_M_iff a).1 ha)
    _ ≤ ∑ a : E n, ((1 : ℚ) / 2) ^ (deg a) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
        intro i _ _; positivity

/-- The number of exponent vectors of degree at most `2n/3` is exponentially smaller than `3ⁿ`:
`m³ · 64ⁿ ≤ 1372ⁿ`, and `1372 < 64 · 27`. -/
