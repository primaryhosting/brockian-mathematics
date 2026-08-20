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

lemma sum_half_pow_deg (n : ℕ) : ∑ a : E n, ((1 : ℚ) / 2) ^ (deg a) = (7 / 4) ^ n := by
  have h1 : ∀ a : E n, ((1 : ℚ) / 2) ^ (deg a) = ∏ i, ((1 : ℚ) / 2) ^ ((a i : ℕ)) := by
    intro a; rw [deg, Finset.prod_pow_eq_pow_sum]
  rw [Finset.sum_congr rfl (fun a _ => h1 a)]
  have key := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin 3)))
    (fun (_ : Fin n) (j : Fin 3) => ((1 : ℚ) / 2) ^ (j : ℕ))
  rw [Fintype.piFinset_univ] at key
  rw [← key]
  have h2 : ∀ i : Fin n, (∑ j : Fin 3, ((1 : ℚ) / 2) ^ ((j : ℕ))) = 7 / 4 := by
    intro i; rw [Fin.sum_univ_three]; norm_num
  rw [Finset.prod_congr rfl (fun i _ => h2 i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

