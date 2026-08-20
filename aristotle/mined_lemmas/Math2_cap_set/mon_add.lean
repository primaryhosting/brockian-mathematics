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

lemma mon_add {n : ℕ} (a : E n) (x y : V n) :
    mon a (x + y) = ∑ b : E n,
      (∏ i, (((a i : ℕ).choose (b i : ℕ) : ℕ) : F)) * (mon b x * mon (asub a b) y) := by
  simp only [mon]
  have h1 : ∀ i : Fin n, ((x + y) i) ^ (a i : ℕ) = ∑ j : Fin 3,
      (((a i : ℕ).choose (j : ℕ) : ℕ) : F) * ((x i) ^ (j : ℕ) * (y i) ^ ((a i : ℕ) - (j : ℕ))) := by
    intro i; simpa using binom_expand (a i) (x i) (y i)
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rfl

/-- Functions of two variables of the shape `∑_{deg b ≤ e} mon b (x) w b (y) +
∑_{deg c ≤ e} w' c (x) mon c (y)`: these have "rank" at most `2 * |M n e|`. -/
