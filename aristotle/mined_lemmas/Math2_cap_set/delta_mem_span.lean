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

lemma delta_mem_span {n : ℕ} (c : V n) :
    (fun x => if x = c then (1 : F) else 0) ∈ Submodule.span F (Set.range (mon (n := n))) := by
  have key : (fun x : V n => if x = c then (1 : F) else 0)
      = ∑ a : E n, (∏ i, (if (a i : ℕ) = 0 then 1 - (c i) ^ 2
          else if (a i : ℕ) = 1 then 2 * (c i) else -1)) • mon a := by
    funext x
    rw [← delta_prod c x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mon]
    have h1 : ∀ i : Fin n, (1 - (x i - c i) ^ 2) = ∑ j : Fin 3,
        (if (j : ℕ) = 0 then 1 - (c i) ^ 2 else if (j : ℕ) = 1 then 2 * (c i) else -1)
          * (x i) ^ (j : ℕ) := fun i => quad_expand (c i) (x i)
    rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_univ_sum, Fintype.piFinset_univ]
    exact Finset.sum_congr rfl (fun a _ => Finset.prod_mul_distrib)
  rw [key]
  exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

