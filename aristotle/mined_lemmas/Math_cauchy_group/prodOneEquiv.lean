/-
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Cauchy's theorem: if a prime `p` divides the order of a finite group `G`, then `G` contains an
element of order `p`.  The proof given here is McKay's counting argument, carried out from
first principles: the cyclic group of order `p` acts by rotation on the set of `p`-tuples of
elements of `G` whose ordered product is `1`, that set has cardinality `|G| ^ (p - 1)`, and the
fixed points of the action are exactly the constant tuples `(g, …, g)` with `g ^ p = 1`.
-/

namespace Math

open MulAction

variable {G : Type*} [Group G]

/-! ### Tuples with product one -/

/-- The set of `n`-tuples of elements of `G` whose (ordered) product is `1`. -/

def prodOneEquiv (G : Type*) [Group G] (n : ℕ) : ProdOne G (n + 1) ≃ (Fin n → G) where
  toFun v := Fin.init v.1
  invFun w := ⟨Fin.snoc w ((List.ofFn w).prod⁻¹), by
    rw [prod_ofFn_split, Fin.snoc_last, Fin.init_snoc, mul_inv_cancel]⟩
  left_inv v := by
    apply Subtype.ext
    have h : (List.ofFn (Fin.init v.1)).prod⁻¹ = v.1 (Fin.last n) :=
      inv_eq_of_mul_eq_one_right (by rw [← prod_ofFn_split, v.2])
    simp only [h, Fin.snoc_init_self]
  right_inv w := by simp [Fin.init_snoc]

