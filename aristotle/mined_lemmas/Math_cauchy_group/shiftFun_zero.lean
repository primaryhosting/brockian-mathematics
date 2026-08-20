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

lemma shiftFun_zero {n : ℕ} (v : Fin (n + 1) → G) : shiftFun 0 v = v := by
  funext i
  simp [shiftFun, Nat.mod_eq_of_lt i.isLt]

/-- The rotation action of the cyclic group of order `n + 1` on tuples with product one. -/
instance rotAction (G : Type*) [Group G] (n : ℕ) :
    MulAction (Multiplicative (ZMod (n + 1))) (ProdOne G (n + 1)) where
  smul k v := ⟨shiftFun (k.toAdd.val) v.1, by
    rw [ofFn_shiftFun]
    exact List.prod_rotate_eq_one_of_prod_eq_one v.2 _⟩
  one_smul v := by
    apply Subtype.ext
    show shiftFun _ v.1 = v.1
    simpa using shiftFun_zero v.1
  mul_smul a b v := by
    apply Subtype.ext
    show shiftFun _ v.1 = shiftFun _ (shiftFun _ v.1)
    rw [shiftFun_shiftFun]
    congr 1

