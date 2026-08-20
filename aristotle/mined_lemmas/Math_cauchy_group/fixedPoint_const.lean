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

lemma fixedPoint_const {n : ℕ} (v : ProdOne G (n + 1))
    (hv : v ∈ fixedPoints (Multiplicative (ZMod (n + 1))) (ProdOne G (n + 1))) (i : Fin (n + 1)) :
    v.1 i = v.1 0 := by
  have hk := hv (Multiplicative.ofAdd ((i.val : ℕ) : ZMod (n + 1)))
  have hk' := congrArg (fun w => (Subtype.val w) (0 : Fin (n + 1))) hk
  simp only [smul_prodOne_coe, shiftFun] at hk'
  have hval : ((i.val : ℕ) : ZMod (n + 1)).val = i.val := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt i.isLt
  rw [show (Multiplicative.ofAdd ((i.val : ℕ) : ZMod (n + 1))).toAdd
      = ((i.val : ℕ) : ZMod (n + 1)) from rfl, hval] at hk'
  simpa [Nat.mod_eq_of_lt i.isLt] using hk'

