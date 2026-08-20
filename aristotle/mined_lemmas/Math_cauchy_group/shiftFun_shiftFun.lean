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

lemma shiftFun_shiftFun {n : ℕ} (v : Fin (n + 1) → G) (a b : ℕ) :
    shiftFun a (shiftFun b v) = shiftFun ((a + b) % (n + 1)) v := by
  funext i
  simp only [shiftFun]
  congr 1
  ext
  simp [Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

omit [Group G] in
