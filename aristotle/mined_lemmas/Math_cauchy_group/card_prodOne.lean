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

lemma card_prodOne (G : Type*) [Group G] [Finite G] (n : ℕ) :
    Nat.card (ProdOne G (n + 1)) = Nat.card G ^ n := by
  rw [Nat.card_congr (prodOneEquiv G n), Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n),
    Fintype.card_fin]

/-! ### The rotation action -/

/-- Cyclic shift of a tuple by `m` places. -/
