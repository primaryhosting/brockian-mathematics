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

lemma fixedPoint_pow {n : ℕ} (v : ProdOne G (n + 1))
    (hv : v ∈ fixedPoints (Multiplicative (ZMod (n + 1))) (ProdOne G (n + 1))) :
    (v.1 0) ^ (n + 1) = 1 := by
  have h : List.ofFn v.1 = List.replicate (n + 1) (v.1 0) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.length_ofFn] at h1
      rw [List.getElem_ofFn, List.getElem_replicate]
      exact fixedPoint_const v hv _
  have := v.2
  rw [h, List.prod_replicate] at this
  exact this

/-! ### Cauchy's theorem -/

/-- **Cauchy's theorem**: if a prime `p` divides the order of a finite group `G`, then `G` has an
element of order `p`. -/
