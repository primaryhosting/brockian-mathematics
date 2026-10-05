import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- `nu H p` is the number of distinct residue classes modulo `p` occupied by the
tuple `H`; in the Hardy–Littlewood singular series this is the quantity `ν_p(H)`
appearing in the local factor `(1 - ν_p(H)/p)(1 - 1/p)^{-|H|}`. -/

lemma nu_pair (d p : ℕ) : nu ({0, d} : Finset ℕ) p = ({0, d % p} : Finset ℕ).card := by
  simp [nu, Finset.image_insert, Nat.zero_mod]

/-- **Admissible gaps are exactly the even ones.**  The pair `{0, d}` is an
admissible `2`-tuple (equivalently, the singular series `𝔖(0, d)` is nonzero)
if and only if `d` is even. -/
