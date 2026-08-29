import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexOrder MatrixOrder
open Matrix

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Mₙ → Mₘ`, indexed by `(n × m) × (n × m)`:
`C (i,a) (j,b) = (Φ (Eᵢⱼ)) a b`. -/

lemma sum_prod_collapse {k : Type} [Fintype k] [DecidableEq k]
    (X : Matrix (k × n) (k × n) ℂ) (r s : k) (g h : n → ℂ) :
    (∑ u : k × n, ∑ v : k × n, X u v *
      ((if r = u.1 then g u.2 else 0) * (if s = v.1 then h v.2 else 0)))
      = ∑ i, ∑ j, X (r, i) (s, j) * (g i * h j) := by
  simp [Fintype.sum_prod_type, ite_mul, mul_ite, Finset.sum_ite_eq]

end Helpers

omit [DecidableEq m] in
/-- A map with a Kraus representation has a positive semidefinite Choi matrix. -/
