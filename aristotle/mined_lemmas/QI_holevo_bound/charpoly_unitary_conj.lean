/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix Finset ComplexOrder

/-! ## Classical information quantities -/

variable {ι X I Y : Type*}

/-- Shannon entropy of a finite (sub)probability vector, `H(p) = -∑ p i log (p i)`. -/

lemma charpoly_unitary_conj {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (A : Matrix n n ℂ) : (U * A * star U).charpoly = A.charpoly := by
  rw [mul_assoc, Matrix.charpoly_mul_comm, mul_assoc, Matrix.mem_unitaryGroup_iff'.1 hU, mul_one]

/-- A unitary conjugate of a real diagonal matrix is Hermitian. -/
