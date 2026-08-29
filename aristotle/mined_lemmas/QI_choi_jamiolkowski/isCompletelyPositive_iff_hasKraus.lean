import Mathlib
/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators MatrixOrder
open Matrix ComplexOrder

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The amplification `id_k ⊗ Φ` of a linear map `Φ` between matrix algebras:
its `((a, p), (b, q))` entry is the `(p, q)` entry of `Φ` applied to the `(a, b)` block. -/

theorem isCompletelyPositive_iff_hasKraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    IsCompletelyPositive Φ ↔ HasKraus Φ :=
  ⟨fun h => hasKraus_of_choiMatrix_posSemidef (choiMatrix_posSemidef_of_cp h), cp_of_hasKraus⟩

/-! ### Sanity checks: the identity map is completely positive, the transpose map is not -/

/-- The identity map on matrices is completely positive. -/
