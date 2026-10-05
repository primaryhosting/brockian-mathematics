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

lemma choiMatrix_posSemidef_of_cp {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (h : IsCompletelyPositive Φ) : (choiMatrix Φ).PosSemidef := by
  have hn := h n (maxEnt n) maxEnt_posSemidef
  rwa [ampl_maxEnt_eq_choiMatrix] at hn

/-- If the Choi matrix of `Φ` is positive semidefinite, then `Φ` has a Kraus decomposition. -/
