/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# The Choi–Jamiołkowski isomorphism

For a linear map `Φ` between finite-dimensional matrix algebras we prove that the following
are equivalent:

* `Φ` is completely positive (`QI.IsCP`), i.e. all amplifications `id ⊗ Φ` preserve positive
  semidefiniteness;
* the Choi matrix of `Φ` (`QI.choiMatrix`) is positive semidefinite;
* `Φ` admits a Kraus decomposition (`QI.HasKraus`).

The main statement is `QI.choi_jamiolkowski`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QI

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The amplification `id_{Fin k} ⊗ Φ` of a linear map `Φ` on matrices: it applies `Φ` to each
`m × m` block of a `(Fin k × m) × (Fin k × m)` matrix. -/

theorem hasKraus_of_choi_posSemidef {Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ}
    (h : (choiMatrix Φ).PosSemidef) : HasKraus Φ := by
  set B : Matrix (m × n) (m × n) ℂ := CFC.sqrt (choiMatrix Φ) with hB
  have hBpsd : (0 : Matrix (m × n) (m × n) ℂ) ≤ B := CFC.sqrt_nonneg _
  have hfac : choiMatrix Φ = B * Bᴴ := by
    rw [hBpsd.posSemidef.isHermitian.eq, hB, CFC.sqrt_mul_sqrt_self _ h.nonneg]
  exact ⟨krausMat B, krausMat_of_choi_eq Φ B hfac⟩

omit [DecidableEq m] [DecidableEq n] in
/-- A map with a Kraus decomposition is completely positive: the amplification of `Φ` is given
by conjugation with the amplified Kraus operators `1 ⊗ V a`. -/
