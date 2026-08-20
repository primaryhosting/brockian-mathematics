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

private theorem sum_comm3 {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ]
    (f : ι → κ → σ → ℂ) : ∑ i, ∑ j, ∑ a, f i j a = ∑ a, ∑ i, ∑ j, f i j a :=
  calc ∑ i, ∑ j, ∑ a, f i j a
      = ∑ i, ∑ a, ∑ j, f i j a := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, f i j a := Finset.sum_comm

omit [Fintype n] [DecidableEq n] in
