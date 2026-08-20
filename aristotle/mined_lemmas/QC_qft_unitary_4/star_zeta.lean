/-
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# The quantum Fourier transform is unitary

We define the `n`-point discrete/quantum Fourier transform matrix

`qftMatrix n = (1/√n) * (ω^(j*k))_{j,k}` with `ω = exp (2πi/n)`,

prove it is unitary for every `n ≠ 0`, and specialize to the 4-qubit case `n = 2^4 = 16`,
giving the target theorem `QC.qft_unitary_4`.
-/

namespace QC

open Complex Matrix Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma star_zeta (n : ℕ) [NeZero n] : star (zeta n) = (zeta n)⁻¹ :=
  (Complex.inv_eq_conj (zeta_norm n)).symm

/-- The geometric sum `∑_{k<n} (ζₙ^d)^k` vanishes whenever `n ∤ d`. -/
