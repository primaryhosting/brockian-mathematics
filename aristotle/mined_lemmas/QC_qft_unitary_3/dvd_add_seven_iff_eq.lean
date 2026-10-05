import Mathlib
/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix

/-- The primitive `8`-th root of unity `ω = exp(2πi/8)` used by the 3-qubit QFT. -/

lemma dvd_add_seven_iff_eq : ∀ j l : Fin 8, 8 ∣ ((j : ℕ) + 7 * (l : ℕ)) ↔ j = l := by decide

/-- The 3-qubit quantum Fourier transform matrix is unitary. -/
