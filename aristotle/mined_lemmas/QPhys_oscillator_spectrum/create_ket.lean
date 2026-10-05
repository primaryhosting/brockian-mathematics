/-
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to precede every command, including module docstrings,
-- so the header above is a plain comment and is repeated as a module docstring below.)
import Mathlib

/-!
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open Finsupp

/-- The `n`-th number state `|n⟩`, realised as a basis vector of the space of
finitely supported functions `ℕ →₀ ℂ` (the algebraic Fock space). -/

lemma create_ket (n : ℕ) : create (ket n) = (Real.sqrt (n + 1) : ℂ) • ket (n + 1) := by
  simp [ket, create_single]

