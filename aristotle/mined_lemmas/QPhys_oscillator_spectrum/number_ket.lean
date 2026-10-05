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

lemma number_ket (n : ℕ) : number (ket n) = (n : ℂ) • ket n := by
  cases n with
  | zero => simp [number, annih_ket, ket]
  | succ m =>
      have h : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
      simp only [number, LinearMap.comp_apply, annih_ket, map_smul, create_ket]
      rw [smul_smul]
      simp only [Nat.add_sub_cancel]
      congr 1
      · rw [← h] at *
        push_cast
        rw [sqrt_sq_cast]
        push_cast
        ring
      · simp

/-- The canonical commutation relation `[a, a†] = 1` for the ladder operators. -/
