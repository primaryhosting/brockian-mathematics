/-
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Oscillator Spectrum

(Lean requires `import` commands to precede every other command, including module
documentation, so the header comment above is a plain block comment.)

We realise the one-dimensional quantum harmonic oscillator algebraically on the Fock space
`ℕ →₀ ℂ`, whose basis vector `Finsupp.single n 1` is the number state `|n⟩`.  The ladder
operators `a` (`QPhys.ann`) and `a†` (`QPhys.cre`) satisfy the canonical commutation
relation `[a, a†] = 1`, the number operator `N = a† a` acts diagonally, and the Hamiltonian
`H = ℏω (a†a + ½)` has eigenvalues exactly `ℏω(n + ½)`, `n ∈ ℕ`.
-/

namespace QPhys

/-! ## Ladder operators -/

/-- The annihilation (lowering) operator, `a |n⟩ = √n |n-1⟩`.  For `n = 0` the prefactor
`√0 = 0` vanishes, so `|0⟩` is the vacuum. -/

theorem cre_pow_vacuum (n : ℕ) :
    (cre ^ n) (Finsupp.single 0 (1 : ℂ)) = Finsupp.single n ((Real.sqrt n.factorial : ℂ)) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', show ((cre * cre ^ m) (Finsupp.single 0 (1 : ℂ)))
            = cre ((cre ^ m) (Finsupp.single 0 (1 : ℂ))) from rfl, ih, cre_single, Finsupp.smul_single, smul_eq_mul]
      congr 1
      rw [← Complex.ofReal_mul, ← Real.sqrt_mul (Nat.cast_nonneg _)]
      norm_cast
      rw [Nat.factorial_succ]
      push_cast
      rw [mul_comm]

/-- The energy eigenstates: `H |n⟩ = ℏω (n + ½) |n⟩`. -/
