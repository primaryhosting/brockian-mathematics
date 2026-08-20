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

theorem numOp_single (n : ℕ) (c : ℂ) :
    numOp (Finsupp.single n c) = (n : ℂ) • Finsupp.single n c := by
  refine Finsupp.ext fun k => ?_
  rw [numOp_apply, Finsupp.smul_apply, smul_eq_mul]
  rcases eq_or_ne n k with rfl | h
  · rfl
  · rw [Finsupp.single_apply, if_neg h]; ring

/-! ## Ladder construction of the eigenstates -/

/-- The vacuum `|0⟩` is annihilated by `a`. -/
