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

theorem hamiltonian_eigenstate (hbar omega : ℝ) (n : ℕ) (c : ℂ) :
    hamiltonian hbar omega (Finsupp.single n c)
      = (((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2)) • Finsupp.single n c := by
  rw [hamiltonian]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_coe, id_eq, numOp_single,
    LinearMap.smul_apply]
  rw [← add_smul, smul_smul]

/-! ## The spectrum -/

/-- **Spectrum of the quantum harmonic oscillator.**
A complex number `lam` is an eigenvalue of the harmonic-oscillator Hamiltonian
`H = ℏω (a†a + ½)` on the Fock space `ℕ →₀ ℂ` if and only if `lam = ℏω (n + ½)` for some
natural number `n`; that is, the spectrum is exactly `{ℏω(n + ½) : n ∈ ℕ}`.  The eigenvector
for the level `n` is the ladder-operator state `(a†)^n |0⟩` (see `QPhys.cre_pow_vacuum`). -/
