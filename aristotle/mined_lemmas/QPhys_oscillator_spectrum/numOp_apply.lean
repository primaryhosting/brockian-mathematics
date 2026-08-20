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

theorem numOp_apply (v : ℕ →₀ ℂ) (n : ℕ) : (numOp v) n = (n : ℂ) * v n := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]; ring
  | single a b =>
      rw [numOp, LinearMap.comp_apply, ann_single, map_smul, cre_single]
      rcases a with _ | m
      · simp only [Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero, Finsupp.single_apply]
        push_cast
        split_ifs with h <;> simp [h]
      · simp only [Nat.add_sub_cancel, Finsupp.smul_single, Finsupp.single_apply, smul_eq_mul]
        split_ifs with h
        · subst h
          push_cast
          linear_combination b * sqrt_mul_sqrt_succ m
        · ring

/-- `a a†` is diagonal in the number basis: `(a a† v) n = (n+1) * v n`. -/
