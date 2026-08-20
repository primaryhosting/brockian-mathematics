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

theorem commutator_ann_cre : ann ∘ₗ cre - cre ∘ₗ ann = LinearMap.id := by
  refine LinearMap.ext fun v => Finsupp.ext fun k => ?_
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe,
    id_eq, Finsupp.sub_apply]
  rw [ann_cre_apply, show cre (ann v) = numOp v from rfl, numOp_apply]
  ring

/-- `N |n⟩ = n |n⟩`. -/
