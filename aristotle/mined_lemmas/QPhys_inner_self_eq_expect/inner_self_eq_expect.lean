/- (header comment; Lean requires `import` to be the first command, so the header
   below is a plain block comment rather than a module docstring)
/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

namespace QPhys

open scoped ComplexInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Expectation value of a (symmetric) operator `A` in the state `psi`. -/

lemma inner_self_eq_expect {A : H →ₗ[ℂ] H} (hA : ∀ u v : H, inner ℂ (A u) v = inner ℂ u (A v))
    (psi : H) : inner ℂ psi (A psi) = ((expect A psi : ℝ) : ℂ) := by
  have h : (starRingEnd ℂ) (inner ℂ psi (A psi)) = inner ℂ psi (A psi) :=
    (inner_conj_symm (A psi) psi).trans (hA psi psi)
  have him := Complex.conj_eq_iff_im.mp h
  exact Complex.ext (by simp [expect]) (by simp [expect, him])

/-- The commutator of the shifted operators equals the commutator of the original operators,
paired against `psi`. -/
