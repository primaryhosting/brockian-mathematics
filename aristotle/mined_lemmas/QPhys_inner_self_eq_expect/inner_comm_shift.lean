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

lemma inner_comm_shift {X P : H →ₗ[ℂ] H}
    (hX : ∀ u v : H, inner ℂ (X u) v = inner ℂ u (X v))
    (hP : ∀ u v : H, inner ℂ (P u) v = inner ℂ u (P v))
    (psi : H) (a b : ℝ) :
    inner ℂ (X psi - (a : ℂ) • psi) (P psi - (b : ℂ) • psi)
      - inner ℂ (P psi - (b : ℂ) • psi) (X psi - (a : ℂ) • psi)
      = inner ℂ psi (X (P psi) - P (X psi)) := by
  have hXs : inner ℂ (X psi) psi = inner ℂ psi (X psi) := hX psi psi
  have hPs : inner ℂ (P psi) psi = inner ℂ psi (P psi) := hP psi psi
  have hXP : inner ℂ (X psi) (P psi) = inner ℂ psi (X (P psi)) := hX psi (P psi)
  have hPX : inner ℂ (P psi) (X psi) = inner ℂ psi (P (X psi)) := hP psi (X psi)
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  rw [hXs, hPs, hXP, hPX]
  ring

/-- **Heisenberg uncertainty principle.**

Let `X` and `P` be symmetric (self-adjoint) operators on a complex inner product space
satisfying the canonical commutation relation `[X, P] psi = i ℏ psi` on a normalized
state `psi`.  Then the product of the spreads of `X` and `P` in the state `psi` is at
least `ℏ / 2`. -/
