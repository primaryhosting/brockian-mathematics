/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a plain comment on the first lines of the file, because
Lean 4 does not permit a module docstring to precede the `import` commands.)

## Contents

* `QPhys.heisenberg_uncertainty`: for a normalized state `ψ` of a complex inner product
  space and symmetric operators `X`, `P` satisfying the canonical commutation relation
  `[X, P] ψ = i ℏ ψ`, the standard deviations satisfy `Δx · Δp ≥ ℏ / 2`.
  The proof is the classical one: the commutator identity computes
  `⟪u, v⟫ - ⟪v, u⟫ = i ℏ` for the centred vectors `u = (X - ⟨X⟩)ψ`, `v = (P - ⟨P⟩)ψ`,
  and Cauchy–Schwarz bounds each inner product by `‖u‖ ‖v‖ = Δx · Δp`.
* `QPhys.heisenberg_uncertainty_sharp`: the hypotheses are satisfiable and the bound is
  attained, for every `ℏ ≥ 0`.
-/

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Expectation values of a symmetric operator in a state are real. -/

lemma inner_comm_diff (X P : E →ₗ[ℂ] E) (hbar : ℝ) (psi : E) (hpsi : ‖psi‖ = 1)
    (hX : ∀ u v : E, inner ℂ (X u) v = inner ℂ u (X v))
    (hP : ∀ u v : E, inner ℂ (P u) v = inner ℂ u (P v))
    (hcomm : X (P psi) - P (X psi) = (Complex.I * (hbar : ℂ)) • psi) :
    inner ℂ (X psi - (inner ℂ psi (X psi) : ℂ) • psi)
        (P psi - (inner ℂ psi (P psi) : ℂ) • psi)
      - inner ℂ (P psi - (inner ℂ psi (P psi) : ℂ) • psi)
        (X psi - (inner ℂ psi (X psi) : ℂ) • psi)
      = Complex.I * (hbar : ℂ) := by
  have hnorm : (inner ℂ psi psi : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]
    norm_num
  set a : ℂ := inner ℂ psi (X psi) with ha
  set b : ℂ := inner ℂ psi (P psi) with hb
  have hac : (starRingEnd ℂ) a = a := expectation_real X hX psi
  have hbc : (starRingEnd ℂ) b = b := expectation_real P hP psi
  have hXpsi : (inner ℂ (X psi) psi : ℂ) = a := by rw [ha, hX]
  have hPpsi : (inner ℂ (P psi) psi : ℂ) = b := by rw [hb, hP]
  have key : (inner ℂ (X psi) (P psi) : ℂ) - inner ℂ (P psi) (X psi)
      = Complex.I * (hbar : ℂ) := by
    have h1 : (inner ℂ (X psi) (P psi) : ℂ) = inner ℂ psi (X (P psi)) := by
      rw [hX]
    have h2 : (inner ℂ (P psi) (X psi) : ℂ) = inner ℂ psi (P (X psi)) := by
      rw [hP]
    rw [h1, h2, ← inner_sub_right, hcomm, inner_smul_right, hnorm, mul_one]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hnorm, hXpsi, hPpsi, hac, hbc, mul_one]
  rw [← key]
  ring

/-- **Heisenberg uncertainty principle** (Robertson form for the canonical commutator).

Let `ψ` be a normalized state of a complex inner product space and let `X`, `P` be
symmetric (formally self-adjoint) operators obeying the canonical commutation relation
`X (P ψ) - P (X ψ) = i ℏ ψ`. If `Δx` and `Δp` denote the standard deviations of `X` and
`P` in the state `ψ`, i.e. the norms of the centred vectors `(X - ⟨X⟩)ψ` and `(P - ⟨P⟩)ψ`,
then `Δx · Δp ≥ ℏ / 2`. -/
