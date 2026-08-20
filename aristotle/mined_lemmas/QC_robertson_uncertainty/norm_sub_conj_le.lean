import Mathlib
/-!
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command in a file
-- (a `/-! ... -/` module docstring is a command), so the required header comment
-- appears immediately after the single `import Mathlib` line.

open scoped ComplexConjugate

namespace QC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => (inner ℂ x y : ℂ)

/-- The expectation value `⟨A⟩_ψ = ⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`
(a real number when `A` is self-adjoint and `ψ` is a unit vector). -/

theorem norm_sub_conj_le (z : ℂ) : ‖z - conj z‖ ≤ 2 * ‖z‖ := by
  have hz : z - conj z = (2 * Complex.I) * ((z.im : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp
      ring
  rw [hz, norm_mul, norm_mul, Complex.norm_I]
  simpa using Complex.abs_im_le_norm z

/-- **Robertson uncertainty relation**: for observables (self-adjoint operators) `A`, `B`
and a unit state vector `ψ`, `ΔA · ΔB ≥ ½ |⟨[A, B]⟩|`. -/
