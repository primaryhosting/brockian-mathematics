import Mathlib
/-!
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands of a
file, so the mandated header comment is placed immediately after the single `import Mathlib`
line; its text is reproduced verbatim.
-/

namespace QPhys

open Finset

/-- The expectation value `⟨ψ| M |ψ⟩ = ∑ i j, conj (ψ i) * M i j * ψ j` of a (matrix)
observable `M` in the state `ψ`. -/

lemma star_mulVec_apply {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (v : Fin n → ℂ) (i : Fin n) :
    star (H.mulVec v i) = ∑ k, H k i * star (v k) := by
  rw [mulVec_apply_eq, star_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [star_mul', hH.apply k i]

/-- **Ehrenfest's theorem** (finite-dimensional form).

If the state `psi : ℝ → (Fin n → ℂ)` obeys the Schrödinger equation
`i ℏ ∂ₜ ψ = H ψ`, i.e. `∂ₜ ψ = -(i/ℏ) H ψ`, with hermitian Hamiltonian `H`, and
`A : ℝ → Matrix (Fin n) (Fin n) ℂ` is a time-dependent observable with time derivative
`dA`, then the expectation value `⟨A⟩ (t) = ⟨ψ t| A t |ψ t⟩` is differentiable in `t` with

`d⟨A⟩/dt = (i/ℏ) ⟨[H, A]⟩ + ⟨∂A/∂t⟩`. -/
