/-
/-!
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (Lean 4 requires `import` commands to precede any module docstring, so the required
-- header above is reproduced verbatim inside a comment block at the top of the file.)

import Mathlib

open scoped InnerProductSpace

namespace QPhys

/-- Applying a continuous `ℂ`-linear operator to a vector is a bounded `ℝ`-bilinear map.
(The Mathlib lemma `isBoundedBilinearMap_apply` only covers the case where the scalar field
of the operators coincides with the differentiability field; here we differentiate in `ℝ`
while the operators are `ℂ`-linear.) -/

theorem hasDerivAt_operator_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {A : ℝ → (E →L[ℂ] E)} {dA : E →L[ℂ] E} {u : ℝ → E} {u' : E} {t : ℝ}
    (hA : HasDerivAt A dA t) (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => A s (u s)) (dA (u t) + A t u') t := by
  have h := (isBoundedBilinearMap_apply_real.hasFDerivAt (A t, u t)).comp_hasDerivAt t
    (hA.hasFDerivAt.prodMk hu.hasFDerivAt).hasDerivAt
  simpa [add_comm] using h

/-- **Ehrenfest's theorem.**

Let `E` be a complex inner product space (the space of states), `H : E →L[ℂ] E` a symmetric
(self-adjoint) Hamiltonian, `psi : ℝ → E` a time-dependent state obeying the Schrödinger
equation `i ℏ ψ'(t) = H ψ(t)`, and `A : ℝ → (E →L[ℂ] E)` a time-dependent observable with
time derivative `dA` at `t`. Then the expectation value `⟨A⟩(s) = ⟪ψ s, A s (ψ s)⟫` is
differentiable at `t` and

`d⟨A⟩/dt = (i/ℏ) ⟪ψ, [H, A] ψ⟫ + ⟪ψ, (∂A/∂t) ψ⟫`,

where `[H, A] = H ∘ A - A ∘ H` is the commutator. -/
