/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The expectation value `⟨A⟩ (t) = ⟪ψ t, A t (ψ t)⟫` of a (possibly time-dependent)
observable `A` in the state `ψ t`. -/

theorem ehrenfest_hasDerivAt
    (hbar : ℝ) (H : E →L[ℂ] E)
    (hH : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y))
    (psi : ℝ → E) (A A' : ℝ → (E →L[ℂ] E)) (t : ℝ)
    (hpsi : HasDerivAt psi ((-Complex.I / (hbar : ℂ)) • H (psi t)) t)
    (hA : HasDerivAt A (A' t) t) :
    HasDerivAt (expVal psi A)
      ((Complex.I / (hbar : ℂ)) * inner ℂ (psi t) (commutator H (A t) (psi t))
        + inner ℂ (psi t) (A' t (psi t))) t := by
  have hAR : HasDerivAt (fun s => (A s).restrictScalars ℝ) ((A' t).restrictScalars ℝ) t :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hA
  have hf : HasDerivAt (fun s => A s (psi s))
      ((A' t) (psi t) + (A t) ((-Complex.I / (hbar : ℂ)) • H (psi t))) t := hAR.clm_apply hpsi
  have h := hpsi.inner ℂ hf
  convert h using 1
  simp [commutator, inner_add_right, inner_smul_right, inner_smul_left,
    ContinuousLinearMap.coe_sub', hH]
  ring

/-- **Ehrenfest theorem**: `d⟨A⟩/dt = (i/ℏ)⟪ψ, [H, A]ψ⟫ + ⟪ψ, (∂A/∂t)ψ⟫`,
for a state `ψ` evolving by the Schrödinger equation `iℏ ψ' = H ψ` with symmetric
Hamiltonian `H`, and a time-dependent observable `A` with time derivative `A'`. -/
