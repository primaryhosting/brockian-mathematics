/-
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

variable {Ω : Type*} [Fintype Ω]

/-- The canonical partition function `Z = ∑ₓ e^{-βH(x)}` of a Hamiltonian `H`
on a finite phase space at inverse temperature `β`. -/

noncomputable def partitionFunctionOn (μ : Measure Ω) (β : ℝ) (H : Ω → ℝ) : ℝ :=
  ∫ x, Real.exp (-β * H x) ∂μ

/-- Free energy on a general phase space: `F = -(1/β) log Z`. -/
