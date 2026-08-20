import Mathlib

/-!
# Quantum relative entropy and data processing

This file develops, for finite-dimensional systems (complex matrices), the basic theory of the
Umegaki quantum relative entropy

`D(ρ‖σ) = Tr(ρ log ρ) - Tr(ρ log σ)`

for faithful (positive definite) density matrices, together with

* Klein's inequality `QI.relEntropy_nonneg` : `0 ≤ D(ρ‖σ)`;
* invariance under unitary channels `QI.relEntropy_unitary_conj`;
* the data-processing inequality `QI.data_processing_condExp` for trace-self-adjoint maps fixing `σ`
  (conditional expectations), and its concrete instance for the completely dephasing channel
  `QI.data_processing_dephasing`.
-/

open Matrix
open scoped ComplexOrder

namespace QI

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The logarithm of a (Hermitian) matrix, defined through the continuous functional calculus. -/

theorem data_processing_dephaseIn (u : unitary (Matrix n n ℂ)) {ρ σ : Matrix n n ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (hfix : dephaseIn u σ = σ) :
    relEntropy (dephaseIn u ρ) (dephaseIn u σ) ≤ relEntropy ρ σ := by
  have hstar : ((star u : unitary (Matrix n n ℂ)) : Matrix n n ℂ)
      = star (u : Matrix n n ℂ) := rfl
  have hρ' : IsDensity (star (u : Matrix n n ℂ) * ρ * (u : Matrix n n ℂ)) := by
    have := isDensity_conj (star u) hρ
    rwa [hstar, star_star] at this
  have hσ' : IsDensity (star (u : Matrix n n ℂ) * σ * (u : Matrix n n ℂ)) := by
    have := isDensity_conj (star u) hσ
    rwa [hstar, star_star] at this
  have hfix' : dephase (star (u : Matrix n n ℂ) * σ * (u : Matrix n n ℂ))
      = star (u : Matrix n n ℂ) * σ * (u : Matrix n n ℂ) := by
    conv_rhs => rw [← hfix]
    rw [dephaseIn, conj_conj_star_cancel]
  have hdρ : IsDensity (dephase (star (u : Matrix n n ℂ) * ρ * (u : Matrix n n ℂ))) :=
    isDensity_dephase hρ'
  have hdσ : IsDensity (dephase (star (u : Matrix n n ℂ) * σ * (u : Matrix n n ℂ))) :=
    isDensity_dephase hσ'
  calc relEntropy (dephaseIn u ρ) (dephaseIn u σ)
      = relEntropy (dephase (star (u : Matrix n n ℂ) * ρ * (u : Matrix n n ℂ)))
          (dephase (star (u : Matrix n n ℂ) * σ * (u : Matrix n n ℂ))) := by
        rw [dephaseIn, dephaseIn, relEntropy_unitary_conj u hdρ.1.1 hdσ.1.1]
    _ ≤ relEntropy (star (u : Matrix n n ℂ) * ρ * (u : Matrix n n ℂ))
          (star (u : Matrix n n ℂ) * σ * (u : Matrix n n ℂ)) :=
        data_processing_dephasing hρ' hσ' hfix'
    _ = relEntropy ρ σ := by
        have := relEntropy_unitary_conj (star u) hρ.1.1 hσ.1.1
        rwa [hstar, star_star] at this

/-- A state which is diagonal in the measurement basis is left unchanged by the measurement. -/
