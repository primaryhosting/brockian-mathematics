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

theorem data_processing {Φ : Matrix n n ℂ → Matrix m m ℂ} (hΦ : IsCPTP Φ)
    {ρ σ : Matrix n n ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hΦρ : IsDensity (Φ ρ)) (hΦσ : IsDensity (Φ σ)) :
    relEntropy (Φ ρ) (Φ σ) ≤ relEntropy ρ σ := by
  obtain ⟨ι, hι, K, hK, hrep⟩ := hΦ
  have hr : Φ ρ = krausMap K ρ := hrep ρ
  have hs : Φ σ = krausMap K σ := hrep σ
  have hKρ : (krausMap K ρ).PosDef := hr ▸ hΦρ.1
  have hKσ : (krausMap K σ).PosDef := hs ▸ hΦσ.1
  have hdenρ : IsDensity (krausMap K ρ) := ⟨hKρ, hr ▸ hΦρ.2⟩
  have hdenσ : IsDensity (krausMap K σ) := ⟨hKσ, hs ▸ hΦσ.2⟩
  rw [hr, hs, relEntropy_eq_integral hdenρ hdenσ, relEntropy_eq_integral hρ hσ]
  refine setIntegral_mono_on (integrableOn_chi hdenρ.1 hdenσ.1) (integrableOn_chi hρ.1 hσ.1)
    measurableSet_Ioi fun t ht => ?_
  have htpos : (0 : ℝ) < t := ht
  have hmono := chi_monotone htpos hK hρ.1 hσ.1 hKρ hKσ
  have hden : (0 : ℝ) < (1 + t) ^ 2 := by positivity
  gcongr

end QI

