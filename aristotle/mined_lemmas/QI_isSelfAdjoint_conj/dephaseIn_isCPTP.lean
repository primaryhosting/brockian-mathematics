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

theorem dephaseIn_isCPTP (u : unitary (Matrix n n ℂ)) : IsCPTP (dephaseIn (n := n) u) := by
  obtain ⟨ι, hι, K, hsum, hrep⟩ := dephase_isCPTP (n := n)
  have hsu : (u : Matrix n n ℂ) * star (u : Matrix n n ℂ) = 1 := Unitary.coe_mul_star_self u
  refine ⟨ι, hι, fun a => (u : Matrix n n ℂ) * K a * star (u : Matrix n n ℂ), ?_, ?_⟩
  · have key : ∀ a, ((u : Matrix n n ℂ) * K a * star (u : Matrix n n ℂ))ᴴ
        * ((u : Matrix n n ℂ) * K a * star (u : Matrix n n ℂ))
        = (u : Matrix n n ℂ) * ((K a)ᴴ * K a) * star (u : Matrix n n ℂ) := by
      intro a
      rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, star_conj,
        conj_mul_conj]
    calc ∑ a, ((u : Matrix n n ℂ) * K a * star (u : Matrix n n ℂ))ᴴ
            * ((u : Matrix n n ℂ) * K a * star (u : Matrix n n ℂ))
        = ∑ a, (u : Matrix n n ℂ) * ((K a)ᴴ * K a) * star (u : Matrix n n ℂ) :=
          Finset.sum_congr rfl fun a _ => key a
      _ = (u : Matrix n n ℂ) * (∑ a, (K a)ᴴ * K a) * star (u : Matrix n n ℂ) := by
          rw [Finset.mul_sum, Finset.sum_mul]
      _ = 1 := by rw [hsum, mul_one, hsu]
  · intro X
    have key : ∀ a, ((u : Matrix n n ℂ) * K a * star (u : Matrix n n ℂ)) * X
          * ((u : Matrix n n ℂ) * K a * star (u : Matrix n n ℂ))ᴴ
        = (u : Matrix n n ℂ)
            * (K a * (star (u : Matrix n n ℂ) * X * (u : Matrix n n ℂ)) * (K a)ᴴ)
            * star (u : Matrix n n ℂ) := by
      intro a
      rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, star_conj]
      conv_lhs => rw [← conj_star_conj_cancel u X]
      rw [conj_mul_conj, conj_mul_conj]
    rw [dephaseIn, hrep (star (u : Matrix n n ℂ) * X * (u : Matrix n n ℂ)), Finset.mul_sum,
      Finset.sum_mul]
    exact (Finset.sum_congr rfl fun a _ => key a).symm

/-- **Data processing for a measurement channel in an arbitrary orthonormal basis**: if the
faithful state `σ` is diagonal in the measurement basis, then measuring cannot increase the
relative entropy. -/
