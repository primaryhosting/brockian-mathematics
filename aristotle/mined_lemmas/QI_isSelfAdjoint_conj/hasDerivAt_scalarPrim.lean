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

private theorem hasDerivAt_scalarPrim {p q : ℝ} (hq : 0 < q) {t : ℝ} (ht : 0 < t)
    (hp : 0 < p) :
    HasDerivAt (scalarPrim p q) ((p - q) ^ 2 / ((t * p + q) * (1 + t) ^ 2)) t := by
  have hd1 : (0 : ℝ) < t * p + q := by nlinarith
  have hd2 : (0 : ℝ) < 1 + t := by linarith
  have h1 : HasDerivAt (fun s : ℝ => s * p + q) p t := by
    simpa using ((hasDerivAt_id t).mul_const p).add_const q
  have h2 : HasDerivAt (fun s : ℝ => Real.log (s * p + q)) ((t * p + q)⁻¹ * p) t := by
    simpa [Function.comp] using (Real.hasDerivAt_log (ne_of_gt hd1)).comp t h1
  have h3 : HasDerivAt (fun s : ℝ => (1 : ℝ) + s) 1 t := by
    simpa using (hasDerivAt_id t).const_add (1 : ℝ)
  have h4 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) ((1 + t)⁻¹ * 1) t := by
    simpa [Function.comp] using (Real.hasDerivAt_log (ne_of_gt hd2)).comp t h3
  have h5 : HasDerivAt (fun s : ℝ => (p - q) / (1 + s))
      ((0 * (1 + t) - (p - q) * 1) / (1 + t) ^ 2) t :=
    (hasDerivAt_const t (p - q)).div h3 (ne_of_gt hd2)
  have h6 := ((h2.const_mul p).sub (h4.const_mul p)).add h5
  convert h6 using 1
  field_simp
  ring

