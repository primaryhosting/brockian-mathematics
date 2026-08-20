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

private theorem tendsto_scalarPrim {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Tendsto (scalarPrim p q) atTop (𝓝 (p * Real.log p)) := by
  have hlim0 : Tendsto (fun s : ℝ => (q - p) / (1 + s)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds (tendsto_atTop_add_const_left _ 1 tendsto_id)
  have hlim0' : Tendsto (fun s : ℝ => (p - q) / (1 + s)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds (tendsto_atTop_add_const_left _ 1 tendsto_id)
  have hlim1 : Tendsto (fun s : ℝ => p + (q - p) / (1 + s)) atTop (𝓝 p) := by
    simpa using tendsto_const_nhds.add hlim0
  have hlim2 : Tendsto (fun s : ℝ => Real.log (p + (q - p) / (1 + s))) atTop (𝓝 (Real.log p)) :=
    (Real.continuousAt_log (ne_of_gt hp)).tendsto.comp hlim1
  have hlim3 : Tendsto (fun s : ℝ => p * Real.log (p + (q - p) / (1 + s)) + (p - q) / (1 + s))
      atTop (𝓝 (p * Real.log p)) := by
    simpa using (hlim2.const_mul p).add hlim0'
  refine hlim3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  have hd1 : (0 : ℝ) < s * p + q := by nlinarith
  have hd2 : (0 : ℝ) < 1 + s := by linarith
  have heq : p + (q - p) / (1 + s) = (s * p + q) / (1 + s) := by
    field_simp
    ring
  rw [scalarPrim, heq, Real.log_div (ne_of_gt hd1) (ne_of_gt hd2)]
  ring

