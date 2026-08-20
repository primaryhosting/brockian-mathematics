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

private theorem continuousWithinAt_scalarPrim {p q : ℝ} (hq : 0 < q) :
    ContinuousWithinAt (scalarPrim p q) (Set.Ici 0) 0 := by
  have h1 : ContinuousAt (fun s : ℝ => p * Real.log (s * p + q)) 0 := by
    refine continuousAt_const.mul (ContinuousAt.log ?_ ?_)
    · fun_prop
    · simpa using ne_of_gt hq
  have h2 : ContinuousAt (fun s : ℝ => p * Real.log (1 + s)) 0 := by
    refine continuousAt_const.mul (ContinuousAt.log ?_ ?_)
    · fun_prop
    · norm_num
  have h3 : ContinuousAt (fun s : ℝ => (p - q) / (1 + s)) 0 := by
    refine continuousAt_const.div ?_ ?_
    · fun_prop
    · norm_num
  exact ((h1.sub h2).add h3).continuousWithinAt

