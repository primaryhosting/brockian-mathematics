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

theorem chi_eq {t : ℝ} (ht : 0 < t) {P Q : Matrix n n ℂ} (hP : P.PosDef) (hQ : Q.PosDef) :
    chi t hP.1 hQ.1
      = 2 * (Matrix.trace ((sylv t hP.1 hQ.1)ᴴ * (P - Q))).re
        - quadForm t P Q (sylv t hP.1 hQ.1) := by
  have h1 : (Matrix.trace ((sylv t hP.1 hQ.1)ᴴ * (P - Q))).re = chi t hP.1 hQ.1 :=
    (trace_conjT_re (P - Q) (sylv t hP.1 hQ.1)).symm
  rw [h1, quadForm_sylv ht hP hQ]
  ring

/-! ### Monotonicity of `χ_t` under CPTP maps -/

omit [DecidableEq n] in
