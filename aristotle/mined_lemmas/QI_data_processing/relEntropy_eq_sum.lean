import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Data Processing
Category: Frontier Qi
Target: QI.data_processing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Data Processing

Category: Frontier Qi.  Target: `QI.data_processing`.

(The header above is repeated as a plain comment at the top of the file, since Lean does not
allow a module docstring to precede the `import` commands.)

## Quantum relative entropy and the data-processing inequality

We work with finite-dimensional quantum systems, i.e. complex matrices indexed by a finite
type `n`, and we use the Umegaki relative entropy
`D(ρ‖σ) = Tr[ρ (log ρ - log σ)]`,
where the matrix logarithm is the one provided by the continuous functional calculus.
-/

namespace QI

open Matrix Unitary
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix logarithm, defined through the continuous functional calculus. -/

lemma relEntropy_eq_sum (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    relEntropy ρ σ = ∑ j, ∑ k, transition hρ hσ j k *
      (hρ.eigenvalues j * Real.log (hρ.eigenvalues j) -
        hρ.eigenvalues j * Real.log (hσ.eigenvalues k)) := by
  have hsplit : (ρ * (logm ρ - logm σ)).trace = (ρ * logm ρ).trace - (ρ * logm σ).trace := by
    rw [mul_sub, Matrix.trace_sub]
  rw [relEntropy, hsplit, trace_mul_logm_self hρ, trace_mul_logm hρ hσ]
  rw [← Complex.ofReal_sub, Complex.ofReal_re]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∑ k, transition hρ hσ j k * (hρ.eigenvalues j * Real.log (hρ.eigenvalues j) -
        hρ.eigenvalues j * Real.log (hσ.eigenvalues k))
      = (∑ k, transition hρ hσ j k) * (hρ.eigenvalues j * Real.log (hρ.eigenvalues j))
        - ∑ k, hρ.eigenvalues j * Real.log (hσ.eigenvalues k) * transition hρ hσ j k := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h1, sum_transition_right hρ hσ, one_mul]

/-- Klein's inequality: `D(ρ‖σ) ≥ Tr ρ - Tr σ` for positive definite `ρ`, `σ`. -/
