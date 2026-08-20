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

theorem relEntropy_ge_trace_sub (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    ρ.trace.re - σ.trace.re ≤ relEntropy ρ σ := by
  have hρh := hρ.isHermitian
  have hσh := hσ.isHermitian
  have hl : ∀ j, 0 < hρh.eigenvalues j := fun j => hρ.eigenvalues_pos j
  have hm : ∀ k, 0 < hσh.eigenvalues k := fun k => hσ.eigenvalues_pos k
  rw [relEntropy_eq_sum hρh hσh]
  have key : ∀ j k, transition hρh hσh j k * (hρh.eigenvalues j - hσh.eigenvalues k)
      ≤ transition hρh hσh j k * (hρh.eigenvalues j * Real.log (hρh.eigenvalues j) -
          hρh.eigenvalues j * Real.log (hσh.eigenvalues k)) := by
    intro j k
    refine mul_le_mul_of_nonneg_left ?_ (transition_nonneg hρh hσh j k)
    have hlog := Real.log_le_sub_one_of_pos (div_pos (hm k) (hl j))
    rw [Real.log_div (hm k).ne' (hl j).ne'] at hlog
    have h2 := mul_le_mul_of_nonneg_left hlog (le_of_lt (hl j))
    have h3 : hρh.eigenvalues j * (hσh.eigenvalues k / hρh.eigenvalues j - 1)
        = hσh.eigenvalues k - hρh.eigenvalues j := by
      have hne : hρh.eigenvalues j ≠ 0 := (hl j).ne'
      field_simp
    have h4 : hρh.eigenvalues j *
          (Real.log (hσh.eigenvalues k) - Real.log (hρh.eigenvalues j))
        = hρh.eigenvalues j * Real.log (hσh.eigenvalues k)
          - hρh.eigenvalues j * Real.log (hρh.eigenvalues j) := by ring
    linarith
  calc ρ.trace.re - σ.trace.re
      = ∑ j, ∑ k, transition hρh hσh j k * (hρh.eigenvalues j - hσh.eigenvalues k) := by
        have e1 : ∑ j, ∑ k, transition hρh hσh j k * hρh.eigenvalues j
            = ∑ j, hρh.eigenvalues j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_mul, sum_transition_right hρh hσh, one_mul]
        have e2 : ∑ j, ∑ k, transition hρh hσh j k * hσh.eigenvalues k
            = ∑ k, hσh.eigenvalues k := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.sum_mul, sum_transition_left hρh hσh, one_mul]
        rw [trace_eq_sum_eigenvalues hρh, trace_eq_sum_eigenvalues hσh, Complex.ofReal_re,
          Complex.ofReal_re, ← e1, ← e2, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ ≤ _ := Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => key j k

/-- Klein's inequality: the relative entropy of two states with the same trace is
nonnegative. -/
