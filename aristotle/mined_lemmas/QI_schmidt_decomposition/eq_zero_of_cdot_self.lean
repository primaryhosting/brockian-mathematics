/-
Header (Lean requires `import` to precede any command, including a module docstring,
so the required header is reproduced verbatim as a module docstring just below the import):

# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

open Matrix

/-- The standard Hermitian inner product on `ℂ^d`, `⟪x, y⟫ = ∑ i, conj (x i) * y i`. -/

theorem eq_zero_of_cdot_self {d : ℕ} {x : Fin d → ℂ} (h : cdot x x = 0) (j : Fin d) :
    x j = 0 := by
  have hr : ((∑ j, ‖x j‖ ^ 2 : ℝ) : ℂ) = 0 := by
    rw [← h, cdot]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (starRingEnd ℂ) (x i) * x i = ((‖x i‖ ^ 2 : ℝ) : ℂ) by
      rw [mul_comm, Complex.mul_conj]
      norm_cast
      exact Complex.normSq_eq_norm_sq (x i)]
    push_cast
    ring
  have hr' : (∑ j, ‖x j‖ ^ 2 : ℝ) = 0 := by exact_mod_cast hr
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 hr' j
    (Finset.mem_univ j)
  simpa using hj

/-- For `t > 0` the `t ^ 2`-eigenspace of the reduced density matrix is spanned by the
Schmidt vectors whose Schmidt coefficient is `t`. -/
