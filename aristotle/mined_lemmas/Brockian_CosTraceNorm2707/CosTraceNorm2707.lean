import Mathlib

/-!
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

namespace Brockian

/-- The cosine Gram matrix `C θ i j = cos (θ i - θ j)`. -/

theorem CosTraceNorm2707 {n : ℕ} (θ : Fin n → ℝ)
    (hherm : (cosGram θ).IsHermitian) :
    ∑ i, |hherm.eigenvalues i| = (n : ℝ) := by
  have hpos : ∀ i, 0 ≤ hherm.eigenvalues i := fun i =>
    Matrix.PosSemidef.eigenvalues_nonneg (cosGram_posSemidef θ) i
  have h1 : ∑ i, |hherm.eigenvalues i| = ∑ i, hherm.eigenvalues i :=
    Finset.sum_congr rfl fun i _ => abs_of_nonneg (hpos i)
  have h2 : (cosGram θ).trace = ∑ i, ((hherm.eigenvalues i : ℝ)) :=
    hherm.trace_eq_sum_eigenvalues
  rw [h1, ← h2, cosGram_trace]

end Brockian

