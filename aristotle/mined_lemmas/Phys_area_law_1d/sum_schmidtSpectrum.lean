import Mathlib
/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header block is required to be the first content of the file; Lean 4 requires
`import` statements to precede every other command, including module docstrings, so the
single `import Mathlib` line above is the only thing preceding it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

namespace Phys

/-! ## Shannon entropy of a finite spectrum -/

/-- Shannon (von Neumann) entropy of a finite family of probabilities. -/

lemma sum_schmidtSpectrum [DecidableEq A] (psi : A → B → ℂ)
    (hnorm : ∑ a, ∑ b, ‖psi a b‖ ^ 2 = 1) :
    ∑ a, schmidtSpectrum psi a = 1 := by
  have htr : (reducedDensity psi).trace = ∑ a, ((schmidtSpectrum psi a : ℝ) : ℂ) :=
    (reducedDensity_posSemidef psi).isHermitian.trace_eq_sum_eigenvalues
  have htr2 : (reducedDensity psi).trace = ((1 : ℝ) : ℂ) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    have : ∀ a : A, reducedDensity psi a a = ((∑ b, ‖psi a b‖ ^ 2 : ℝ) : ℂ) := by
      intro a
      rw [reducedDensity_apply]
      push_cast
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Complex.mul_conj]
      norm_cast
      exact Complex.normSq_eq_norm_sq _
    rw [Finset.sum_congr rfl (fun a _ => this a), ← Complex.ofReal_sum, hnorm]
  rw [htr2] at htr
  have : ((∑ a, schmidtSpectrum psi a : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]; exact htr.symm
  exact_mod_cast this

/-- Entanglement entropy of a bipartite pure state: the von Neumann entropy of its
reduced density matrix. -/
