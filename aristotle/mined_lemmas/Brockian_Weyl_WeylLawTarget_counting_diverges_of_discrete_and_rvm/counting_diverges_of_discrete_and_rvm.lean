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
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Weyl-law style statement proved here: for a linear operator `T` on an infinite
dimensional real vector space (in particular on a real inner product space) whose spectrum is
*discrete* — every spectral subspace below a level is finite dimensional — and whose
eigensystem is *complete*, as furnished by the Rayleigh variational method (RVM), the
eigenvalue counting function `lam ↦ dim (span of eigenvectors with eigenvalue ≤ lam)`
diverges to `+∞`.

The final section exhibits an explicit model (the diagonal operator `f ↦ (n ↦ n * f n)` on
finitely supported real sequences) satisfying all the hypotheses, so the theorem is not
vacuous.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.Weyl.WeylLawTarget

section General

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- The low-lying spectral subspace: the span of all eigenvectors of `T` whose
eigenvalue is at most `lam`. -/

theorem counting_diverges_of_discrete_and_rvm (T : Module.End ℝ H)
    (hinf : ¬ FiniteDimensional ℝ H) (hdisc : HasDiscreteSpectrum T)
    (hrvm : RVMComplete T) :
    Filter.Tendsto (counting T) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun k => ?_
  obtain ⟨lam, hlam⟩ := exists_le_counting T hinf hdisc hrvm k
  exact ⟨lam, fun a ha => hlam.trans (counting_mono T hdisc ha)⟩

end General

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Weyl law in the inner product space setting.**
Specialization of `counting_diverges_of_discrete_and_rvm` to an operator on an infinite
dimensional real inner product space. -/
