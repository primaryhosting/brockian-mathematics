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

theorem diagOp_counting_diverges :
    Filter.Tendsto (counting diagOp) Filter.atTop Filter.atTop :=
  counting_diverges_of_discrete_and_rvm diagOp finsupp_not_finiteDimensional
    diagOp_hasDiscreteSpectrum diagOp_rvmComplete

end Model

end Brockian.Weyl.WeylLawTarget

