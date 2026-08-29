/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open Matrix Finset

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/

theorem vonNeumann_trace_ineq_sorted {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (A * B)).re ≤
      ∑ i, (hA.eigenvalues ∘ Tuple.sort hA.eigenvalues ∘ Fin.rev) i *
        (hB.eigenvalues ∘ Tuple.sort hB.eigenvalues ∘ Fin.rev) i := by
  refine vonNeumann_trace_ineq hA hB _ _ ?_ ?_
    ⟨(Fin.revPerm).trans (Tuple.sort hA.eigenvalues), rfl⟩
    ⟨(Fin.revPerm).trans (Tuple.sort hB.eigenvalues), rfl⟩
  · exact fun i j hij => Tuple.monotone_sort hA.eigenvalues (Fin.rev_le_rev.mpr hij)
  · exact fun i j hij => Tuple.monotone_sort hB.eigenvalues (Fin.rev_le_rev.mpr hij)

end Zeta23Redux.LinAlg

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

