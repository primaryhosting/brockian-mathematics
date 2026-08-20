import Brockian.Weyl.WeylLawTarget

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

import Mathlib
/-!
# Counting Diverges Of Candidate
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_candidate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.Weyl.WeylLawTarget

/-- A *candidate spectrum* for a Weyl-law statement: a nondecreasing sequence of real
eigenvalue candidates `lam 0 ≤ lam 1 ≤ ⋯` which is unbounded above.  This is the
combinatorial data underlying the eigenvalue counting function of a Weyl law. -/
structure Candidate where
  /-- The candidate eigenvalues, listed with multiplicity in nondecreasing order. -/
  lam : ℕ → ℝ
  /-- The listing is nondecreasing. -/
  mono : Monotone lam
  /-- The listing is unbounded: only finitely many candidates lie below any threshold. -/
  unbounded : Filter.Tendsto lam Filter.atTop Filter.atTop

namespace Candidate

variable (C : Candidate)

/-- Below any threshold `t` only finitely many candidate eigenvalues occur. -/

theorem succ_le_counting {k : ℕ} {t : ℝ} (hk : C.lam k ≤ t) : k + 1 ≤ C.counting t := by
  have hsub : Set.Iic k ⊆ {n : ℕ | C.lam n ≤ t} := fun n hn =>
    le_trans (C.mono (Set.mem_Iic.1 hn)) hk
  have := Set.ncard_le_ncard hsub (C.finite_below t)
  simpa [counting, Nat.card_Iic] using this

end Candidate

/-- **Divergence of the counting function of a candidate spectrum.**
For any candidate spectrum, the eigenvalue counting function
`N(t) = #{n : lam n ≤ t}` tends to infinity as `t → ∞`.  This discharges the
hypothesis that the Weyl counting function of a candidate is unbounded. -/
