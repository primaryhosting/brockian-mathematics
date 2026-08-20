/-
# Grover Optimal
Category: Frontier Qi
Target: QI.grover_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Grover Optimal
Category: Frontier Qi
Target: QI.grover_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The BBBV lower bound for unstructured search

This file formalises the *hybrid argument* of Bennett, Bernstein, Brassard and Vazirani,
which shows that any quantum algorithm that distinguishes the empty database from each of the
`N` single-marked-item databases must make `Ω(√N)` oracle queries.  Consequently Grover's
algorithm, which uses `O(√N)` queries, is optimal.

### The model

* The algorithm's Hilbert space is `EuclideanSpace ℂ ι` for a finite index type `ι`
  (index register together with an arbitrary workspace).
* `idx : ι → Fin N` records, for each computational basis state, which of the `N` database
  entries is being queried.
* The oracle for a marked item `x : Fin N` is the phase oracle `phaseOracle idx x`, which
  negates exactly the amplitudes of the basis states querying `x`.  The *empty* database
  corresponds to the identity oracle.
* The algorithm is an arbitrary sequence `U : ℕ → E ≃ₗᵢ[ℂ] E` of unitaries interleaved with
  the oracle calls, started in an arbitrary unit vector `init`.
* `psi x` is the run against the oracle marking `x`, `phi` is the run against the empty
  database.

The conclusion is `c * √N ≤ 2 * T` whenever the two final states are at distance at least `c`
for *every* `x`, i.e. `T ≥ (c/2)·√N` queries are needed.
-/

namespace QI

open Finset

section

variable {ι : Type*} [Fintype ι] {N : ℕ}

/-- The phase oracle marking the database entry `x`: it negates the amplitude of every
computational basis state whose query register holds `x`. -/

theorem grover_optimal_run {ι : Type*} [Fintype ι] {N T : ℕ} (idx : ι → Fin N)
    (U : ℕ → (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι))
    (init : EuclideanSpace ℂ ι) (hinit : ‖init‖ = 1) (c : ℝ)
    (hdist : ∀ x, c ≤ ‖oracleRun U (phaseOracle idx x) init T - oracleRun U id init T‖) :
    c * Real.sqrt N ≤ 2 * T :=
  grover_optimal idx U init hinit (fun x => oracleRun U (phaseOracle idx x) init)
    (oracleRun U id init) (fun _ => rfl) (fun _ _ => rfl) rfl (fun _ => rfl) c hdist

end QI

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

