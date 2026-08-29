/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Phys

/-- An explicit Kochen–Specker set of 18 vectors in `ℝ⁴` (all entries in `{0, 1, -1}`).
They are grouped by `ksBasis` into nine orthogonal bases, each vector belonging to
exactly two of the nine bases. -/

lemma ksBasis_orth (i : Fin 9) (j k : Fin 4) (hjk : j ≠ k) :
    ∑ m, ksVec (ksBasis i j) m * ksVec (ksBasis i k) m = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [ksVec, ksBasis, Fin.sum_univ_four]

/-- **Kochen–Specker theorem via an explicit 18-vector set.**
There is no `{0,1}`-coloring `c` of the nonzero vectors of `ℝ⁴` assigning the value `1`
to exactly one vector of every orthogonal basis (i.e. with `c x + c y + c z + c w = 1`
for every four pairwise orthogonal nonzero vectors `x, y, z, w`).  The proof exhibits the
explicit 18-vector set `ksVec`, which forms nine orthogonal bases (`ksBasis`) in which each
vector occurs exactly twice: summing the nine basis equations gives `2 * N = 9`, which is
impossible.  (The hypothesis `hc01` that `c` takes only the values `0` and `1` is recorded
as part of the statement of a `{0,1}`-coloring; it is in fact implied by `hbasis` together
with `c` being `ℕ`-valued, so the proof does not need it.) -/
