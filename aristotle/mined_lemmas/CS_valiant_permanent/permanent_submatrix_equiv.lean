import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed directly after the `import` line: Lean 4 requires `import`
commands to come first in a file.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

open Matrix

/-! ## Permanents as counting problems -/

/-- The permanent, written as a sum over permutations of the products `∏ i, M i (σ i)`
(Mathlib's definition uses `∏ i, M (σ i) i`; the two agree). -/

theorem permanent_submatrix_equiv {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V']
    [DecidableEq V'] (e : V ≃ V') (M : Matrix V' V' ℕ) :
    (M.submatrix e e).permanent = M.permanent := by
  classical
  refine Fintype.sum_equiv (Equiv.permCongr e) _ _ (fun σ => ?_)
  rw [← Equiv.prod_comp e (fun j => M ((e.permCongr σ) j) j)]
  simp [Matrix.submatrix, Equiv.permCongr]

/-- For a matrix with entries in `{0,1}`, the permanent counts the permutations `σ` all of whose
entries `M i (σ i)` equal `1`; i.e. the permanent of a 0/1 matrix is the number of witnesses of an
explicitly checkable relation (the "membership in `#P`" half of Valiant's theorem). -/
