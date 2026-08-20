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

namespace Frontier

section Mixing

variable {V : Type*} [Fintype V]

/-- The bilinear form associated with a weight matrix `A : V → V → ℝ`. -/

lemma sum_indicator_eq_card (S : Finset V) :
    ∑ v, (if v ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp

/-- **Expander mixing lemma** (base case, weighted/matrix form).

Let `A` be a symmetric real matrix indexed by a finite nonempty vertex set `V`, all of whose
row sums equal `d` (a `d`-regular weighted graph, e.g. the adjacency matrix of a `d`-regular
graph), and suppose that the quadratic form of `A` restricted to the space orthogonal to the
all-ones vector is bounded in absolute value by `lam` (i.e. `lam` bounds the second largest
eigenvalue in absolute value). Then for any two sets of vertices `S`, `T`, the number of edges
between them (counted with weights) differs from its "expected" value `d |S| |T| / n` by at
most `lam * √(|S| |T|)`. -/
