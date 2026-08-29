/-
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The bilinear form `u ↦ v ↦ ∑ᵢ ∑ⱼ uᵢ Mᵢⱼ vⱼ` attached to a matrix `M`. -/

lemma sum_indicator_mul {V : Type*} [Fintype V] (S : Finset V) (f : V → ℝ) :
    ∑ i, (if i ∈ S then (1 : ℝ) else 0) * f i = ∑ i ∈ S, f i := by
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    show (if i ∈ S then (1 : ℝ) else 0) * f i = if i ∈ S then f i else 0 by
      by_cases h : i ∈ S <;> simp [h])]
  rw [Finset.sum_ite_mem]
  simp

/-- **Expander mixing lemma** (Alon–Chung; see Hoory–Linial–Wigderson).

Let `M` be a real symmetric matrix indexed by a finite vertex set `V` all of whose row sums
equal `d` (e.g. the adjacency matrix of a `d`-regular graph), and suppose `M` contracts the
space of mean-zero vectors by a factor `lam` (i.e. `lam` dominates the absolute values of all
eigenvalues other than the trivial one `d`).  Then for any two vertex subsets `S`, `T` the
number of edges between `S` and `T` deviates from its "random graph" expectation
`d |S| |T| / n` by at most `lam * sqrt (|S| |T|)`. -/
