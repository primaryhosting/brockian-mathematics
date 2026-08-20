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

/-!
# The no-deleting theorem

Given two copies of an arbitrary unknown quantum state, it is impossible to delete one of
them by a unitary evolution of the composite system (system + system + ancilla).

We model the qubit Hilbert space by `EuclideanSpace ℂ (Fin 2)`, the ancilla by
`EuclideanSpace ℂ ι` for an arbitrary finite index type `ι`, and the composite system
`H ⊗ H ⊗ A` by `EuclideanSpace ℂ (Fin 2 × Fin 2 × ι)`.  The tensor product of vectors is
`QI.kron`, and `QI.tri x y z` is the threefold tensor product `x ⊗ y ⊗ z`.

The proof is the standard inner-product argument: a linear isometry preserves inner
products, so if `ψ ⊗ ψ ⊗ anc` were mapped to `ψ ⊗ blank ⊗ out` with `blank` and `out`
independent of `ψ`, then for all unit vectors `ψ`, `φ` one would get
`⟪ψ, φ⟫ * ⟪blank, blank⟫ * ⟪out, out⟫ = ⟪ψ, φ⟫ ^ 2 * ⟪anc, anc⟫`.  Taking `ψ = φ` shows
`⟪blank, blank⟫ * ⟪out, out⟫ = ⟪anc, anc⟫`, and then a pair of states with
`⟪ψ, φ⟫ = 3 / 5` forces `⟪anc, anc⟫ = 0`, i.e. `anc = 0`.
-/

namespace QI

/-- The tensor product `u ⊗ v` of two vectors, realized concretely as a vector indexed by
the product of the index types. -/

noncomputable def kron {α β : Type*} [Fintype α] [Fintype β]
    (u : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β) : EuclideanSpace ℂ (α × β) :=
  WithLp.toLp 2 (fun p => u p.1 * v p.2)

/-- Inner products factor over the tensor product. -/
