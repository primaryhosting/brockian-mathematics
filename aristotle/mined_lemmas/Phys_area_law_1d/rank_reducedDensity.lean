import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
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

namespace Phys

/-! ## Shannon entropy of a finite probability vector -/

/-- The Shannon entropy `-∑ pᵢ log pᵢ` of a finite family of reals. -/

theorem rank_reducedDensity (d N x : ℕ) (psi : (Fin N → Fin d) → ℂ) :
    (reducedDensity d N x psi).rank = (cutMatrix d N x psi).rank :=
  Matrix.rank_self_mul_conjTranspose _

/-! ## The area law -/

/-- **Entanglement-entropy area law in one dimension (Hastings).**

Setting: a chain of `N` sites with local Hilbert-space dimension `d`, in a normalized pure state
`psi`. For a cut at position `x` the state is matricized into `cutMatrix`, whose rank is the
Schmidt rank across the cut; the reduced density matrix of the left block is
`reducedDensity = M Mᴴ`, and the entanglement entropy of the cut is its von Neumann entropy.

Hypothesis `hSchmidt` is the content of Hastings' matrix-product-state construction for gapped
local Hamiltonians: the ground state has Schmidt rank bounded by a *bond dimension* `D` that
depends only on the local dimension and the spectral gap (through the correlation length), and not
on the system size `N` nor on the location `x` of the cut.

Conclusion: the entanglement entropy across *every* cut is bounded by `log D`, a constant
independent of the size of the subsystem — i.e. the entropy obeys an area law (in one dimension the
"boundary" of a block is a single point, so the area law means a size-independent constant). -/
