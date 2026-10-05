import Mathlib

/-!
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

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

variable {G : Type*} [Monoid G]

/-- A linear map `f : V → U` *intertwines* the representations `ρ` (on `V`) and `σ` (on `U`)
if it commutes with the group action. -/

theorem vanishes_on_K {X U : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G U)
    (K : Submodule ℂ X) (hKinv : ∀ (g : G), ∀ x ∈ K, ρ g x ∈ K)
    (hKhom : ∀ f : K →ₗ[ℂ] U, Intertwines (subRep ρ K hKinv) σ f → f = 0)
    (f : X →ₗ[ℂ] U) (hf : Intertwines ρ σ f) : ∀ k ∈ K, f k = 0 := by
  intro k hk
  have h0 : f ∘ₗ K.subtype = 0 := by
    refine hKhom _ ?_
    intro g x
    simpa using hf g (x : X)
  have := LinearMap.congr_fun h0 ⟨k, hk⟩
  simpa using this

/-- **Multiplicity-one rigidity.** Let `X` be a representation containing exactly one copy of the
finite-dimensional irreducible representation `U`: `X` is the sum of the image of an equivariant
map `ι : U → X` and an invariant complement `K` in which `U` does not occur.  Then any two
intertwiners `X → U` are proportional; in particular every intertwiner `T` is a scalar multiple of
a fixed nonzero one `C`. -/
