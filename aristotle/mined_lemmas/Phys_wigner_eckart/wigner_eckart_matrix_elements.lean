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

theorem wigner_eckart_matrix_elements {V W U : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    {ιm ιq ιm' : Type*} (eV : ιm → V) (eW : ιq → W) (dU : ιm' → (U →ₗ[ℂ] ℂ))
    (ρV : Representation ℂ G V) (ρW : Representation ℂ G W) (σ : Representation ℂ G U)
    (hσ : IsIrrep σ)
    (K : Submodule ℂ (V ⊗[ℂ] W))
    (hKinv : ∀ (g : G), ∀ x ∈ K, (ρV.tprod ρW) g x ∈ K)
    (hKhom : ∀ f : K →ₗ[ℂ] U, Intertwines (subRep (ρV.tprod ρW) K hKinv) σ f → f = 0)
    (ι : U →ₗ[ℂ] V ⊗[ℂ] W) (hι : Intertwines σ (ρV.tprod ρW) ι)
    (hdec : ∀ x : V ⊗[ℂ] W, ∃ u : U, ∃ k ∈ K, x = ι u + k)
    (C T : (V ⊗[ℂ] W) →ₗ[ℂ] U)
    (hC : Intertwines (ρV.tprod ρW) σ C) (hT : Intertwines (ρV.tprod ρW) σ T) (hC0 : C ≠ 0) :
    ∃ r : ℂ, ∀ (m : ιm) (q : ιq) (m' : ιm'),
      dU m' (T (eV m ⊗ₜ[ℂ] eW q)) = r * dU m' (C (eV m ⊗ₜ[ℂ] eW q)) := by
  obtain ⟨r, hr⟩ :=
    wigner_eckart ρV ρW σ hσ K hKinv hKhom ι hι hdec C T hC hT hC0
  exact ⟨r, fun m q m' => hr (dU m') (eV m) (eW q)⟩

/-- A concrete instance showing that the hypotheses of `Phys.wigner_eckart` are satisfiable:
taking the trivial one-dimensional representation on the left factor, `ℂ ⊗ U` contains exactly one
copy of the irreducible representation `U`, and the Clebsch–Gordan map is the canonical
isomorphism `ℂ ⊗ U ≃ U`.  Hence every tensor operator `T : ℂ ⊗ U → U` is a fixed multiple of it. -/
