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
def Intertwines {V U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (f : V →ₗ[ℂ] U) : Prop :=
  ∀ (g : G) (v : V), f (ρ g v) = σ g (f v)

/-- A representation is irreducible if the underlying space is nontrivial and the only
invariant subspaces are `⊥` and `⊤`. -/
structure IsIrrep {U : Type*} [AddCommGroup U] [Module ℂ U]
    (σ : Representation ℂ G U) : Prop where
  nontrivial : Nontrivial U
  simple : ∀ p : Submodule ℂ U, (∀ (g : G), ∀ u ∈ p, σ g u ∈ p) → p = ⊥ ∨ p = ⊤

/-- The restriction of a representation to an invariant subspace. -/
def subRep {X : Type*} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (K : Submodule ℂ X) (hK : ∀ (g : G), ∀ x ∈ K, ρ g x ∈ K) : Representation ℂ G K where
  toFun g := (ρ g).restrict (fun x hx => hK g x hx)
  map_one' := by
    ext x
    simp [LinearMap.restrict_apply]
  map_mul' g h := by
    ext x
    simp [LinearMap.restrict_apply]

@[simp] lemma subRep_apply_coe {X : Type*} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) (K : Submodule ℂ X) (hK : ∀ (g : G), ∀ x ∈ K, ρ g x ∈ K)
    (g : G) (k : K) : ((subRep ρ K hK g k : K) : X) = ρ g (k : X) := rfl

/-- **Schur's lemma** (scalar form): a self-intertwiner of a finite-dimensional irreducible
complex representation is a scalar multiple of the identity. -/
theorem schur_scalar {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (σ : Representation ℂ G U) (hσ : IsIrrep σ) (f : U →ₗ[ℂ] U) (hf : Intertwines σ σ f) :
    ∃ c : ℂ, ∀ u : U, f u = c • u := by
  haveI := hσ.nontrivial
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (K := ℂ) (V := U) f
  refine ⟨c, ?_⟩
  have hinv : ∀ (g : G), ∀ u ∈ Module.End.eigenspace f c, σ g u ∈ Module.End.eigenspace f c := by
    intro g u hu
    rw [Module.End.mem_eigenspace_iff] at hu ⊢
    rw [hf g u, hu, map_smul]
  rcases hσ.simple (Module.End.eigenspace f c) hinv with h | h
  · exact absurd h hc
  · intro u
    have hu : u ∈ Module.End.eigenspace f c := by rw [h]; trivial
    rwa [Module.End.mem_eigenspace_iff] at hu

/-- If `U` does not occur in the invariant subspace `K` (i.e. `Hom_G(K, U) = 0`), then every
intertwiner `X → U` vanishes on `K`. -/
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
theorem intertwiner_eq_smul {X U : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G U) (hσ : IsIrrep σ)
    (K : Submodule ℂ X) (hKinv : ∀ (g : G), ∀ x ∈ K, ρ g x ∈ K)
    (hKhom : ∀ f : K →ₗ[ℂ] U, Intertwines (subRep ρ K hKinv) σ f → f = 0)
    (ι : U →ₗ[ℂ] X) (hι : Intertwines σ ρ ι)
    (hdec : ∀ x : X, ∃ u : U, ∃ k ∈ K, x = ι u + k)
    (C T : X →ₗ[ℂ] U) (hC : Intertwines ρ σ C) (hT : Intertwines ρ σ T) (hC0 : C ≠ 0) :
    ∃ r : ℂ, T = r • C := by
  have hCK : ∀ k ∈ K, C k = 0 := vanishes_on_K ρ σ K hKinv hKhom C hC
  have hTK : ∀ k ∈ K, T k = 0 := vanishes_on_K ρ σ K hKinv hKhom T hT
  have hCi : Intertwines σ σ (C ∘ₗ ι) := by
    intro g u
    simp only [LinearMap.comp_apply]
    rw [hι g u, hC g (ι u)]
  have hTi : Intertwines σ σ (T ∘ₗ ι) := by
    intro g u
    simp only [LinearMap.comp_apply]
    rw [hι g u, hT g (ι u)]
  obtain ⟨c, hc⟩ := schur_scalar σ hσ (C ∘ₗ ι) hCi
  obtain ⟨t, ht⟩ := schur_scalar σ hσ (T ∘ₗ ι) hTi
  simp only [LinearMap.comp_apply] at hc ht
  have hcne : c ≠ 0 := by
    intro hc0
    apply hC0
    ext x
    obtain ⟨u, k, hk, rfl⟩ := hdec x
    rw [map_add, hc u, hCK k hk, hc0, zero_smul, add_zero]
    simp
  refine ⟨t / c, ?_⟩
  ext x
  obtain ⟨u, k, hk, rfl⟩ := hdec x
  rw [LinearMap.smul_apply, map_add, map_add, hc u, ht u, hCK k hk, hTK k hk, add_zero, add_zero,
    smul_smul]
  field_simp

/-- **Wigner–Eckart theorem.**

Let `V`, `W`, `U` be complex representations of a group `G`, with `U` finite-dimensional and
irreducible (think `V = V_j` the states, `W = V_k` the tensor-operator multiplet, and `U = V_{j'}`
the final multiplet).  Assume `U` occurs with multiplicity one in `V ⊗ W`: there is an equivariant
embedding `ι : U → V ⊗ W` and an invariant complement `K` containing no copy of `U`
(`Hom_G(K, U) = 0`).

Let `C : V ⊗ W → U` be a fixed nonzero intertwiner — the Clebsch–Gordan map, whose components
`L (C (v ⊗ w))` are the Clebsch–Gordan coefficients — and let `T : V ⊗ W → U` be any intertwiner
(a tensor operator).

Then there is a single constant `r` (the *reduced matrix element*, independent of the magnetic
quantum numbers, i.e. of `v`, `w` and of the final-state functional `L`) such that every matrix
element of `T` is the corresponding Clebsch–Gordan coefficient times `r`. -/
theorem wigner_eckart {V W U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (ρV : Representation ℂ G V) (ρW : Representation ℂ G W) (σ : Representation ℂ G U)
    (hσ : IsIrrep σ)
    (K : Submodule ℂ (V ⊗[ℂ] W))
    (hKinv : ∀ (g : G), ∀ x ∈ K, (ρV.tprod ρW) g x ∈ K)
    (hKhom : ∀ f : K →ₗ[ℂ] U, Intertwines (subRep (ρV.tprod ρW) K hKinv) σ f → f = 0)
    (ι : U →ₗ[ℂ] V ⊗[ℂ] W) (hι : Intertwines σ (ρV.tprod ρW) ι)
    (hdec : ∀ x : V ⊗[ℂ] W, ∃ u : U, ∃ k ∈ K, x = ι u + k)
    (C T : (V ⊗[ℂ] W) →ₗ[ℂ] U)
    (hC : Intertwines (ρV.tprod ρW) σ C) (hT : Intertwines (ρV.tprod ρW) σ T) (hC0 : C ≠ 0) :
    ∃ r : ℂ, ∀ (L : U →ₗ[ℂ] ℂ) (v : V) (w : W),
      L (T (v ⊗ₜ[ℂ] w)) = r * L (C (v ⊗ₜ[ℂ] w)) := by
  obtain ⟨r, hr⟩ :=
    intertwiner_eq_smul (ρV.tprod ρW) σ hσ K hKinv hKhom ι hι hdec C T hC hT hC0
  refine ⟨r, fun L v w => ?_⟩
  rw [hr]
  simp

/-- Coordinate form of the Wigner–Eckart theorem: with bases `|j m⟩` of `V`, `|k q⟩` of `W`, and
functionals `⟨j' m'|` on `U`, the matrix elements `⟨j' m'| T |j m, k q⟩` of a tensor operator `T`
are the Clebsch–Gordan coefficients `⟨j' m'| C |j m, k q⟩` times a single reduced matrix element
`r`, independent of `m`, `q` and `m'`. -/
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
theorem wigner_eckart_trivial_left {U : Type*} [AddCommGroup U] [Module ℂ U]
    [FiniteDimensional ℂ U] (σ : Representation ℂ G U) (hσ : IsIrrep σ)
    (T : (ℂ ⊗[ℂ] U) →ₗ[ℂ] U) (hT : Intertwines ((1 : Representation ℂ G ℂ).tprod σ) σ T) :
    ∃ r : ℂ, ∀ (L : U →ₗ[ℂ] ℂ) (a : ℂ) (u : U),
      L (T (a ⊗ₜ[ℂ] u)) = r * L ((TensorProduct.lid ℂ U) (a ⊗ₜ[ℂ] u)) := by
  haveI := hσ.nontrivial
  have hKinv : ∀ (g : G), ∀ x ∈ (⊥ : Submodule ℂ (ℂ ⊗[ℂ] U)),
      ((1 : Representation ℂ G ℂ).tprod σ) g x ∈ (⊥ : Submodule ℂ (ℂ ⊗[ℂ] U)) := by
    intro g x hx
    rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]
  have hC0 : ((TensorProduct.lid ℂ U).toLinearMap) ≠ 0 := by
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    intro h
    apply hu
    have := LinearMap.congr_fun h ((1 : ℂ) ⊗ₜ[ℂ] u)
    simpa using this
  obtain ⟨r, hr⟩ := wigner_eckart (1 : Representation ℂ G ℂ) σ σ hσ ⊥ hKinv
    (by
      intro f _
      ext x
      have hx : x = 0 := Subtype.ext (Submodule.mem_bot ℂ |>.1 x.2)
      rw [hx, map_zero]
      simp)
    ((TensorProduct.lid ℂ U).symm.toLinearMap)
    (by
      intro g u
      simp)
    (by
      intro x
      exact ⟨(TensorProduct.lid ℂ U) x, 0, Submodule.zero_mem _, by simp⟩)
    ((TensorProduct.lid ℂ U).toLinearMap) T
    (by
      intro g x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a u => simp
      | add x y hx hy => simp only [map_add, hx, hy])
    hT hC0
  exact ⟨r, fun L a u => hr L a u⟩

end Phys

