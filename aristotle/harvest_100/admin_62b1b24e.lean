/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped TensorProduct
open Representation

namespace Phys

variable {k G U V W : Type*} [Field k] [Group G]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The space of intertwining (`G`-equivariant) linear maps between two representations,
as a subspace of all linear maps. -/
def intertwiners (ρ : Representation k G V) (σ : Representation k G W) :
    Submodule k (V →ₗ[k] W) where
  carrier := {f | ∀ (g : G) (v : V), f (ρ g v) = σ g (f v)}
  zero_mem' := by intro g v; simp
  add_mem' := by
    intro f₁ f₂ h₁ h₂ g v
    simp [h₁ g v, h₂ g v]
  smul_mem' := by
    intro c f h g v
    simp [h g v]

@[simp] lemma mem_intertwiners {ρ : Representation k G V} {σ : Representation k G W}
    {f : V →ₗ[k] W} : f ∈ intertwiners ρ σ ↔ ∀ (g : G) (v : V), f (ρ g v) = σ g (f v) := Iff.rfl

/-- Bundling a member of `Phys.intertwiners` as a Mathlib `Representation.IntertwiningMap`. -/
def toIntertwiningMap {ρ : Representation k G V} {σ : Representation k G W}
    (f : V →ₗ[k] W) (hf : f ∈ intertwiners ρ σ) : IntertwiningMap ρ σ where
  toLinearMap := f
  isIntertwining' := hf

@[simp] lemma coe_toIntertwiningMap {ρ : Representation k G V} {σ : Representation k G W}
    (f : V →ₗ[k] W) (hf : f ∈ intertwiners ρ σ) :
    ⇑(toIntertwiningMap f hf) = ⇑f := rfl

/-- The inverse of a bijective intertwining map is again an intertwining map. -/
noncomputable def intertwinerInverse {ρ : Representation k G V} {σ : Representation k G W}
    (f : IntertwiningMap ρ σ) (hf : Function.Bijective f) : IntertwiningMap σ ρ where
  toLinearMap := (LinearEquiv.ofBijective f.toLinearMap hf).symm
  isIntertwining' g w := by
    have key : ∀ x : W, f ((LinearEquiv.ofBijective f.toLinearMap hf).symm x) = x :=
      fun x => (LinearEquiv.ofBijective f.toLinearMap hf).apply_symm_apply x
    apply hf.injective
    change f ((LinearEquiv.ofBijective f.toLinearMap hf).symm ((σ g) w))
      = f ((ρ g) ((LinearEquiv.ofBijective f.toLinearMap hf).symm w))
    rw [key, f.isIntertwining, key]

@[simp] lemma intertwinerInverse_apply_apply {ρ : Representation k G V}
    {σ : Representation k G W} (f : IntertwiningMap ρ σ) (hf : Function.Bijective f) (v : V) :
    intertwinerInverse f hf (f v) = v :=
  (LinearEquiv.ofBijective f.toLinearMap hf).symm_apply_apply v

/-- **Proportionality of intertwiners in a multiplicity-one situation.**
If the space of intertwiners `ρ → σ` is at most one dimensional and `CG` is a nonzero
intertwiner, then every intertwiner is a scalar multiple of `CG`. -/
theorem exists_smul_eq_of_rank_le_one {ρ : Representation k G V} {σ : Representation k G W}
    (hmult : Module.rank k (intertwiners ρ σ) ≤ 1)
    {CG T : V →ₗ[k] W} (hCG : CG ∈ intertwiners ρ σ) (hT : T ∈ intertwiners ρ σ)
    (hCG0 : CG ≠ 0) :
    ∃ c : k, T = c • CG := by
  rw [rank_le_one_iff] at hmult
  obtain ⟨v₀, h⟩ := hmult
  obtain ⟨a, ha⟩ := h ⟨CG, hCG⟩
  obtain ⟨b, hb⟩ := h ⟨T, hT⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hCG0
    have := congrArg Subtype.val ha
    simpa using this.symm
  refine ⟨b / a, ?_⟩
  have hb' : b • (v₀ : V →ₗ[k] W) = T := congrArg Subtype.val hb
  have ha' : a • (v₀ : V →ₗ[k] W) = CG := congrArg Subtype.val ha
  rw [← hb', ← ha', smul_smul, div_mul_cancel₀ _ ha0]

/-- **Schur's lemma, multiplicity-one form.** Over an algebraically closed field, the space of
intertwiners between two irreducible representations (the target being finite dimensional)
has rank at most one. -/
theorem rank_intertwiners_le_one [IsAlgClosed k] {ρ : Representation k G V}
    {σ : Representation k G W} [FiniteDimensional k W]
    [IsIrreducible ρ] [IsIrreducible σ] :
    Module.rank k (intertwiners ρ σ) ≤ 1 := by
  rw [rank_le_one_iff]
  by_cases h : ∀ f : intertwiners ρ σ, f = 0
  · exact ⟨0, fun f => ⟨0, by rw [h f, zero_smul]⟩⟩
  push_neg at h
  obtain ⟨g, hg⟩ := h
  set G' : IntertwiningMap ρ σ := toIntertwiningMap g.1 g.2 with hG'
  have hG'0 : G' ≠ 0 := by
    intro hh
    apply hg
    ext v
    have : G' v = 0 := by rw [hh]; rfl
    simpa [hG', toIntertwiningMap] using this
  have hbij : Function.Bijective G' :=
    (IsIrreducible.bijective_or_eq_zero G').resolve_right hG'0
  refine ⟨g, fun f => ?_⟩
  set F : IntertwiningMap ρ σ := toIntertwiningMap f.1 f.2 with hF
  obtain ⟨c, hc⟩ :=
    (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := σ)).surjective (F.comp (intertwinerInverse G' hbij))
  refine ⟨c, ?_⟩
  ext v
  have hv := congrArg (fun e : IntertwiningMap σ σ => e (G' v)) hc
  simp only [IntertwiningMap.algebraMap_apply] at hv
  have hcomp : (F.comp (intertwinerInverse G' hbij)) (G' v) = F v := by
    simp [IntertwiningMap.comp, IntertwiningMap.llcomp]
  rw [hcomp] at hv
  have hleft : ((c • (1 : IntertwiningMap σ σ)) : IntertwiningMap σ σ) (G' v) = c • (G' v) := rfl
  rw [hleft] at hv
  simpa [hF, hG', toIntertwiningMap] using hv

/-- **The Wigner–Eckart theorem.**

Let `τ`, `ρ`, `σ` be representations of a group `G` on `U`, `V`, `W`: think of `τ` as the spin-`k`
representation carrying the components `q` of a tensor operator `T^k_q`, of `ρ` as the spin-`j`
representation of the initial states `|j m⟩`, and of `σ` as the spin-`j'` representation of the
final states `|j' m'⟩`.  A tensor operator is precisely an equivariant map `T : τ ⊗ ρ → σ`, and
the Clebsch–Gordan map `CG` is a distinguished nonzero such equivariant map.

Assuming multiplicity one, i.e. that the space of equivariant maps `τ ⊗ ρ → σ` is at most one
dimensional (the standard `SU(2)` Clebsch–Gordan fact), there is a single scalar `red`, the
*reduced matrix element*, independent of the magnetic quantum numbers, such that every matrix
element `⟨j' m'| T^k_q |j m⟩` factors as `red` times the corresponding Clebsch–Gordan
coefficient `⟨j' m'| CG (q ⊗ m)⟩`. -/
theorem wigner_eckart {τ : Representation k G U} {ρ : Representation k G V}
    {σ : Representation k G W}
    (hmult : Module.rank k (intertwiners (τ.tprod ρ) σ) ≤ 1)
    (CG T : (U ⊗[k] V) →ₗ[k] W)
    (hCG : CG ∈ intertwiners (τ.tprod ρ) σ) (hT : T ∈ intertwiners (τ.tprod ρ) σ)
    (hCG0 : CG ≠ 0) :
    ∃ red : k, T = red • CG ∧ ∀ (φ : W →ₗ[k] k) (u : U) (v : V),
      φ (T (u ⊗ₜ[k] v)) = red * φ (CG (u ⊗ₜ[k] v)) := by
  obtain ⟨red, hred⟩ := exists_smul_eq_of_rank_le_one hmult hCG hT hCG0
  refine ⟨red, hred, fun φ u v => ?_⟩
  rw [hred]
  simp

/-- A version of `Phys.wigner_eckart` in which the multiplicity-one hypothesis is supplied by
Schur's lemma. -/
theorem wigner_eckart_of_irreducible [IsAlgClosed k] {τ : Representation k G U}
    {ρ : Representation k G V} {σ : Representation k G W} [FiniteDimensional k W]
    [IsIrreducible (τ.tprod ρ)] [IsIrreducible σ]
    (CG T : (U ⊗[k] V) →ₗ[k] W)
    (hCG : CG ∈ intertwiners (τ.tprod ρ) σ) (hT : T ∈ intertwiners (τ.tprod ρ) σ)
    (hCG0 : CG ≠ 0) :
    ∃ red : k, T = red • CG ∧ ∀ (φ : W →ₗ[k] k) (u : U) (v : V),
      φ (T (u ⊗ₜ[k] v)) = red * φ (CG (u ⊗ₜ[k] v)) :=
  wigner_eckart rank_intertwiners_le_one CG T hCG hT hCG0

/-! ### A concrete instance, showing the hypotheses are not vacuous -/

section Concrete

variable (Γ : Type*) [Group Γ]

/-- The trivial one-dimensional complex representation of a group `Γ`. -/
def trivialRep : Representation ℂ Γ ℂ := 1

/-- For the one-dimensional trivial representations of any group the multiplicity-one
hypothesis of `Phys.wigner_eckart` holds. -/
theorem rank_intertwiners_trivial_le_one :
    Module.rank ℂ (intertwiners ((trivialRep Γ).tprod (trivialRep Γ)) (trivialRep Γ)) ≤ 1 := by
  have h0 :
      Module.rank ℂ (intertwiners ((trivialRep Γ).tprod (trivialRep Γ)) (trivialRep Γ))
        ≤ Module.rank ℂ ((ℂ ⊗[ℂ] ℂ) →ₗ[ℂ] ℂ) :=
    Submodule.rank_le _
  refine le_trans h0 ?_
  have h : Module.finrank ℂ ((ℂ ⊗[ℂ] ℂ) →ₗ[ℂ] ℂ) = 1 := by
    rw [Module.finrank_linearMap]; simp
  rw [← Module.finrank_eq_rank, h]
  norm_num

/-- The canonical multiplication map `ℂ ⊗ ℂ → ℂ` is an intertwiner of trivial representations;
it plays the role of the Clebsch–Gordan map in this example. -/
theorem lid_mem_intertwiners_trivial :
    (TensorProduct.lid ℂ ℂ).toLinearMap ∈
      intertwiners ((trivialRep Γ).tprod (trivialRep Γ)) (trivialRep Γ) := by
  intro g v
  simp [Representation.tprod, trivialRep]

theorem lid_ne_zero : (TensorProduct.lid ℂ ℂ).toLinearMap ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : (ℂ ⊗[ℂ] ℂ) →ₗ[ℂ] ℂ => f (1 ⊗ₜ[ℂ] 1)) h
  simp at h1

/-- A concrete, non-vacuous instance of the Wigner–Eckart theorem. -/
theorem wigner_eckart_trivial (T : (ℂ ⊗[ℂ] ℂ) →ₗ[ℂ] ℂ)
    (hT : T ∈ intertwiners ((trivialRep Γ).tprod (trivialRep Γ)) (trivialRep Γ)) :
    ∃ red : ℂ, T = red • (TensorProduct.lid ℂ ℂ).toLinearMap ∧ ∀ (φ : ℂ →ₗ[ℂ] ℂ) (u v : ℂ),
      φ (T (u ⊗ₜ[ℂ] v)) = red * φ ((TensorProduct.lid ℂ ℂ) (u ⊗ₜ[ℂ] v)) :=
  wigner_eckart (rank_intertwiners_trivial_le_one Γ) _ T
    (lid_mem_intertwiners_trivial Γ) hT lid_ne_zero

end Concrete

end Phys

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

