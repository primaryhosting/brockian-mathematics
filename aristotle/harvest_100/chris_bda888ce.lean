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

open scoped TensorProduct

variable {G : Type*} [Group G]
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A (complex) representation is *irreducible* if the space is nontrivial and the only
subspaces invariant under the group action are `⊥` and `⊤`. -/
def IsIrrep (ρ : Representation ℂ G V) : Prop :=
  Nontrivial V ∧
    ∀ U : Submodule ℂ V, (∀ (g : G) (v : V), v ∈ U → ρ g v ∈ U) → U = ⊥ ∨ U = ⊤

/-- `T` intertwines the representations `ρ` and `σ` (i.e. it is an operator transforming
covariantly: `T ∘ ρ g = σ g ∘ T`).  For `V = V_k ⊗ V_j` this is exactly the statement that the
components `T_q` form an irreducible tensor operator of rank `k`. -/
def Intertwines (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (T : V →ₗ[ℂ] W) : Prop :=
  ∀ (g : G) (v : V), T (ρ g v) = σ g (T v)

section Schur

variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- A nonzero intertwiner out of an irreducible representation is injective. -/
theorem Intertwines.injective (hρ : IsIrrep ρ) {T : V →ₗ[ℂ] W} (hT : Intertwines ρ σ T)
    (hT0 : T ≠ 0) : Function.Injective T := by
  have hker : LinearMap.ker T = ⊥ ∨ LinearMap.ker T = ⊤ := by
    refine hρ.2 _ ?_
    intro g v hv
    simp only [LinearMap.mem_ker] at hv ⊢
    rw [hT g v, hv, map_zero]
  rcases hker with h | h
  · exact LinearMap.ker_eq_bot.mp h
  · exact absurd (by ext v; simpa using (LinearMap.mem_ker (f := T)).mp (h ▸ Submodule.mem_top))
      hT0

/-- A nonzero intertwiner into an irreducible representation is surjective. -/
theorem Intertwines.surjective (hσ : IsIrrep σ) {T : V →ₗ[ℂ] W} (hT : Intertwines ρ σ T)
    (hT0 : T ≠ 0) : Function.Surjective T := by
  have hr : LinearMap.range T = ⊥ ∨ LinearMap.range T = ⊤ := by
    refine hσ.2 _ ?_
    rintro g _ ⟨v, rfl⟩
    exact ⟨ρ g v, hT g v⟩
  rcases hr with h | h
  · refine absurd ?_ hT0
    ext v
    have : T v ∈ (⊥ : Submodule ℂ W) := h ▸ LinearMap.mem_range_self T v
    simpa using this
  · exact LinearMap.range_eq_top.mp h

/-- **Schur's lemma** (the key intermediate step): any two intertwiners between irreducible
complex representations are proportional, provided the second one is nonzero.  This is the
mathematical content behind the Wigner–Eckart theorem. -/
theorem exists_smul_of_intertwines [FiniteDimensional ℂ V] (hρ : IsIrrep ρ) (hσ : IsIrrep σ)
    {S : V →ₗ[ℂ] W} (hS : Intertwines ρ σ S) (hS0 : S ≠ 0)
    {T : V →ₗ[ℂ] W} (hT : Intertwines ρ σ T) :
    ∃ c : ℂ, T = c • S := by
  haveI : Nontrivial V := hρ.1
  have hbij : Function.Bijective S := ⟨hS.injective hρ hS0, hS.surjective hσ hS0⟩
  let e : V ≃ₗ[ℂ] W := LinearEquiv.ofBijective S hbij
  have he : ∀ v : V, e v = S v := fun v => rfl
  have hesymm : ∀ (g : G) (w : W), e.symm (σ g w) = ρ g (e.symm w) := by
    intro g w
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he (ρ g (e.symm w)), hS g (e.symm w), ← he,
      LinearEquiv.apply_symm_apply]
  let f : Module.End ℂ V := (e.symm : W →ₗ[ℂ] V) ∘ₗ T
  have hf : ∀ (g : G) (v : V), f (ρ g v) = ρ g (f v) := by
    intro g v
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hT g v, hesymm g (T v)]
  obtain ⟨c, hc⟩ := f.exists_eigenvalue
  have hinv : ∀ (g : G) (v : V), v ∈ Module.End.eigenspace f c → ρ g v ∈
      Module.End.eigenspace f c := by
    intro g v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [hf g v, hv, map_smul]
  have htop : Module.End.eigenspace f c = ⊤ := by
    rcases hρ.2 _ hinv with h | h
    · exact absurd h hc
    · exact h
  refine ⟨c, ?_⟩
  ext v
  have hv : f v = c • v := by
    rw [← Module.End.mem_eigenspace_iff, htop]
    exact Submodule.mem_top
  have : T v = e (f v) := by
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [this, hv, map_smul, he]
  simp

/-- There is a *universal* intertwiner `S` (unique up to scale) such that every intertwiner is a
scalar multiple of it: the space of intertwiners between irreducible representations is at most
one-dimensional. -/
theorem exists_universal_intertwiner [FiniteDimensional ℂ V] (hρ : IsIrrep ρ) (hσ : IsIrrep σ) :
    ∃ S : V →ₗ[ℂ] W, Intertwines ρ σ S ∧
      ∀ T : V →ₗ[ℂ] W, Intertwines ρ σ T → ∃ c : ℂ, T = c • S := by
  by_cases h : ∃ S : V →ₗ[ℂ] W, Intertwines ρ σ S ∧ S ≠ 0
  · obtain ⟨S, hS, hS0⟩ := h
    exact ⟨S, hS, fun T hT => exists_smul_of_intertwines hρ hσ hS hS0 hT⟩
  · push_neg at h
    refine ⟨0, fun g v => by simp, fun T hT => ⟨0, ?_⟩⟩
    rw [h T hT]
    simp

end Schur

/-- **Wigner–Eckart theorem.**

Let `ρ` be an irreducible representation on `V` (physically `V = V_k ⊗ V_j`, spanned by the states
`|k q⟩ ⊗ |j m⟩`) and `σ` an irreducible representation on `W` (physically `V_{j'}`, spanned by the
states `|j' m'⟩`).  Then there is a fixed array of numbers `CG m' m` — the Clebsch–Gordan
coefficients, depending only on the representations and the chosen bases, *not* on the operator —
such that for **every** tensor operator `T` (i.e. every intertwiner) there is a single number
`red` — the reduced matrix element, independent of the magnetic quantum numbers `m`, `m'` — with

`⟨m'| T |m⟩ = red * CG m' m`.

That is, the matrix elements of a tensor operator factor into a Clebsch–Gordan coefficient times a
reduced matrix element. -/
theorem wigner_eckart [FiniteDimensional ℂ V] {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (hρ : IsIrrep ρ) (hσ : IsIrrep σ)
    {ι κ : Type*} (bV : Module.Basis ι ℂ V) (bW : Module.Basis κ ℂ W) :
    ∃ CG : κ → ι → ℂ,
      ∀ T : V →ₗ[ℂ] W, Intertwines ρ σ T →
        ∃ red : ℂ, ∀ (m' : κ) (m : ι), bW.repr (T (bV m)) m' = red * CG m' m := by
  obtain ⟨S, hS, huniv⟩ := exists_universal_intertwiner hρ hσ
  refine ⟨fun m' m => bW.repr (S (bV m)) m', ?_⟩
  intro T hT
  obtain ⟨c, rfl⟩ := huniv T hT
  exact ⟨c, fun m' m => by simp [smul_eq_mul]⟩

/-- The Wigner–Eckart theorem in its familiar tensor-operator form: `V₁` carries the rank-`k`
operator index `q`, `V₂` carries the initial state index `m`, `W` the final state index `m'`, and
the operator acts on `V₁ ⊗ V₂`.  The matrix element `⟨m'| T_q |m⟩` factors as a Clebsch–Gordan
coefficient `CG m' (q, m)` (independent of the operator) times a reduced matrix element `red`
(independent of `q, m, m'`). -/
theorem wigner_eckart_tensor {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₂]
    {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}
    {ρ₁₂ : Representation ℂ G (V₁ ⊗[ℂ] V₂)} {σ : Representation ℂ G W}
    (hρ₁₂tmul : ∀ (g : G) (x : V₁) (y : V₂), ρ₁₂ g (x ⊗ₜ[ℂ] y) = (ρ₁ g x) ⊗ₜ[ℂ] (ρ₂ g y))
    (hρ₁₂ : IsIrrep ρ₁₂) (hσ : IsIrrep σ)
    {ι₁ ι₂ κ : Type*} (b₁ : Module.Basis ι₁ ℂ V₁) (b₂ : Module.Basis ι₂ ℂ V₂)
    (bW : Module.Basis κ ℂ W) :
    ∃ CG : κ → ι₁ × ι₂ → ℂ,
      ∀ T : (V₁ ⊗[ℂ] V₂) →ₗ[ℂ] W,
        (∀ (g : G) (x : V₁) (y : V₂), T ((ρ₁ g x) ⊗ₜ[ℂ] (ρ₂ g y)) = σ g (T (x ⊗ₜ[ℂ] y))) →
        ∃ red : ℂ, ∀ (m' : κ) (q : ι₁) (m : ι₂),
          bW.repr (T (b₁ q ⊗ₜ[ℂ] b₂ m)) m' = red * CG m' (q, m) := by
  obtain ⟨CG, hCG⟩ := wigner_eckart (ρ := ρ₁₂) (σ := σ) hρ₁₂ hσ (b₁.tensorProduct b₂) bW
  refine ⟨CG, ?_⟩
  intro T hT
  have hTint : Intertwines ρ₁₂ σ T := by
    intro g v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rw [hρ₁₂tmul g x y, hT g x y]
    | add x y hx hy => simp [hx, hy]
  obtain ⟨red, hred⟩ := hCG T hTint
  refine ⟨red, fun m' q m => ?_⟩
  have := hred m' (q, m)
  simpa using this

/-- Standard physical corollary of the Wigner–Eckart theorem: the matrix elements of any two
tensor operators of the same rank between the same pair of irreducible multiplets are
proportional, with a single proportionality constant (the ratio of their reduced matrix elements)
that does not depend on the magnetic quantum numbers `m`, `m'`. -/
theorem matrixElement_proportional [FiniteDimensional ℂ V] {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (hρ : IsIrrep ρ) (hσ : IsIrrep σ)
    {ι κ : Type*} (bV : Module.Basis ι ℂ V) (bW : Module.Basis κ ℂ W)
    {T T' : V →ₗ[ℂ] W} (hT : Intertwines ρ σ T) (hT' : Intertwines ρ σ T') (hT'0 : T' ≠ 0) :
    ∃ c : ℂ, ∀ (m' : κ) (m : ι),
      bW.repr (T (bV m)) m' = c * bW.repr (T' (bV m)) m' := by
  obtain ⟨c, rfl⟩ := exists_smul_of_intertwines hρ hσ hT' hT'0 hT
  exact ⟨c, fun m' m => by simp [smul_eq_mul]⟩

/-- Non-vacuity check: the trivial one-dimensional representation is irreducible, so the
hypotheses of `Phys.wigner_eckart` are satisfiable. -/
theorem isIrrep_one_complex : IsIrrep (1 : Representation ℂ G ℂ) := by
  refine ⟨inferInstance, fun U _ => ?_⟩
  exact (inferInstance : IsSimpleModule ℂ ℂ).eq_bot_or_eq_top U

end Phys

