/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Statement: Matrix elements of tensor operators factor into a Clebsch–Gordan × reduced element (Wigner–Eckart).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

open TensorProduct

variable {G : Type*} [Monoid G]

/-- `f` intertwines the representations `ρ` and `σ`. -/
def Intertwines {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (f : V →ₗ[ℂ] W) : Prop :=
  ∀ (g : G) (v : V), f (ρ g v) = σ g (f v)

/-- A representation is irreducible when the space is nontrivial and the only invariant
subspaces are `⊥` and `⊤`. -/
def IsIrred {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) : Prop :=
  Nontrivial V ∧
    ∀ S : Submodule ℂ V, (∀ (g : G), ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤

/-- **Schur's lemma** (over `ℂ`): a self-intertwiner of a finite-dimensional irreducible
complex representation is a scalar. -/
theorem schur_scalar {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hirr : IsIrred ρ) (f : V →ₗ[ℂ] V)
    (hf : Intertwines ρ ρ f) : ∃ r : ℂ, ∀ v : V, f v = r • v := by
  obtain ⟨hnt, hsub⟩ := hirr
  haveI : Nontrivial V := hnt
  obtain ⟨r, hr⟩ := Module.End.exists_eigenvalue (K := ℂ) (V := V) f
  refine ⟨r, ?_⟩
  set S : Submodule ℂ V := Module.End.eigenspace f r with hS
  have hSinv : ∀ (g : G), ∀ v ∈ S, ρ g v ∈ S := by
    intro g v hv
    rw [hS, Module.End.mem_eigenspace_iff] at hv ⊢
    rw [hf g v, hv, map_smul]
  have hSne : S ≠ ⊥ := hr
  rcases hsub S hSinv with h | h
  · exact absurd h hSne
  · intro v
    have : v ∈ S := by rw [h]; trivial
    rw [hS, Module.End.mem_eigenspace_iff] at this
    exact this

section Abstract

variable {Vi Vf K : Type*}
  [AddCommGroup Vi] [Module ℂ Vi]
  [AddCommGroup Vf] [Module ℂ Vf] [FiniteDimensional ℂ Vf]
  [AddCommGroup K] [Module ℂ K]

/-- If the "coupled" space `Vi` splits equivariantly as `Vf ⊕ K` with `K` containing no
copy of `Vf`, then every intertwiner `Vi → Vf` is a scalar multiple of the projection onto
the `Vf`-summand. -/
theorem intertwiner_eq_smul_fst
    (ρi : Representation ℂ G Vi) (ρf : Representation ℂ G Vf) (ρK : Representation ℂ G K)
    (hirr : IsIrred ρf)
    (e : Vi ≃ₗ[ℂ] Vf × K)
    (he : ∀ (g : G) (v : Vi), e (ρi g v) = (ρf g (e v).1, ρK g (e v).2))
    (hmult : ∀ f : K →ₗ[ℂ] Vf, Intertwines ρK ρf f → f = 0)
    (A : Vi →ₗ[ℂ] Vf) (hA : Intertwines ρi ρf A) :
    ∃ a : ℂ, ∀ v : Vi, A v = a • (e v).1 := by
  -- equivariance of `e.symm`
  have hesymm : ∀ (g : G) (p : Vf × K),
      e.symm (ρf g p.1, ρK g p.2) = ρi g (e.symm p) := by
    intro g p
    have := he g (e.symm p)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← this, LinearEquiv.symm_apply_apply]
  -- restriction to the first summand
  set A₁ : Vf →ₗ[ℂ] Vf :=
    A ∘ₗ (e.symm : Vf × K →ₗ[ℂ] Vi) ∘ₗ LinearMap.inl ℂ Vf K with hA₁
  set A₂ : K →ₗ[ℂ] Vf :=
    A ∘ₗ (e.symm : Vf × K →ₗ[ℂ] Vi) ∘ₗ LinearMap.inr ℂ Vf K with hA₂
  have hA₁eq : Intertwines ρf ρf A₁ := by
    intro g y
    simp only [hA₁, LinearMap.comp_apply, LinearMap.inl_apply, LinearEquiv.coe_coe]
    have h0 : (ρf g y, (0 : K)) = (ρf g (y, (0 : K)).1, ρK g (y, (0 : K)).2) := by
      simp
    rw [h0, hesymm g (y, (0 : K)), hA]
  have hA₂eq : Intertwines ρK ρf A₂ := by
    intro g z
    simp only [hA₂, LinearMap.comp_apply, LinearMap.inr_apply, LinearEquiv.coe_coe]
    have h0 : ((0 : Vf), ρK g z) = (ρf g ((0 : Vf), z).1, ρK g ((0 : Vf), z).2) := by
      simp
    rw [h0, hesymm g ((0 : Vf), z), hA]
  obtain ⟨a, ha⟩ := schur_scalar ρf hirr A₁ hA₁eq
  have hA₂zero : A₂ = 0 := hmult A₂ hA₂eq
  refine ⟨a, ?_⟩
  intro v
  have hsplit : v = e.symm ((e v).1, 0) + e.symm (0, (e v).2) := by
    rw [← map_add]
    have : (((e v).1, (0 : K)) + ((0 : Vf), (e v).2)) = e v := by
      ext <;> simp
    rw [this, LinearEquiv.symm_apply_apply]
  calc A v = A (e.symm ((e v).1, 0)) + A (e.symm (0, (e v).2)) := by
        rw [← map_add, ← hsplit]
    _ = A₁ ((e v).1) + A₂ ((e v).2) := by
        simp only [hA₁, hA₂, LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
          LinearEquiv.coe_coe]
    _ = a • (e v).1 := by rw [ha, hA₂zero]; simp

/-- **Wigner–Eckart, abstract form.** In a multiplicity-free situation, any two intertwiners
from the coupled space `Vi` to the irreducible `Vf` are proportional: `T = r • C`, with `r`
(the *reduced matrix element*) uniquely determined. -/
theorem wigner_eckart_abstract
    (ρi : Representation ℂ G Vi) (ρf : Representation ℂ G Vf) (ρK : Representation ℂ G K)
    (hirr : IsIrred ρf)
    (e : Vi ≃ₗ[ℂ] Vf × K)
    (he : ∀ (g : G) (v : Vi), e (ρi g v) = (ρf g (e v).1, ρK g (e v).2))
    (hmult : ∀ f : K →ₗ[ℂ] Vf, Intertwines ρK ρf f → f = 0)
    (C T : Vi →ₗ[ℂ] Vf) (hC : Intertwines ρi ρf C) (hT : Intertwines ρi ρf T)
    (hC0 : C ≠ 0) :
    ∃! r : ℂ, ∀ v : Vi, T v = r • C v := by
  obtain ⟨c, hc⟩ := intertwiner_eq_smul_fst ρi ρf ρK hirr e he hmult C hC
  obtain ⟨t, ht⟩ := intertwiner_eq_smul_fst ρi ρf ρK hirr e he hmult T hT
  have hcne : c ≠ 0 := by
    rintro rfl
    apply hC0
    ext v
    simp [hc v]
  refine ⟨t / c, ?_, ?_⟩
  · intro v
    rw [ht v, hc v, smul_smul]
    congr 1
    field_simp
  · intro r hr
    obtain ⟨v, hv⟩ : ∃ v : Vi, C v ≠ 0 := by
      by_contra h
      push_neg at h
      exact hC0 (by ext v; simp [h v])
    have h1 : (t / c) • C v = r • C v := by
      rw [← hr v, ht v, hc v, smul_smul]
      congr 1
      field_simp
    have := sub_eq_zero.mpr h1
    rw [← sub_smul] at this
    rcases smul_eq_zero.mp this with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h hv

end Abstract

section TensorOperator

variable {Vk Vj Vf K : Type*}
  [AddCommGroup Vk] [Module ℂ Vk]
  [AddCommGroup Vj] [Module ℂ Vj]
  [AddCommGroup Vf] [Module ℂ Vf] [FiniteDimensional ℂ Vf]
  [AddCommGroup K] [Module ℂ K]

/-- **The Wigner–Eckart theorem.**

`Vk` carries the representation under which the components of a rank-`k` tensor operator
transform, `Vj` is the initial-state space and `Vf` the (irreducible) final-state space.
A *tensor operator* is a bilinear family `T : Vk → Vj → Vf`, `(q, m) ↦ T^k_q |j m⟩`,
whose defining covariance property is `T (ρk g q) (ρj g m) = ρf g (T q m)`
(equivalently `ρf g ∘ T_q ∘ ρj g⁻¹ = Σ_{q'} D^k_{q' q}(g) T_{q'}`).

The multiplicity-free hypothesis is that the coupled space `Vk ⊗ Vj` splits equivariantly as
`Vf ⊕ K`, where `K` carries no copy of `Vf`; `C` is the corresponding Clebsch–Gordan
intertwiner (any nonzero one).

Conclusion: there is a unique scalar `r` — the *reduced matrix element* `⟨j' ‖ T^k ‖ j⟩` —
such that every matrix element `⟨j' m' | T^k_q | j m⟩` equals the Clebsch–Gordan coefficient
`⟨j' m' | C (q ⊗ m)⟩` times `r`. -/
theorem wigner_eckart
    (ρk : Representation ℂ G Vk) (ρj : Representation ℂ G Vj)
    (ρf : Representation ℂ G Vf) (ρK : Representation ℂ G K)
    (hirr : IsIrred ρf)
    (e : (Vk ⊗[ℂ] Vj) ≃ₗ[ℂ] Vf × K)
    (he : ∀ (g : G) (v : Vk ⊗[ℂ] Vj),
      e ((Representation.tprod ρk ρj) g v) = (ρf g (e v).1, ρK g (e v).2))
    (hmult : ∀ f : K →ₗ[ℂ] Vf, Intertwines ρK ρf f → f = 0)
    (C T : Vk →ₗ[ℂ] Vj →ₗ[ℂ] Vf)
    (hC : ∀ (g : G) (q : Vk) (m : Vj), C (ρk g q) (ρj g m) = ρf g (C q m))
    (hT : ∀ (g : G) (q : Vk) (m : Vj), T (ρk g q) (ρj g m) = ρf g (T q m))
    (hC0 : C ≠ 0) :
    ∃! r : ℂ, ∀ (bra : Module.Dual ℂ Vf) (q : Vk) (m : Vj),
      bra (T q m) = r * bra (C q m) := by
  -- lift the tensor operators to the coupled space
  set CL : (Vk ⊗[ℂ] Vj) →ₗ[ℂ] Vf := TensorProduct.lift C with hCL
  set TL : (Vk ⊗[ℂ] Vj) →ₗ[ℂ] Vf := TensorProduct.lift T with hTL
  have lift_int : ∀ (F : Vk →ₗ[ℂ] Vj →ₗ[ℂ] Vf),
      (∀ (g : G) (q : Vk) (m : Vj), F (ρk g q) (ρj g m) = ρf g (F q m)) →
      Intertwines (Representation.tprod ρk ρj) ρf (TensorProduct.lift F) := by
    intro F hF g v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul q m =>
        show (TensorProduct.lift F) (TensorProduct.map (ρk g) (ρj g) (q ⊗ₜ m)) = _
        simp only [TensorProduct.map_tmul, TensorProduct.lift.tmul]
        exact hF g q m
    | add x y hx hy =>
        have hadd : (Representation.tprod ρk ρj) g (x + y)
            = (Representation.tprod ρk ρj) g x + (Representation.tprod ρk ρj) g y :=
          map_add _ _ _
        rw [hadd, map_add, hx, hy, map_add, map_add]
  have hCLint : Intertwines (Representation.tprod ρk ρj) ρf CL := lift_int C hC
  have hTLint : Intertwines (Representation.tprod ρk ρj) ρf TL := lift_int T hT
  have hCL0 : CL ≠ 0 := by
    intro h
    apply hC0
    ext q m
    have : CL (q ⊗ₜ m) = 0 := by rw [h]; rfl
    simpa [hCL] using this
  obtain ⟨r, hr, huniq⟩ :=
    wigner_eckart_abstract (Representation.tprod ρk ρj) ρf ρK hirr e he hmult CL TL
      hCLint hTLint hCL0
  have hrtmul : ∀ (q : Vk) (m : Vj), T q m = r • C q m := by
    intro q m
    have := hr (q ⊗ₜ m)
    simpa [hTL, hCL] using this
  refine ⟨r, ?_, ?_⟩
  · intro bra q m
    rw [hrtmul q m, map_smul]
    simp [smul_eq_mul]
  · intro r' hr'
    obtain ⟨q, m, hqm⟩ : ∃ (q : Vk) (m : Vj), C q m ≠ 0 := by
      by_contra h
      push_neg at h
      exact hC0 (by ext q m; simp [h q m])
    obtain ⟨bra, hbra⟩ := Module.Projective.exists_dual_ne_zero ℂ hqm
    have h1 : bra (T q m) = r' * bra (C q m) := hr' bra q m
    have h2 : bra (T q m) = r * bra (C q m) := by
      rw [hrtmul q m, map_smul]; simp [smul_eq_mul]
    have : r' * bra (C q m) = r * bra (C q m) := by rw [← h1, h2]
    exact mul_right_cancel₀ hbra this

end TensorOperator

end Phys

section Sanity

open TensorProduct

/-- Auxiliary isomorphism `ℂ ⊗ ℂ ≃ ℂ × 0` used in the non-vacuity check below. -/
noncomputable def sanityEquiv : (ℂ ⊗[ℂ] ℂ) ≃ₗ[ℂ] ℂ × PUnit.{1} :=
  (TensorProduct.lid ℂ ℂ).trans
    { toFun := fun x => (x, PUnit.unit)
      map_add' := by intro a b; apply Prod.ext <;> simp
      map_smul' := by intro c a; apply Prod.ext <;> simp
      invFun := Prod.fst
      left_inv := fun _ => rfl
      right_inv := fun _ => by apply Prod.ext <;> simp }

/-- Non-vacuity check: the hypotheses of `Phys.wigner_eckart` are satisfiable, here in the
simplest instance (trivial group, one-dimensional final space, `T = 3 • C`). -/
example : ∃! r : ℂ, ∀ (bra : Module.Dual ℂ ℂ) (q m : ℂ),
    bra (((3 : ℂ) • LinearMap.mul ℂ ℂ) q m) = r * bra ((LinearMap.mul ℂ ℂ) q m) := by
  refine Phys.wigner_eckart (G := Unit) (Vk := ℂ) (Vj := ℂ) (Vf := ℂ) (K := PUnit.{1})
    1 1 1 1 ⟨inferInstance, fun S _ => Ideal.eq_bot_or_top S⟩ sanityEquiv ?_ ?_
    (LinearMap.mul ℂ ℂ) ((3 : ℂ) • LinearMap.mul ℂ ℂ) ?_ ?_ ?_
  · intro g v
    simp
  · intro f _
    exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero]; rfl
  · intro g q m
    simp
  · intro g q m
    simp
  · intro h
    have : (LinearMap.mul ℂ ℂ) 1 1 = 0 := by rw [h]; rfl
    simp at this

end Sanity
#print axioms Phys.wigner_eckart
#print axioms Phys.wigner_eckart_abstract
#print axioms Phys.schur_scalar

