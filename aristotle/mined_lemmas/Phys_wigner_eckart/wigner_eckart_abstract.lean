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
