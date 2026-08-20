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
