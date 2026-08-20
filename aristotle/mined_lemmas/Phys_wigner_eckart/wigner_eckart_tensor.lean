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
