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
