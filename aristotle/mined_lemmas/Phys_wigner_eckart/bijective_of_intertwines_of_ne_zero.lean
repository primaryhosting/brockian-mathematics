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

section

variable {G : Type*} [Group G]
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A complex representation is *irreducible* if the space is nontrivial and the only
subspaces invariant under the group action are `⊥` and `⊤`. -/

theorem bijective_of_intertwines_of_ne_zero {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (hρ : IsIrrep ρ) (hσ : IsIrrep σ)
    {S : V →ₗ[ℂ] W} (hS : Intertwines ρ σ S) (hS0 : S ≠ 0) :
    Function.Bijective S := by
  have hker : LinearMap.ker S = ⊥ := by
    rcases hρ.2 (LinearMap.ker S) (by
      intro g v hv
      simp only [LinearMap.mem_ker] at hv ⊢
      rw [hS g v, hv, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.mp h) hS0
  have hran : LinearMap.range S = ⊤ := by
    rcases hσ.2 (LinearMap.range S) (by
      rintro g _ ⟨v, rfl⟩
      exact ⟨ρ g v, hS g v⟩) with h | h
    · exact absurd (LinearMap.range_eq_bot.mp h) hS0
    · exact h
  exact ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hran⟩

/-- **Schur's lemma, quantitative form.**  Over `ℂ`, any two intertwiners between
finite-dimensional irreducible representations are proportional: if `S ≠ 0`, then
`T = c • S` for a unique scalar `c` (the *reduced matrix element*). -/
