/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Statement: Matrix elements of tensor operators factor into a Clebsch–Gordan × reduced element (Wigner–Eckart).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Statement: Matrix elements of tensor operators factor into a Clebsch–Gordan × reduced element (Wigner–Eckart).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

* `Phys.Intertwines`, `Phys.IsIrrep` : equivariant maps and irreducible representations.
* `Phys.schur_scalar` : Schur's lemma (endomorphism form).
* `Phys.exists_scalar_of_ker_le` : uniqueness of intertwiners up to scale.
* `Phys.wigner_eckart` : the Wigner–Eckart theorem.
* `Phys.wigner_eckart_of_decomposition` : the same, with multiplicity one supplied as a
  direct-sum decomposition of the coupled space.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace Phys

variable {k G V W U : Type*}
  [Field k] [Group G]
  [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]

/-- `Intertwines ρ σ f` says that the linear map `f` is equivariant (a morphism of
representations) from `ρ` to `σ`: `f ∘ ρ g = σ g ∘ f` for all group elements `g`. -/

theorem surjective_of_ne_zero {ρX : Representation k G V} {ρU : Representation k G U}
    (hU : IsIrrep ρU) {C : V →ₗ[k] U} (hC : Intertwines ρX ρU C) (hC0 : C ≠ 0) :
    Function.Surjective C := by
  have hinv : ∀ (g : G), ∀ u ∈ LinearMap.range C, ρU g u ∈ LinearMap.range C := by
    rintro g _ ⟨v, rfl⟩
    exact ⟨ρX g v, hC g v⟩
  rcases hU.simple (LinearMap.range C) hinv with h | h
  · exact absurd (LinearMap.range_eq_bot.mp h) hC0
  · rw [← LinearMap.range_eq_top]; exact h

/-- **Schur's lemma, uniqueness of intertwiners up to scale.** If `C` and `T` are equivariant
maps into a finite-dimensional irreducible representation over an algebraically closed field,
`C ≠ 0`, and `T` vanishes wherever `C` does (the multiplicity-one hypothesis), then `T` is a
scalar multiple of `C`. -/
