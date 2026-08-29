import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

open Finset Matrix

/-! ## Part A: the 0/1 permanent as a counting problem -/

/-- For a 0/1 matrix, the permanent counts the permutations supported on the matrix, i.e. the
perfect matchings of the associated bipartite graph (equivalently, the cycle covers of the
associated digraph). -/

lemma toPermV_injective :
    Function.Injective
      (fun p : (π : Equiv.Perm (Fin n)) × (∀ i, Fin (A i (π i))) => toPermV A p.1 p.2) := by
  rintro ⟨π₁, k₁⟩ ⟨π₂, k₂⟩ h
  simp only at h
  have hcell : ∀ i, cellOf A π₁ k₁ i = cellOf A π₂ k₂ i := by
    intro i
    have h1 := (Equiv.ext_iff.mp h) (Sum.inl i)
    rw [toPermV_inl, toPermV_inl] at h1
    exact Sum.inr.inj h1
  have hπ : π₁ = π₂ :=
    Equiv.ext fun i => congrArg (fun c : Cells A => c.1.2) (hcell i)
  subst hπ
  have hk : k₁ = k₂ := by
    funext i
    have := hcell i
    simpa [cellOf, Sigma.mk.injEq] using this
  simp [hk]

