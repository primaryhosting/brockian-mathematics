/-
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
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

set_option grind.warning false

namespace Frontier

/-!
## The set-up

Let `X` be a smooth complex projective variety and let `p : ℤ`.  The Hodge conjecture
concerns the rational cohomology group `V = H^{2p}(X, ℚ)`, which carries a rational
Hodge structure of weight `2p`: its complexification `ℂ ⊗[ℚ] V ≃ H^{2p}(X, ℂ)`
decomposes as an internal direct sum of the Hodge pieces `H^{i, 2p-i}`, and complex
conjugation on the complexification interchanges `H^{i, 2p-i}` and `H^{2p-i, i}`.

The group of *Hodge classes* is `Hdg^p(X) = V ∩ H^{p,p}`, the set of rational classes
whose image in the complexification lies in the middle piece.  The group of *algebraic
classes* is the ℚ-span of the cycle classes of the codimension-`p` algebraic subvarieties
of `X`; it is contained in `Hdg^p(X)`.

Since Mathlib contains neither the singular cohomology of a complex variety nor the cycle
class map, we axiomatise exactly this data: a `Frontier.HodgeDatum V p` records the
rational Hodge structure of weight `2p` on `V` together with the subspace of algebraic
classes and the (elementary) fact that algebraic classes are Hodge classes.  The Hodge
conjecture is then the statement `Frontier.HodgeConjecture`, namely that every Hodge class
is algebraic.
-/

section Complexification

variable (V : Type*) [AddCommGroup V] [Module ℚ V]

/-- Complex conjugation on the complexification `ℂ ⊗[ℚ] V` of a rational vector space `V`,
i.e. the map `z ⊗ v ↦ conj z ⊗ v`.  It is only `ℚ`-linear (it is conjugate-linear over `ℂ`). -/

theorem isInternal_prod (A : ι → Submodule R M) (B : ι → Submodule R N)
    (hA : DirectSum.IsInternal A) (hB : DirectSum.IsInternal B) :
    DirectSum.IsInternal (fun i => (A i).prod (B i)) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hA hB ⊢
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  constructor
  · intro i
    rw [Submodule.disjoint_def]
    rintro ⟨x, y⟩ hxy hsup
    have hle : (⨆ j, ⨆ (_ : j ≠ i), (A j).prod (B j)) ≤
        (⨆ j, ⨆ (_ : j ≠ i), A j).prod (⨆ j, ⨆ (_ : j ≠ i), B j) :=
      iSup_le fun j => iSup_le fun hj => Submodule.prod_mono
        (le_iSup_of_le j (le_iSup_of_le hj le_rfl)) (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
    have hsup' := hle hsup
    rw [Submodule.mem_prod] at hsup' hxy
    have hx : x = 0 := (Submodule.disjoint_def.mp (hA1 i)) x hxy.1 hsup'.1
    have hy : y = 0 := (Submodule.disjoint_def.mp (hB1 i)) y hxy.2 hsup'.2
    simp [hx, hy]
  · refine le_antisymm le_top ?_
    rw [← LinearMap.sup_range_inl_inr (R := R) (M := M) (M₂ := N)]
    refine sup_le ?_ ?_
    · rw [← Submodule.map_top (LinearMap.inl R M N), ← hA2, Submodule.map_iSup]
      refine iSup_le fun j => le_iSup_of_le j ?_
      rintro z ⟨a, ha, rfl⟩
      exact ⟨ha, by simp⟩
    · rw [← Submodule.map_top (LinearMap.inr R M N), ← hB2, Submodule.map_iSup]
      refine iSup_le fun j => le_iSup_of_le j ?_
      rintro z ⟨b, hb, rfl⟩
      exact ⟨by simp, hb⟩

/-- Equality of products of submodules is equality of the factors. -/
