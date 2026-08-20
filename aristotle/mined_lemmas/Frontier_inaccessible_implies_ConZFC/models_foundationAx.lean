import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Frontier

open FirstOrder Language ZFSet Ordinal Cardinal Order Set

/-! ## Cardinal arithmetic of the von Neumann hierarchy below an inaccessible -/

variable {κ : Cardinal.{u}}

/-- Below an inaccessible cardinal `κ`, all the beth-numbers are smaller than `κ`. -/

theorem models_foundationAx (hA : A.IsTransitive) : (A : Type (u+1)) ⊨ foundationAx := by
  rw [foundationAx]; realize_simp
  intro a ha x _ hxa
  have hne : a ≠ ∅ := by
    intro h
    rw [h] at hxa
    exact ZFSet.notMem_empty x hxa
  obtain ⟨y, hy, hint⟩ := ZFSet.regularity a hne
  refine ⟨y, hy, hA a ha hy, fun c _ hca hcy => ?_⟩
  have hmem : c ∈ a ∩ y := ZFSet.mem_inter.mpr ⟨hca, hcy⟩
  rw [hint] at hmem
  exact ZFSet.notMem_empty c hmem

