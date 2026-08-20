import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Frontier

open FirstOrder Language ZFSet Ordinal Cardinal Order

/-! ## The first-order language of set theory -/

/-- The relation symbols of the language of set theory: a single binary symbol `∈`. -/
inductive memRelSym : ℕ → Type
  | mem : memRelSym 2

/-- The first-order language of set theory: no function symbols, one binary relation `∈`. -/

theorem model_axFound : VSet o ⊨ axFound := by
  rw [realize_axFound]
  rintro x ⟨y0, hy0⟩
  simp only [memR_VSet] at hy0
  have hne : (x : ZFSet) ≠ ∅ := by
    intro h
    rw [h] at hy0
    exact ZFSet.notMem_empty _ hy0
  obtain ⟨y, hy, hinter⟩ := ZFSet.regularity (x : ZFSet) hne
  refine ⟨⟨y, mem_mem_V x.2 hy⟩, hy, fun z => ?_⟩
  rintro ⟨hzy, hzx⟩
  have hmem : (z : ZFSet) ∈ (x : ZFSet) ∩ y := ZFSet.mem_inter.2 ⟨hzx, hzy⟩
  rw [hinter] at hmem
  exact ZFSet.notMem_empty _ hmem

