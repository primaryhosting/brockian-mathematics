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

theorem not_model_ZFCTheory_of_subsingleton {M : Type*} [setLang.Structure M] [Nonempty M]
    [Subsingleton M] : ¬ (M ⊨ ZFCTheory) := by
  intro hM
  have hE : M ⊨ axEmpty := hM.realize_of_mem _ (by
    simp only [ZFCTheory, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto)
  have hP : M ⊨ axPair := hM.realize_of_mem _ (by
    simp only [ZFCTheory, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto)
  rw [realize_axEmpty] at hE
  rw [realize_axPair] at hP
  obtain ⟨x, hx⟩ := hE
  obtain ⟨y, hy⟩ := hP x x
  exact hx x (Subsingleton.elim y x ▸ (hy x).2 (Or.inl rfl))

/-- Consequently, `Con(ZFC + φ) → Con(ZFC)` for any sentence `φ`; in particular for the
statement that an inaccessible cardinal exists. -/
