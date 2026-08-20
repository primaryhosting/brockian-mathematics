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

theorem model_axInf (hω : ω < o) : VSet o ⊨ axInf := by
  rw [realize_axInf]
  have hVω : V_ (ω : Ordinal.{u}) ∈ V_ o := vonNeumann_omega_mem_V hω
  have hemp : (∅ : ZFSet.{u}) ∈ V_ (ω : Ordinal.{u}) := empty_mem_V omega0_pos
  refine ⟨⟨V_ (ω : Ordinal.{u}), hVω⟩,
    ⟨⟨∅, mem_mem_V hVω hemp⟩, hemp, fun y => ZFSet.notMem_empty _⟩, ?_⟩
  intro y hy
  have hins : insert (y : ZFSet) (y : ZFSet) ∈ V_ (ω : Ordinal.{u}) :=
    insert_mem_V isSuccLimit_omega0 hy hy
  refine ⟨⟨insert (y : ZFSet) (y : ZFSet), mem_mem_V hVω hins⟩, hins, fun w => ?_⟩
  simp [ZFSet.mem_insert_iff, or_comm]

