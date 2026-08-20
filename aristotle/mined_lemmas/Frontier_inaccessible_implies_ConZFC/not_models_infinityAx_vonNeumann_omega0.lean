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

theorem not_models_infinityAx_vonNeumann_omega0 :
    ¬ ((vonNeumann Ordinal.omega0.{0} : Type 1) ⊨ infinityAx) := by
  rw [infinityAx]; realize_simp
  intro a e hea _ _ haV
  have htr : (vonNeumann Ordinal.omega0.{0}).IsTransitive := isTransitive_vonNeumann _
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (ZFSet.mem_vonNeumann.mp haV)
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := by
    cases n with
    | zero =>
      exfalso
      have hlt := ZFSet.rank_lt_of_mem hea
      rw [hn] at hlt
      simp at hlt
    | succ m => exact ⟨m, rfl⟩
  obtain ⟨y, hya, hym⟩ : ∃ y ∈ a, ((m : Ordinal)) ≤ ZFSet.rank y := by
    refine ZFSet.lt_rank_iff.mp ?_
    rw [hn]
    exact_mod_cast Nat.lt_succ_self m
  have hylt : ZFSet.rank y < ((m : Ordinal) + 1) := by
    have hlt := ZFSet.rank_lt_of_mem hya
    rw [hn] at hlt
    exact_mod_cast hlt
  have hyrank : ZFSet.rank y = (m : Ordinal) :=
    le_antisymm (by rwa [← Order.succ_eq_add_one, Order.lt_succ_iff] at hylt) hym
  refine ⟨y, htr a haV hya, hya, ?_⟩
  intro s hsa hsV
  by_contra hcon
  push_neg at hcon
  have hseq : s = insert y y := by
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hw
      have := (hcon w (htr s hsV hw)).1 hw
      tauto
    · intro hw
      have hwV : w ∈ vonNeumann Ordinal.omega0.{0} := by
        rcases hw with rfl | hw
        · exact htr a haV hya
        · exact htr _ (htr a haV hya) hw
      exact (hcon w hwV).2 (by tauto)
  have hrs : ZFSet.rank s = (m : Ordinal) + 1 := by
    rw [hseq, ZFSet.rank_insert, hyrank, max_eq_left (Order.le_succ _), Order.succ_eq_add_one]
  have hlt := ZFSet.rank_lt_of_mem hsa
  rw [hn, hrs] at hlt
  exact absurd hlt (lt_irrefl _)

end Frontier

import Mathlib

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

