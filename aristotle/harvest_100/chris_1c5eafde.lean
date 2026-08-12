/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The header block above is kept verbatim, except that it is written as an ordinary comment
(`/- ... -/`) rather than a module docstring (`/-! ... -/`), since Lean 4 does not allow a
module docstring to precede the `import` line.

This file proves the sunflower lemma: a family of more than `w ! * (r-1) ^ w` sets of size `w`
contains a sunflower with `r` petals (`Math2.sunflower_bound`), together with the weaker but
tidier bound `(r * w) ^ w` (`Math2.sunflower_bound_pow`). The bound obtained here is the
classical Erdős–Rado one; the Alweiss–Lovett–Wu–Zhang improvement to `(C r log w) ^ w` is not
formalized.
-/

open scoped BigOperators
open scoped Nat

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A family `S` of finite sets is a *sunflower* (or *Δ-system*) with core `core` when the
core is contained in every member of `S` and any two distinct members of `S` intersect
exactly in `core`. -/
def IsSunflower (S : Finset (Finset α)) (core : Finset α) : Prop :=
  (∀ A ∈ S, core ⊆ A) ∧ (∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = core)

/-- Auxiliary Erdős–Rado induction, with `k = r - 1` petals-minus-one. -/
theorem sunflower_aux (k : ℕ) :
    ∀ (w : ℕ) (F : Finset (Finset α)), (∀ A ∈ F, A.card = w) → w ! * k ^ w < F.card →
      ∃ S ⊆ F, ∃ core : Finset α, S.card = k + 1 ∧ IsSunflower S core := by
  intro w
  induction w with
  | zero =>
    intro F hw hcard
    exfalso
    have hsub : F ⊆ {∅} := by
      intro A hA
      simp [Finset.card_eq_zero.mp (hw A hA)]
    have := Finset.card_le_card hsub
    simp at this hcard
    omega
  | succ w ih =>
    intro F hw hcard
    classical
    -- the collection of pairwise disjoint subfamilies of `F`
    set D : Finset (Finset (Finset α)) :=
      F.powerset.filter (fun S => ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = ∅) with hD
    have hDne : D.Nonempty := ⟨∅, by simp [hD]⟩
    obtain ⟨T, hTD, hTmax⟩ := Finset.exists_max_image D Finset.card hDne
    rw [hD, Finset.mem_filter, Finset.mem_powerset] at hTD
    obtain ⟨hTF, hTdisj⟩ := hTD
    by_cases hbig : k + 1 ≤ T.card
    · -- many pairwise disjoint sets: a sunflower with empty core
      obtain ⟨S, hST, hScard⟩ := Finset.exists_subset_card_eq hbig
      exact ⟨S, hST.trans hTF, ∅, hScard, fun A _ => Finset.empty_subset A,
        fun A hA B hB hAB => hTdisj A (hST hA) B (hST hB) hAB⟩
    · -- otherwise every member of `F` meets the small set `Y`
      push_neg at hbig
      have hTcard : T.card ≤ k := by omega
      set Y : Finset α := T.biUnion id with hY
      have hmeet : ∀ A ∈ F, ∃ y ∈ Y, y ∈ A := by
        intro A hA
        by_contra hcon
        push_neg at hcon
        have hAne : A ≠ ∅ := by
          intro h
          have := hw A hA
          rw [h] at this
          simp at this
        have hdisj : ∀ B ∈ T, A ∩ B = ∅ := by
          intro B hB
          ext x
          simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
          intro hxA hxB
          exact hcon x (by simp [hY]; exact ⟨B, hB, hxB⟩) hxA
        have hAT : A ∉ T := by
          intro hAT
          exact hAne (by simpa using hdisj A hAT)
        have : insert A T ∈ D := by
          rw [hD, Finset.mem_filter, Finset.mem_powerset]
          refine ⟨Finset.insert_subset hA hTF, ?_⟩
          intro X hX Z hZ hXZ
          rcases Finset.mem_insert.mp hX with hXA | hXT
          · rcases Finset.mem_insert.mp hZ with hZA | hZT
            · exact absurd (hXA.trans hZA.symm) hXZ
            · rw [hXA]; exact hdisj Z hZT
          · rcases Finset.mem_insert.mp hZ with hZA | hZT
            · rw [hZA, Finset.inter_comm]; exact hdisj X hXT
            · exact hTdisj X hXT Z hZT hXZ
        have := hTmax _ this
        rw [Finset.card_insert_of_notMem hAT] at this
        omega
      have hYcard : Y.card ≤ k * (w + 1) := by
        calc Y.card ≤ ∑ B ∈ T, (id B).card := Finset.card_biUnion_le
          _ = ∑ B ∈ T, (w + 1) := Finset.sum_congr rfl (fun B hB => hw B (hTF hB))
          _ = T.card * (w + 1) := by simp [Finset.sum_const]
          _ ≤ k * (w + 1) := Nat.mul_le_mul_right _ hTcard
      -- pigeonhole: some element lies in many members of `F`
      have hFsum : F.card ≤ ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card := by
        calc F.card ≤ (Y.biUnion (fun y => F.filter (fun A => y ∈ A))).card := by
              apply Finset.card_le_card
              intro A hA
              obtain ⟨y, hyY, hyA⟩ := hmeet A hA
              exact Finset.mem_biUnion.mpr ⟨y, hyY, Finset.mem_filter.mpr ⟨hA, hyA⟩⟩
          _ ≤ _ := Finset.card_biUnion_le
      have hex : ∃ y ∈ Y, w ! * k ^ w < (F.filter (fun A => y ∈ A)).card := by
        by_contra hcon
        push_neg at hcon
        have h1 : ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card ≤ Y.card * (w ! * k ^ w) := by
          calc ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card ≤ ∑ _y ∈ Y, (w ! * k ^ w) :=
                Finset.sum_le_sum (fun y hy => hcon y hy)
            _ = Y.card * (w ! * k ^ w) := by simp [Finset.sum_const, mul_comm]
        have h2 : Y.card * (w ! * k ^ w) ≤ (w + 1)! * k ^ (w + 1) := by
          calc Y.card * (w ! * k ^ w) ≤ (k * (w + 1)) * (w ! * k ^ w) :=
                Nat.mul_le_mul_right _ hYcard
            _ = (w + 1)! * k ^ (w + 1) := by
                rw [Nat.factorial_succ]; ring
        omega
      obtain ⟨y, hyY, hy⟩ := hex
      -- pass to the link of `y`
      set G : Finset (Finset α) := F.filter (fun A => y ∈ A) with hG
      set F' : Finset (Finset α) := G.image (fun A => A.erase y) with hF'
      have hinj : Set.InjOn (fun A => A.erase y) (G : Set (Finset α)) := by
        intro A hA B hB hAB
        simp only [hG, Finset.coe_filter, Set.mem_setOf_eq] at hA hB
        have := congrArg (insert y) hAB
        simpa [Finset.insert_erase hA.2, Finset.insert_erase hB.2] using this
      have hF'card : F'.card = G.card := Finset.card_image_of_injOn hinj
      have hF'w : ∀ B ∈ F', B.card = w := by
        intro B hB
        rw [hF', Finset.mem_image] at hB
        obtain ⟨A, hA, rfl⟩ := hB
        rw [hG, Finset.mem_filter] at hA
        rw [Finset.card_erase_of_mem hA.2, hw A hA.1]
        omega
      obtain ⟨S', hS'F', c, hS'card, hS'core, hS'sun⟩ := ih F' hF'w (by rw [hF'card]; exact hy)
      have hyS' : ∀ B ∈ S', y ∉ B := by
        intro B hB
        have := hS'F' hB
        rw [hF', Finset.mem_image] at this
        obtain ⟨A, _, rfl⟩ := this
        simp
      refine ⟨S'.image (insert y), ?_, insert y c, ?_, ?_, ?_⟩
      · intro X hX
        rw [Finset.mem_image] at hX
        obtain ⟨B, hB, rfl⟩ := hX
        have := hS'F' hB
        rw [hF', Finset.mem_image] at this
        obtain ⟨A, hA, rfl⟩ := this
        rw [hG, Finset.mem_filter] at hA
        rw [Finset.insert_erase hA.2]
        exact hA.1
      · rw [Finset.card_image_of_injOn, hS'card]
        intro B hB C hC hBC
        have hB' := hyS' B hB
        have hC' := hyS' C hC
        have := congrArg (fun s => Finset.erase s y) hBC
        simpa [Finset.erase_insert hB', Finset.erase_insert hC'] using this
      · intro X hX
        rw [Finset.mem_image] at hX
        obtain ⟨B, hB, rfl⟩ := hX
        exact Finset.insert_subset_insert y (hS'core B hB)
      · intro X hX Z hZ hXZ
        rw [Finset.mem_image] at hX hZ
        obtain ⟨B, hB, rfl⟩ := hX
        obtain ⟨C, hC, rfl⟩ := hZ
        have hBC : B ≠ C := by rintro rfl; exact hXZ rfl
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨hx1, hx2⟩
          rcases hx1 with rfl | hx1
          · left; rfl
          · rcases hx2 with rfl | hx2
            · left; rfl
            · right
              have : x ∈ B ∩ C := Finset.mem_inter.mpr ⟨hx1, hx2⟩
              rwa [hS'sun B hB C hC hBC] at this
        · rintro (rfl | hx)
          · exact ⟨Or.inl rfl, Or.inl rfl⟩
          · rw [← hS'sun B hB C hC hBC] at hx
            exact ⟨Or.inr (Finset.mem_inter.mp hx).1, Or.inr (Finset.mem_inter.mp hx).2⟩

/-- **The sunflower bound (Erdős–Rado sunflower lemma).**

If `F` is a family of sets each of size exactly `w` and `F` has more than `w ! * (r-1)^w`
members, then `F` contains a sunflower with `r` petals: a subfamily `S ⊆ F` of `r` sets and a
`core` contained in each of them such that any two distinct members of `S` meet exactly in
`core`.

Note on the bound: this is the classical Erdős–Rado bound `w ! (r-1)^w`. The
Alweiss–Lovett–Wu–Zhang improvement replaces it by `(C r log w)^w`; that improvement is *not*
formalized here. -/
theorem sunflower_bound (w r : ℕ) (hr : 1 ≤ r) (F : Finset (Finset α))
    (hw : ∀ A ∈ F, A.card = w) (hcard : w ! * (r - 1) ^ w < F.card) :
    ∃ S ⊆ F, ∃ core : Finset α, S.card = r ∧ IsSunflower S core := by
  obtain ⟨S, hSF, core, hcardS, hsun⟩ := sunflower_aux (r - 1) w F hw hcard
  exact ⟨S, hSF, core, by omega, hsun⟩

/-- A convenient weaker form of the sunflower bound: more than `(r * w) ^ w` sets of size `w`
already force a sunflower with `r` petals. -/
theorem sunflower_bound_pow (w r : ℕ) (hr : 1 ≤ r) (F : Finset (Finset α))
    (hw : ∀ A ∈ F, A.card = w) (hcard : (r * w) ^ w < F.card) :
    ∃ S ⊆ F, ∃ core : Finset α, S.card = r ∧ IsSunflower S core := by
  refine sunflower_bound w r hr F hw (lt_of_le_of_lt ?_ hcard)
  calc w ! * (r - 1) ^ w ≤ w ^ w * r ^ w :=
        Nat.mul_le_mul (Nat.factorial_le_pow w) (Nat.pow_le_pow_left (by omega) w)
    _ = (r * w) ^ w := by rw [mul_pow]; ring

end Math2

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

