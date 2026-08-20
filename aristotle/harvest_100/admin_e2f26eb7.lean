import Mathlib

/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Scope note.  Mathlib (at the version pinned by this project) contains no sunflower lemma:
searching for `sunflower` / `Sunflower` turns up nothing, and `exact?`/`apply?` have nothing
to offer on the statement below, so the development here is self-contained.

The bound proved as `Math2.sunflower_bound` is the classical Erdős–Rado bound
`k! * (r-1)^k`.  The Alweiss–Lovett–Wu–Zhang improvement to `(C * r * log k)^k` is *not*
established here; `Math2.sunflower_bound_pow` only records the convenient weakening
`(k * r)^k` of the Erdős–Rado bound.

`import Mathlib` has to precede the header comment above because Lean 4 requires `import`
commands to come first in a file (a `/-! -/` module docstring before them is rejected).
-/

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

set_option grind.warning false

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A family `S` of finite sets is a *sunflower* with core `core` when any two distinct
members of `S` meet exactly in `core`. -/
def IsSunflower (core : Finset α) (S : Finset (Finset α)) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = core

/-- A subfamily whose members are pairwise disjoint. -/
def PairwiseDisjointFamily (D : Finset (Finset α)) : Prop :=
  ∀ A ∈ D, ∀ B ∈ D, A ≠ B → A ∩ B = ∅

lemma isSunflower_empty_core {D : Finset (Finset α)} (hD : PairwiseDisjointFamily D)
    {S : Finset (Finset α)} (hS : S ⊆ D) : IsSunflower (∅ : Finset α) S := by
  intro A hA B hB hAB
  exact hD A (hS hA) B (hS hB) hAB

/-- There is a pairwise disjoint subfamily of maximal cardinality. -/
lemma exists_max_pairwise_disjoint (F : Finset (Finset α)) :
    ∃ D ⊆ F, PairwiseDisjointFamily D ∧
      ∀ D' ⊆ F, PairwiseDisjointFamily D' → D'.card ≤ D.card := by
  classical
  set P : Finset (Finset (Finset α)) :=
    (F.powerset).filter (fun D => PairwiseDisjointFamily D) with hP
  have hne : P.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [hP, PairwiseDisjointFamily]
  obtain ⟨D, hDmem, hDmax⟩ := P.exists_max_image Finset.card hne
  simp only [hP, Finset.mem_filter, Finset.mem_powerset] at hDmem
  refine ⟨D, hDmem.1, hDmem.2, ?_⟩
  intro D' hD' hD'disj
  exact hDmax D' (by simp [hP, Finset.mem_filter, Finset.mem_powerset, hD', hD'disj])

/-- **Erdős–Rado sunflower lemma.**  A `k`-uniform family with more than `k! (r-1)^k`
members contains a sunflower with `r` petals. -/
theorem sunflower_bound (k r : ℕ) (F : Finset (Finset α))
    (hk : ∀ A ∈ F, A.card = k) (hF : k ! * (r - 1) ^ k < F.card) :
    ∃ (core : Finset α) (S : Finset (Finset α)), S ⊆ F ∧ S.card = r ∧ IsSunflower core S := by
  classical
  induction k generalizing F with
  | zero =>
      -- every member is `∅`, so `F.card ≤ 1`, contradicting `1 < F.card`
      exfalso
      have hsub : F ⊆ {∅} := by
        intro A hA
        simp only [Finset.mem_singleton]
        exact Finset.card_eq_zero.mp (hk A hA)
      have hle := Finset.card_le_card hsub
      rw [Finset.card_singleton] at hle
      simp at hF
      omega
  | succ k ih =>
      obtain ⟨D, hDF, hDdisj, hDmax⟩ := exists_max_pairwise_disjoint F
      by_cases hDr : r ≤ D.card
      · -- a large disjoint subfamily is already a sunflower with empty core
        obtain ⟨S, hSD, hScard⟩ := Finset.exists_subset_card_eq hDr
        exact ⟨∅, S, hSD.trans hDF, hScard, isSunflower_empty_core hDdisj hSD⟩
      · push_neg at hDr
        -- every member of `F` meets `Y`
        set Y : Finset α := D.biUnion id with hY
        have hmeet : ∀ A ∈ F, ∃ y ∈ Y, y ∈ A := by
          intro A hA
          by_contra hcon
          push_neg at hcon
          have hAdisj : ∀ B ∈ D, A ∩ B = ∅ := by
            intro B hB
            rw [Finset.eq_empty_iff_forall_notMem]
            intro x hx
            rw [Finset.mem_inter] at hx
            exact hcon x (Finset.mem_biUnion.mpr ⟨B, hB, hx.2⟩) hx.1
          have hAnotD : A ∉ D := by
            intro hAD
            have hAcard : A.card = k + 1 := hk A hA
            obtain ⟨x, hx⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
            exact hcon x (Finset.mem_biUnion.mpr ⟨A, hAD, hx⟩) hx
          have hins : PairwiseDisjointFamily (insert A D) := by
            intro X hX Z hZ hXZ
            rcases Finset.mem_insert.mp hX with rfl | hX'
            · rcases Finset.mem_insert.mp hZ with rfl | hZ'
              · exact absurd rfl hXZ
              · exact hAdisj Z hZ'
            · rcases Finset.mem_insert.mp hZ with rfl | hZ'
              · rw [Finset.inter_comm]; exact hAdisj X hX'
              · exact hDdisj X hX' Z hZ' hXZ
          have := hDmax (insert A D) (Finset.insert_subset hA hDF) hins
          rw [Finset.card_insert_of_notMem hAnotD] at this
          omega
        -- some element of `Y` lies in many members
        have hYcard : Y.card ≤ D.card * (k + 1) := by
          calc Y.card ≤ ∑ B ∈ D, (id B).card := Finset.card_biUnion_le
          _ ≤ ∑ _B ∈ D, (k + 1) := by
                refine Finset.sum_le_sum ?_
                intro B hB
                exact le_of_eq (hk B (hDF hB))
          _ = D.card * (k + 1) := by simp
        have hsum : F.card ≤ ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card := by
          calc F.card = ∑ A ∈ F, 1 := by simp
          _ ≤ ∑ A ∈ F, (Y.filter (fun y => y ∈ A)).card := by
                refine Finset.sum_le_sum ?_
                intro A hA
                obtain ⟨y, hyY, hyA⟩ := hmeet A hA
                exact Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hyY, hyA⟩⟩
          _ = ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card := by
                simp only [Finset.card_filter]
                exact Finset.sum_comm
        obtain ⟨y, hyY, hy⟩ : ∃ y ∈ Y, Y.card * ((k)! * (r - 1) ^ k) <
            (F.filter (fun A => y ∈ A)).card * Y.card := by
          by_contra hcon
          push_neg at hcon
          have hYpos : 0 < Y.card := by
            rcases Finset.card_pos.mp (by omega : 0 < F.card) with ⟨A, hA⟩
            obtain ⟨y, hyY, -⟩ := hmeet A hA
            exact Finset.card_pos.mpr ⟨y, hyY⟩
          have hb : ∀ y ∈ Y, (F.filter (fun A => y ∈ A)).card ≤ (k)! * (r - 1) ^ k := by
            intro y hyY
            have := hcon y hyY
            exact Nat.le_of_mul_le_mul_right (by simpa [mul_comm] using this) hYpos
          have : F.card ≤ Y.card * ((k)! * (r - 1) ^ k) := by
            calc F.card ≤ ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card := hsum
            _ ≤ ∑ _y ∈ Y, ((k)! * (r - 1) ^ k) := Finset.sum_le_sum hb
            _ = Y.card * ((k)! * (r - 1) ^ k) := by simp
          have hchain : Y.card * ((k)! * (r - 1) ^ k) ≤
              (D.card * (k + 1)) * ((k)! * (r - 1) ^ k) :=
            Nat.mul_le_mul_right _ hYcard
          have hDle : D.card ≤ r - 1 := by omega
          have hchain2 : (D.card * (k + 1)) * ((k)! * (r - 1) ^ k) ≤
              ((r - 1) * (k + 1)) * ((k)! * (r - 1) ^ k) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hDle)
          have hfac : ((r - 1) * (k + 1)) * ((k)! * (r - 1) ^ k)
              = (k + 1)! * (r - 1) ^ (k + 1) := by
            rw [Nat.factorial_succ]
            ring
          omega
        -- the link at `y`
        set G : Finset (Finset α) :=
          (F.filter (fun A => y ∈ A)).image (fun A => A.erase y) with hG
        have hGcard : G.card = (F.filter (fun A => y ∈ A)).card := by
          rw [hG]
          refine Finset.card_image_of_injOn ?_
          intro A hA B hB hAB
          simp only [Finset.mem_coe, Finset.mem_filter] at hA hB
          have := congrArg (insert y) hAB
          rwa [Finset.insert_erase hA.2, Finset.insert_erase hB.2] at this
        have hGunif : ∀ B ∈ G, B.card = k := by
          intro B hB
          rw [hG] at hB
          obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
          simp only [Finset.mem_filter] at hA
          have := hk A hA.1
          rw [Finset.card_erase_of_mem hA.2]
          omega
        have hGbig : (k)! * (r - 1) ^ k < G.card := by
          rw [hGcard]
          have hYpos : 0 < Y.card := by
            by_contra h
            have : Y.card = 0 := by omega
            rw [this] at hy
            simp at hy
          exact lt_of_mul_lt_mul_right (by simpa [mul_comm] using hy) (Nat.zero_le _)
        obtain ⟨c, S', hS'G, hS'card, hS'sun⟩ := ih G hGunif hGbig
        -- lift the sunflower back
        have hynot : ∀ B ∈ S', y ∉ B := by
          intro B hB
          have := hS'G hB
          rw [hG] at this
          obtain ⟨A, -, rfl⟩ := Finset.mem_image.mp this
          exact Finset.notMem_erase y A
        refine ⟨insert y c, S'.image (fun B => insert y B), ?_, ?_, ?_⟩
        · intro A hA
          obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
          have hBG := hS'G hB
          rw [hG] at hBG
          obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hBG
          simp only [Finset.mem_filter] at hA'
          rw [Finset.insert_erase hA'.2]
          exact hA'.1
        · rw [Finset.card_image_of_injOn, hS'card]
          intro B hB B' hB' hEq
          simp only [Finset.mem_coe] at hB hB'
          have h1 : y ∉ B := hynot B hB
          have h2 : y ∉ B' := hynot B' hB'
          have hEq' : insert y B = insert y B' := hEq
          rw [← Finset.erase_insert h1, hEq', Finset.erase_insert h2]
        · intro A hA B hB hAB
          obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
          obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hB
          have hne : A' ≠ B' := by
            intro h; exact hAB (by rw [h])
          have := hS'sun A' hA' B' hB' hne
          ext x
          simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨hx1, hx2⟩
            rcases hx1 with rfl | hx1
            · exact Or.inl rfl
            · rcases hx2 with rfl | hx2
              · exact Or.inl rfl
              · exact Or.inr (by rw [← this]; exact Finset.mem_inter.mpr ⟨hx1, hx2⟩)
          · rintro (rfl | hx)
            · exact ⟨Or.inl rfl, Or.inl rfl⟩
            · rw [← this] at hx
              rw [Finset.mem_inter] at hx
              exact ⟨Or.inr hx.1, Or.inr hx.2⟩

/-- In a sunflower with at least two petals, the core is contained in every petal. -/
theorem IsSunflower.core_subset {core : Finset α} {S : Finset (Finset α)}
    (hS : IsSunflower core S) (hcard : 2 ≤ S.card) {A : Finset α} (hA : A ∈ S) :
    core ⊆ A := by
  classical
  obtain ⟨B, hB, hBA⟩ : ∃ B ∈ S, B ≠ A := by
    by_contra hcon
    push_neg at hcon
    have : S ⊆ {A} := by
      intro X hX
      simpa using hcon X hX
    have := Finset.card_le_card this
    simp at this
    omega
  have h := hS A hA B hB (Ne.symm hBA)
  rw [← h]
  exact Finset.inter_subset_left

/-- A convenient weakening of `Math2.sunflower_bound`: a `k`-uniform family with more than
`(k * r) ^ k` members contains a sunflower with `r` petals. -/
theorem sunflower_bound_pow (k r : ℕ) (F : Finset (Finset α))
    (hk : ∀ A ∈ F, A.card = k) (hF : (k * r) ^ k < F.card) :
    ∃ (core : Finset α) (S : Finset (Finset α)), S ⊆ F ∧ S.card = r ∧ IsSunflower core S := by
  refine sunflower_bound k r F hk (lt_of_le_of_lt ?_ hF)
  calc k ! * (r - 1) ^ k ≤ k ^ k * r ^ k :=
        Nat.mul_le_mul (Nat.factorial_le_pow k) (Nat.pow_le_pow_left (by omega) k)
  _ = (k * r) ^ k := (Nat.mul_pow k r k).symm

end Math2

