/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- `IsSunflower T c` says that the family `T` is a *sunflower* with *core* `c`:
any two distinct members of `T` intersect exactly in `c`.  (The members of `T`
minus the core are the *petals*, and they are pairwise disjoint.) -/
def IsSunflower (T : Finset (Finset α)) (c : Finset α) : Prop :=
  ∀ A ∈ T, ∀ B ∈ T, A ≠ B → A ∩ B = c

/-- A family with at most one member is a sunflower (vacuously), with core `∅`. -/
theorem isSunflower_of_card_le_one {T : Finset (Finset α)} (h : T.card ≤ 1) :
    IsSunflower T ∅ := by
  intro A hA B hB hAB
  exact absurd (Finset.card_le_one.mp h A hA B hB) hAB

/-- Double counting: every member of `F` meets `Y`, hence `|F|` is at most the sum over
`y ∈ Y` of the number of members of `F` containing `y`. -/
theorem card_le_sum_filter {F : Finset (Finset α)} {Y : Finset α}
    (h : ∀ A ∈ F, (A ∩ Y).Nonempty) :
    F.card ≤ ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card := by
  classical
  have key : ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card
      = ∑ A ∈ F, (Y.filter (fun y => y ∈ A)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [key]
  calc F.card = ∑ _A ∈ F, 1 := by simp
    _ ≤ ∑ A ∈ F, (Y.filter (fun y => y ∈ A)).card := by
        refine Finset.sum_le_sum ?_
        intro A hA
        obtain ⟨y, hy⟩ := h A hA
        rw [Finset.mem_inter] at hy
        exact Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hy.2, hy.1⟩⟩

/-- **Erdős–Rado sunflower lemma.**  A family of more than `w ! * (r-1)^w` sets, each of
size `w`, contains a sunflower with `r` petals. -/
theorem sunflower_erdos_rado (r : ℕ) :
    ∀ (w : ℕ) (F : Finset (Finset α)), (∀ A ∈ F, A.card = w) →
      w ! * (r - 1) ^ w < F.card → ∃ T ⊆ F, T.card = r ∧ ∃ c, IsSunflower T c := by
  classical
  intro w
  induction w with
  | zero =>
      intro F hsize hcard
      exfalso
      have hsub : F ⊆ {∅} := by
        intro A hA
        simp [Finset.card_eq_zero.mp (hsize A hA)]
      have h1 := Finset.card_le_card hsub
      simp only [Finset.card_singleton, Nat.factorial_zero, pow_zero, mul_one] at h1 hcard
      omega
  | succ w ih =>
      intro F hsize hcard
      by_cases hr : r ≤ 1
      · -- trivial cases `r = 0` and `r = 1`
        have hrF : r ≤ F.card := by
          interval_cases r
          · exact Nat.zero_le _
          · simpa using hcard
        obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hrF
        exact ⟨T, hTsub, hTcard, ∅, isSunflower_of_card_le_one (by omega)⟩
      push_neg at hr
      -- a maximum-size pairwise disjoint subfamily
      obtain ⟨M, hMP, hMmax⟩ :=
        Finset.exists_max_image ((F.powerset).filter (fun M => IsSunflower M ∅))
          (fun M => M.card) ⟨∅, by simp [IsSunflower]⟩
      rw [Finset.mem_filter, Finset.mem_powerset] at hMP
      obtain ⟨hMsub, hMdisj⟩ := hMP
      by_cases hMr : r ≤ M.card
      · obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hMr
        refine ⟨T, hTsub.trans hMsub, hTcard, ∅, ?_⟩
        intro A hA B hB hAB
        exact hMdisj A (hTsub hA) B (hTsub hB) hAB
      push_neg at hMr
      set Y : Finset α := M.biUnion id with hYdef
      have hYcard : Y.card ≤ (r - 1) * (w + 1) := by
        calc Y.card ≤ ∑ A ∈ M, (id A).card := Finset.card_biUnion_le
          _ = ∑ _A ∈ M, (w + 1) := by
              refine Finset.sum_congr rfl (fun A hA => hsize A (hMsub hA))
          _ = M.card * (w + 1) := by simp
          _ ≤ (r - 1) * (w + 1) := by
              exact Nat.mul_le_mul_right _ (by omega)
      have hmeet : ∀ A ∈ F, (A ∩ Y).Nonempty := by
        intro A hA
        by_contra hcon
        rw [Finset.not_nonempty_iff_eq_empty] at hcon
        have hAne : A.Nonempty := by
          rw [← Finset.card_pos, hsize A hA]; omega
        have hAM : A ∉ M := by
          intro hAM
          obtain ⟨x, hx⟩ := hAne
          have : x ∈ A ∩ Y := Finset.mem_inter.mpr ⟨hx, Finset.mem_biUnion.mpr ⟨A, hAM, hx⟩⟩
          simp [hcon] at this
        have hins : insert A M ∈ (F.powerset).filter (fun M => IsSunflower M ∅) := by
          rw [Finset.mem_filter, Finset.mem_powerset]
          refine ⟨Finset.insert_subset hA hMsub, ?_⟩
          have hAdisj : ∀ B ∈ M, A ∩ B = ∅ := by
            intro B hB
            rw [Finset.eq_empty_iff_forall_notMem]
            intro x hx
            rw [Finset.mem_inter] at hx
            have : x ∈ A ∩ Y :=
              Finset.mem_inter.mpr ⟨hx.1, Finset.mem_biUnion.mpr ⟨B, hB, hx.2⟩⟩
            simp [hcon] at this
          intro B hB C hC hBC
          rw [Finset.mem_insert] at hB hC
          rcases hB with rfl | hB
          · rcases hC with rfl | hC
            · exact absurd rfl hBC
            · exact hAdisj C hC
          · rcases hC with rfl | hC
            · rw [Finset.inter_comm]; exact hAdisj B hB
            · exact hMdisj B hB C hC hBC
        have := hMmax _ hins
        rw [Finset.card_insert_of_notMem hAM] at this
        omega
      -- pigeonhole: some element of `Y` lies in many members of `F`
      have hpig : ∃ y ∈ Y, w ! * (r - 1) ^ w < (F.filter (fun A => y ∈ A)).card := by
        by_contra hcon
        push_neg at hcon
        have h1 := card_le_sum_filter hmeet
        have h2 : ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card ≤ Y.card * (w ! * (r - 1) ^ w) := by
          calc ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card
              ≤ ∑ _y ∈ Y, (w ! * (r - 1) ^ w) := Finset.sum_le_sum hcon
            _ = Y.card * (w ! * (r - 1) ^ w) := by simp
        have h3 : Y.card * (w ! * (r - 1) ^ w) ≤ (w + 1)! * (r - 1) ^ (w + 1) := by
          calc Y.card * (w ! * (r - 1) ^ w) ≤ ((r - 1) * (w + 1)) * (w ! * (r - 1) ^ w) :=
                Nat.mul_le_mul_right _ hYcard
            _ = ((w + 1) * w !) * ((r - 1) ^ w * (r - 1)) := by ring
            _ = (w + 1)! * (r - 1) ^ (w + 1) := by
                rw [Nat.factorial_succ, pow_succ]
        omega
      obtain ⟨y, hyY, hy⟩ := hpig
      set Fy : Finset (Finset α) := F.filter (fun A => y ∈ A) with hFydef
      set G : Finset (Finset α) := Fy.image (fun A => A.erase y) with hGdef
      have hGcard : G.card = Fy.card := by
        refine Finset.card_image_of_injOn ?_
        intro A hA B hB hAB
        have hyA : y ∈ A := (Finset.mem_filter.mp hA).2
        have hyB : y ∈ B := (Finset.mem_filter.mp hB).2
        have h := congrArg (fun s : Finset α => insert y s) hAB
        simpa [Finset.insert_erase hyA, Finset.insert_erase hyB] using h
      have hGsize : ∀ B ∈ G, B.card = w := by
        intro B hB
        obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
        have hyA : y ∈ A := (Finset.mem_filter.mp hA).2
        have hAF : A ∈ F := (Finset.mem_filter.mp hA).1
        rw [Finset.card_erase_of_mem hyA, hsize A hAF]
        omega
      obtain ⟨T', hT'sub, hT'card, c, hc⟩ := ih G hGsize (by rw [hGcard]; exact hy)
      have hynot : ∀ B ∈ T', y ∉ B := by
        intro B hB
        obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp (hT'sub hB)
        exact Finset.notMem_erase y A
      refine ⟨T'.image (fun B => insert y B), ?_, ?_, insert y c, ?_⟩
      · intro X hX
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hX
        obtain ⟨A, hA, hAB⟩ := Finset.mem_image.mp (hT'sub hB)
        have hyA : y ∈ A := (Finset.mem_filter.mp hA).2
        rw [← hAB, Finset.insert_erase hyA]
        exact (Finset.mem_filter.mp hA).1
      · rw [← hT'card]
        refine Finset.card_image_of_injOn ?_
        intro B hB C hC hBC
        have h1 : y ∉ B := hynot B hB
        have h2 : y ∉ C := hynot C hC
        have h := congrArg (fun s : Finset α => s.erase y) hBC
        simpa [Finset.erase_insert h1, Finset.erase_insert h2] using h
      · intro X hX Z hZ hXZ
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hX
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hZ
        have hBC : B ≠ C := by
          intro h; exact hXZ (by rw [h])
        have hins : insert y B ∩ insert y C = insert y (B ∩ C) := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_insert]
          tauto
        rw [hins, hc B hB C hC hBC]

/-- **Sunflower bound.**  Any family `F` of sets of size `w` with more than `(w * r) ^ w`
members contains a sunflower with `r` petals, i.e. `r` distinct members of `F` all of whose
pairwise intersections are equal to one common core `c`.

This is the Erdős–Rado sunflower lemma, in the slightly weakened but cleaner form obtained
from the bound `w ! * (r - 1) ^ w` via `w ! ≤ w ^ w` and `(r - 1) ^ w ≤ r ^ w`; see
`Math2.sunflower_erdos_rado` for the sharp Erdős–Rado form.

Remark on the state of the art: Alweiss–Lovett–Wu–Zhang (and its subsequent refinements)
improve the bound to `(C * r * Real.log w) ^ w` for an absolute constant `C`; that
improvement is *not* formalised here — the bound proved below is the classical one. -/
theorem sunflower_bound (w r : ℕ) (F : Finset (Finset α)) (hsize : ∀ A ∈ F, A.card = w)
    (hcard : (w * r) ^ w < F.card) :
    ∃ T ⊆ F, T.card = r ∧ ∃ c : Finset α, IsSunflower T c := by
  refine sunflower_erdos_rado r w F hsize (lt_of_le_of_lt ?_ hcard)
  calc w ! * (r - 1) ^ w ≤ w ^ w * r ^ w :=
        Nat.mul_le_mul (Nat.factorial_le_pow w) (Nat.pow_le_pow_left (Nat.sub_le r 1) w)
    _ = (w * r) ^ w := (Nat.mul_pow w r w).symm

/-- The statement of the Alweiss–Lovett–Wu–Zhang improved sunflower bound, recorded here
for reference: there is an absolute constant `C` such that every family of more than
`(C * r * Real.log w) ^ w` sets of size `w` (with `w ≥ 2`) contains a sunflower with `r`
petals.  This `Prop` is only *stated*; it is not proved in this file.  What is proved here
is the classical Erdős–Rado bound, `Math2.sunflower_bound`. -/
def ALWZSunflowerBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (β : Type) [DecidableEq β] (w r : ℕ), 2 ≤ w → 1 ≤ r →
    ∀ F : Finset (Finset β), (∀ A ∈ F, A.card = w) →
      (C * r * Real.log w) ^ w < (F.card : ℝ) →
        ∃ T ⊆ F, T.card = r ∧ ∃ c : Finset β, IsSunflower T c

end Math2

