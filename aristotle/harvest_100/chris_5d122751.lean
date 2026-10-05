/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A family `S` of finite sets is a *sunflower with core `K`* if any two distinct members
of `S` meet exactly in `K`. -/
def IsSunflower (K : Finset α) (S : Finset (Finset α)) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = K

lemma IsSunflower.subset {K : Finset α} {S T : Finset (Finset α)}
    (h : IsSunflower K T) (hST : S ⊆ T) : IsSunflower K S :=
  fun A hA B hB hAB => h A (hST hA) B (hST hB) hAB

lemma insert_inter_insert (a : α) (s t : Finset α) :
    insert a s ∩ insert a t = insert a (s ∩ t) := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_insert]
  tauto

/-- Auxiliary form of the Erdős–Rado sunflower lemma: a `w`-uniform family with more than
`w ! * k ^ w` members contains a sunflower with `k + 1` petals. -/
theorem erdos_rado_aux (k : ℕ) (hk : 1 ≤ k) :
    ∀ (w : ℕ) (F : Finset (Finset α)), (∀ A ∈ F, A.card = w) → w ! * k ^ w < F.card →
      ∃ (K : Finset α) (S : Finset (Finset α)), S ⊆ F ∧ S.card = k + 1 ∧ IsSunflower K S := by
  intro w
  induction w with
  | zero =>
    intro F hF hcard
    exfalso
    have hsub : F ⊆ {∅} := by
      intro A hA
      simp only [Finset.mem_singleton]
      exact Finset.card_eq_zero.mp (hF A hA)
    have h1 := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at h1
    simp only [Nat.factorial_zero, pow_zero, mul_one] at hcard
    omega
  | succ w ih =>
    intro F hF hcard
    -- a maximum-size pairwise disjoint subfamily
    set D0 := F.powerset.filter (fun D => IsSunflower (∅ : Finset α) D) with hD0
    have hne : D0.Nonempty := by
      refine ⟨∅, ?_⟩
      simp only [hD0, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.empty_subset _, by intro A hA; simp at hA⟩
    obtain ⟨D, hD, hDmax⟩ := Finset.exists_max_image D0 Finset.card hne
    have hDmem := Finset.mem_filter.mp hD
    have hDF : D ⊆ F := Finset.mem_powerset.mp hDmem.1
    have hDsun : IsSunflower (∅ : Finset α) D := hDmem.2
    by_cases hbig : k + 1 ≤ D.card
    · obtain ⟨S, hSD, hS⟩ := Finset.exists_subset_card_eq hbig
      exact ⟨∅, S, hSD.trans hDF, hS, hDsun.subset hSD⟩
    push_neg at hbig
    have hDcard : D.card ≤ k := by omega
    set Y := D.biUnion id with hYdef
    have hYcard : Y.card ≤ k * (w + 1) := by
      calc Y.card ≤ ∑ A ∈ D, (id A).card := Finset.card_biUnion_le
        _ = ∑ _A ∈ D, (w + 1) := by
            refine Finset.sum_congr rfl ?_
            intro A hA
            exact hF A (hDF hA)
        _ = D.card * (w + 1) := by simp [Finset.sum_const]
        _ ≤ k * (w + 1) := Nat.mul_le_mul_right _ hDcard
    have hsubY : ∀ A ∈ D, A ⊆ Y := by
      intro A hA x hx
      simp only [hYdef, Finset.mem_biUnion, id]
      exact ⟨A, hA, hx⟩
    have hmeet : ∀ A ∈ F, (A ∩ Y).Nonempty := by
      intro A hA
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      have hAne : A ≠ ∅ := by
        intro h
        have := hF A hA
        rw [h] at this
        simp at this
      have hAD : A ∉ D := by
        intro hmem
        exact hAne (by rw [← hcon, Finset.inter_eq_left.mpr (hsubY A hmem)])
      have hins : insert A D ∈ D0 := by
        simp only [hD0, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨Finset.insert_subset hA hDF, ?_⟩
        intro X hX Z hZ hXZ
        simp only [Finset.mem_insert] at hX hZ
        rcases hX with rfl | hX
        · rcases hZ with rfl | hZ
          · exact absurd rfl hXZ
          · have : X ∩ Y = ∅ := hcon
            exact Finset.subset_empty.mp
              (by rw [← this]; exact Finset.inter_subset_inter_left (hsubY Z hZ))
        · rcases hZ with rfl | hZ
          · have : Z ∩ Y = ∅ := hcon
            have h2 : X ∩ Z ⊆ Z ∩ Y := by
              rw [Finset.inter_comm X Z]
              exact Finset.inter_subset_inter_left (hsubY X hX)
            exact Finset.subset_empty.mp (by rw [← this]; exact h2)
          · exact hDsun X hX Z hZ hXZ
      have := hDmax _ hins
      rw [Finset.card_insert_of_notMem hAD] at this
      omega
    have hFpos : 0 < F.card := by
      have h1 : 1 ≤ (w + 1)! * k ^ (w + 1) :=
        Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (pow_ne_zero _ (by omega)))
      omega
    obtain ⟨A0, hA0⟩ := Finset.card_pos.mp hFpos
    have hYne : Y.Nonempty := by
      obtain ⟨x, hx⟩ := hmeet A0 hA0
      exact ⟨x, (Finset.mem_inter.mp hx).2⟩
    -- double counting
    have hsum : F.card ≤ ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card := by
      have hswap : ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card
          = ∑ A ∈ F, (Y.filter (fun y => y ∈ A)).card := by
        simp only [Finset.card_filter]
        rw [Finset.sum_comm]
      rw [hswap]
      calc F.card = ∑ _A ∈ F, 1 := by simp
        _ ≤ ∑ A ∈ F, (Y.filter (fun y => y ∈ A)).card := by
            refine Finset.sum_le_sum ?_
            intro A hA
            have : (Y.filter (fun y => y ∈ A)).Nonempty := by
              obtain ⟨x, hx⟩ := hmeet A hA
              rw [Finset.mem_inter] at hx
              exact ⟨x, Finset.mem_filter.mpr ⟨hx.2, hx.1⟩⟩
            exact Finset.card_pos.mpr this
    obtain ⟨y0, hy0Y, hy0max⟩ :=
      Finset.exists_max_image Y (fun y => (F.filter (fun A => y ∈ A)).card) hYne
    have hmaxsum : ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card
        ≤ Y.card * (F.filter (fun A => y0 ∈ A)).card := by
      have := Finset.sum_le_card_nsmul Y (fun y => (F.filter (fun A => y ∈ A)).card)
        ((F.filter (fun A => y0 ∈ A)).card) hy0max
      simpa [smul_eq_mul] using this
    set d := (F.filter (fun A => y0 ∈ A)).card with hd
    have hkey : w ! * k ^ w < d := by
      have h1 : F.card ≤ (k * (w + 1)) * d :=
        le_trans (le_trans hsum hmaxsum) (Nat.mul_le_mul_right _ hYcard)
      have h2 : (w + 1)! * k ^ (w + 1) = (k * (w + 1)) * (w ! * k ^ w) := by
        rw [Nat.factorial_succ, pow_succ]
        ring
      have h3 : (k * (w + 1)) * (w ! * k ^ w) < (k * (w + 1)) * d := by omega
      exact Nat.lt_of_mul_lt_mul_left h3
    -- the link of `y0`
    set F' := (F.filter (fun A => y0 ∈ A)).image (fun A => A.erase y0) with hF'
    have hinj : Set.InjOn (fun A => A.erase y0) (F.filter (fun A => y0 ∈ A) : Set (Finset α)) := by
      intro A hA B hB hAB
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hA hB
      have := congrArg (insert y0) hAB
      simpa [Finset.insert_erase hA.2, Finset.insert_erase hB.2] using this
    have hF'card : F'.card = d := by
      rw [hF', Finset.card_image_of_injOn hinj, hd]
    have hF'unif : ∀ B ∈ F', B.card = w := by
      intro B hB
      rw [hF'] at hB
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
      rw [Finset.mem_filter] at hA
      rw [Finset.card_erase_of_mem hA.2, hF A hA.1]
      omega
    obtain ⟨K, S', hS'F', hS'card, hS'sun⟩ := ih F' hF'unif (by rw [hF'card]; exact hkey)
    have hy0notin : ∀ B ∈ S', y0 ∉ B := by
      intro B hB
      have := hS'F' hB
      rw [hF'] at this
      obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp this
      exact Finset.notMem_erase _ _
    refine ⟨insert y0 K, S'.image (insert y0), ?_, ?_, ?_⟩
    · intro X hX
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hX
      have hBF' := hS'F' hB
      rw [hF'] at hBF'
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hBF'
      rw [Finset.mem_filter] at hA
      rw [Finset.insert_erase hA.2]
      exact hA.1
    · rw [Finset.card_image_of_injOn, hS'card]
      intro B hB C hC hBC
      simp only [Finset.mem_coe] at hB hC
      have h1 := hy0notin B hB
      have h2 := hy0notin C hC
      have := congrArg (fun s => Finset.erase s y0) hBC
      simpa [Finset.erase_insert h1, Finset.erase_insert h2] using this
    · intro X hX Z hZ hXZ
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hX
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hZ
      have hBC : B ≠ C := by
        intro h
        exact hXZ (by rw [h])
      rw [insert_inter_insert, hS'sun B hB C hC hBC]

/-- **Erdős–Rado sunflower lemma.**  Any `w`-uniform family of finite sets with more than
`w ! * (r - 1) ^ w` members contains a sunflower with `r` petals, i.e. `r` distinct members
all of whose pairwise intersections coincide with a common core `K`.

This is the classical sunflower bound.  (It is *not* the improved Alweiss–Lovett–Wu–Zhang
bound `(C * r * Real.log w) ^ w`, which is not proved here.) -/
theorem sunflower_bound {w r : ℕ} (hr : 2 ≤ r) (F : Finset (Finset α))
    (hF : ∀ A ∈ F, A.card = w) (hcard : w ! * (r - 1) ^ w < F.card) :
    ∃ (K : Finset α) (S : Finset (Finset α)), S ⊆ F ∧ S.card = r ∧ IsSunflower K S := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  simpa using erdos_rado_aux k hk w F hF (by simpa using hcard)

/-- A cruder but simpler form of the sunflower bound: a `w`-uniform family with more than
`(r * w) ^ w` members contains a sunflower with `r` petals. -/
theorem sunflower_bound_pow {w r : ℕ} (hr : 2 ≤ r) (F : Finset (Finset α))
    (hF : ∀ A ∈ F, A.card = w) (hcard : (r * w) ^ w < F.card) :
    ∃ (K : Finset α) (S : Finset (Finset α)), S ⊆ F ∧ S.card = r ∧ IsSunflower K S := by
  refine sunflower_bound hr F hF (lt_of_le_of_lt ?_ hcard)
  calc w ! * (r - 1) ^ w ≤ w ^ w * r ^ w :=
        Nat.mul_le_mul (Nat.factorial_le_pow w) (Nat.pow_le_pow_left (by omega) w)
    _ = (r * w) ^ w := by rw [mul_pow]; ring

/-- A formal statement of the *improved* sunflower bound of Alweiss–Lovett–Wu–Zhang
(in the form due to Rao and to Bell–Chueluecha–Warnke): there is an absolute constant `C`
such that every `w`-uniform family with more than `(C * r * Real.log w) ^ w` members contains a
sunflower with `r` petals.

This is recorded here only as a `Prop`-valued definition, for reference: it is **not** proved in
this file.  What is proved above (`Math2.sunflower_bound`) is the classical Erdős–Rado bound
`w ! * (r - 1) ^ w`. -/
def ALWZSunflowerBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (β : Type) [DecidableEq β] (w r : ℕ), 2 ≤ r → 2 ≤ w →
    ∀ F : Finset (Finset β), (∀ A ∈ F, A.card = w) →
      ((C * r * Real.log w) ^ w < (F.card : ℝ)) →
      ∃ (K : Finset β) (S : Finset (Finset β)), S ⊆ F ∧ S.card = r ∧ IsSunflower K S

end Math2

