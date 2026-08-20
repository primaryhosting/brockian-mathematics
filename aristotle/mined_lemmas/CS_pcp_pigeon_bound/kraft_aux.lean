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

namespace CS

/-- A finite set of binary codewords is *prefix-free* when no codeword is a prefix of a
different codeword. -/

private lemma kraft_aux (n : ℕ) : ∀ S : Finset (List Bool),
    (∀ w ∈ S, w.length ≤ n) → PrefixFree S →
    ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length ≤ 1 := by
  induction n with
  | zero =>
    intro S hlen _
    have hsub : S ⊆ {[]} := by
      intro w hw
      have h0 : w.length = 0 := Nat.le_zero.mp (hlen w hw)
      simp [List.length_eq_zero_iff.mp h0]
    calc ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length
        ≤ ∑ w ∈ ({[]} : Finset (List Bool)), (1 / 2 : ℝ) ^ w.length := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
          intro i _ _
          positivity
      _ = 1 := by simp
  | succ n ih =>
    intro S hlen hpf
    by_cases hnil : [] ∈ S
    · have hS : S = {[]} :=
        Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hnil, fun v hv => (hpf [] hnil v hv List.nil_prefix).symm⟩
      simp [hS]
    · -- Every codeword is nonempty; split according to the first bit.
      have hne : ∀ w ∈ S, w ≠ [] := by
        intro w hw h
        exact hnil (h ▸ hw)
      have key : ∀ b : Bool,
          ∑ w ∈ S.filter (fun w => w.headI = b), (1 / 2 : ℝ) ^ w.length ≤ 1 / 2 := by
        intro b
        set F : Finset (List Bool) := S.filter (fun w => w.headI = b) with hF
        have hmem : ∀ w ∈ F, w ∈ S ∧ w.headI = b := by
          intro w hw
          rw [hF, Finset.mem_filter] at hw
          exact hw
        have hcons : ∀ w ∈ F, b :: w.tail = w := by
          intro w hw
          obtain ⟨hwS, hwb⟩ := hmem w hw
          exact head_cons_tail (hne w hwS) hwb
        have hinj : ∀ x ∈ F, ∀ y ∈ F, x.tail = y.tail → x = y := by
          intro x hx y hy hxy
          rw [← hcons x hx, ← hcons y hy, hxy]
        set T : Finset (List Bool) := F.image List.tail with hT
        have hTmem : ∀ t ∈ T, b :: t ∈ S := by
          intro t ht
          rw [hT, Finset.mem_image] at ht
          obtain ⟨w, hw, rfl⟩ := ht
          rw [hcons w hw]
          exact (hmem w hw).1
        have hTlen : ∀ t ∈ T, t.length ≤ n := by
          intro t ht
          have hS : b :: t ∈ S := hTmem t ht
          have := hlen _ hS
          simpa using this
        have hTpf : PrefixFree T := by
          intro u hu v hv huv
          have h1 : b :: u ∈ S := hTmem u hu
          have h2 : b :: v ∈ S := hTmem v hv
          have hp : b :: u <+: b :: v := by
            rw [List.cons_prefix_iff]
            exact ⟨v, rfl, huv⟩
          have := hpf _ h1 _ h2 hp
          exact (List.cons_inj_right b).mp this
        have hsum : ∑ w ∈ F, (1 / 2 : ℝ) ^ w.length
            = ∑ t ∈ T, (1 / 2 : ℝ) ^ (t.length + 1) := by
          rw [hT, Finset.sum_image hinj]
          refine Finset.sum_congr rfl ?_
          intro w hw
          have hlw : w.length = w.tail.length + 1 := by
            have : w ≠ [] := hne w (hmem w hw).1
            cases w with
            | nil => exact absurd rfl this
            | cons a t => simp
          rw [hlw]
        rw [hsum]
        have : ∑ t ∈ T, (1 / 2 : ℝ) ^ (t.length + 1)
            = (1 / 2 : ℝ) * ∑ t ∈ T, (1 / 2 : ℝ) ^ t.length := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro t _
          ring
        rw [this]
        have hle := ih T hTlen hTpf
        linarith
      have hsplit : ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length
          = (∑ w ∈ S.filter (fun w => w.headI = true), (1 / 2 : ℝ) ^ w.length)
            + ∑ w ∈ S.filter (fun w => w.headI = false), (1 / 2 : ℝ) ^ w.length := by
        rw [← Finset.sum_filter_add_sum_filter_not S (fun w => w.headI = true)]
        congr 1
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        refine Finset.filter_congr ?_
        intro w _
        simp
      rw [hsplit]
      have h1 := key true
      have h2 := key false
      linarith

/-- **Kraft's inequality.** For any prefix-free binary code `S` (a finite set of binary
codewords, none of which is a prefix of another), the sum `∑ 2^(-ℓᵢ)` over the codeword
lengths `ℓᵢ` is at most `1`. -/
