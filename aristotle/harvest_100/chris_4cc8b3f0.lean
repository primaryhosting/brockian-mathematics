/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
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

set_option grind.warning false

namespace CS

/-- A codeword lying in the `head? = some b` part of a set is `b :: its tail`. -/
lemma cons_head_tail_of_head?_eq {b : Bool} {w : List Bool} (hw : w.head? = some b) :
    w = b :: w.tail := by
  cases w with
  | nil => simp at hw
  | cons a t => simp at hw; simp [hw]

/-- Kraft's inequality, with an explicit bound `N` on the codeword lengths,
proved by induction on `N`. -/
lemma kraft_aux (N : ℕ) : ∀ S : Finset (List Bool),
    (∀ w ∈ S, w.length ≤ N) →
    (∀ w ∈ S, ∀ v ∈ S, w <+: v → w = v) →
    ∑ w ∈ S, (2 : ℝ)⁻¹ ^ w.length ≤ 1 := by
  induction N with
  | zero =>
      intro S hlen _
      have hsub : S ⊆ {([] : List Bool)} := by
        intro w hw
        have := hlen w hw
        have : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp this)
        simp [this]
      calc ∑ w ∈ S, (2 : ℝ)⁻¹ ^ w.length
          ≤ ∑ w ∈ ({[]} : Finset (List Bool)), (2 : ℝ)⁻¹ ^ w.length := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
            intro i _ _
            positivity
        _ = 1 := by simp
  | succ N ih =>
      intro S hlen hpf
      by_cases hnil : ([] : List Bool) ∈ S
      · -- prefix-freeness forces `S = {[]}`
        have hS : S = {([] : List Bool)} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr
          refine ⟨hnil, ?_⟩
          intro v hv
          exact (hpf [] hnil v hv (List.nil_prefix)).symm
        simp [hS]
      · -- split according to the first bit
        have key : ∀ b : Bool,
            ∑ w ∈ S.filter (fun w => w.head? = some b), (2 : ℝ)⁻¹ ^ w.length ≤ 2⁻¹ := by
          intro b
          set X : Finset (List Bool) := S.filter (fun w => w.head? = some b) with hX
          have hmemX : ∀ w ∈ X, w ∈ S ∧ w.head? = some b := by
            intro w hw
            have := Finset.mem_filter.mp hw
            exact ⟨this.1, by simpa using this.2⟩
          have hcons : ∀ w ∈ X, w = b :: w.tail := by
            intro w hw
            exact cons_head_tail_of_head?_eq (hmemX w hw).2
          have hinj : ∀ w ∈ X, ∀ v ∈ X, w.tail = v.tail → w = v := by
            intro w hw v hv h
            rw [hcons w hw, hcons v hv, h]
          set T : Finset (List Bool) := X.image List.tail with hT
          have hTlen : ∀ u ∈ T, u.length ≤ N := by
            intro u hu
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
            have hwS := (hmemX w hw).1
            have := hlen w hwS
            have hw' := hcons w hw
            have : w.length = w.tail.length + 1 := by
              conv_lhs => rw [hw']
              simp
            omega
          have hTpf : ∀ u ∈ T, ∀ v ∈ T, u <+: v → u = v := by
            intro u hu v hv huv
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
            obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hv
            have h1 : (b :: w.tail) <+: (b :: w'.tail) := List.cons_prefix_cons.mpr ⟨rfl, huv⟩
            rw [← hcons w hw, ← hcons w' hw'] at h1
            have := hpf w (hmemX w hw).1 w' (hmemX w' hw').1 h1
            rw [this]
          have hTsum : ∑ u ∈ T, (2 : ℝ)⁻¹ ^ u.length ≤ 1 := ih T hTlen hTpf
          have hrewrite : ∑ w ∈ X, (2 : ℝ)⁻¹ ^ w.length
              = 2⁻¹ * ∑ u ∈ T, (2 : ℝ)⁻¹ ^ u.length := by
            rw [hT, Finset.sum_image hinj, Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro w hw
            have hw' := hcons w hw
            have hlw : w.length = w.tail.length + 1 := by
              conv_lhs => rw [hw']
              simp
            rw [hlw, pow_succ]
            ring
          rw [hrewrite]
          nlinarith [hTsum]
        have hsplit : S = S.filter (fun w => w.head? = some false)
            ∪ S.filter (fun w => w.head? = some true) := by
          ext w
          simp only [Finset.mem_union, Finset.mem_filter]
          constructor
          · intro hw
            have hne : w ≠ [] := by rintro rfl; exact hnil hw
            cases w with
            | nil => exact absurd rfl hne
            | cons a t => cases a <;> simp [hw]
          · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw
        have hdisj : Disjoint (S.filter (fun w => w.head? = some false))
            (S.filter (fun w => w.head? = some true)) := by
          rw [Finset.disjoint_left]
          intro w hw hw'
          have h1 := (Finset.mem_filter.mp hw).2
          have h2 := (Finset.mem_filter.mp hw').2
          rw [h1] at h2
          simp at h2
        calc ∑ w ∈ S, (2 : ℝ)⁻¹ ^ w.length
            = ∑ w ∈ S.filter (fun w => w.head? = some false), (2 : ℝ)⁻¹ ^ w.length
              + ∑ w ∈ S.filter (fun w => w.head? = some true), (2 : ℝ)⁻¹ ^ w.length := by
              conv_lhs => rw [hsplit]
              exact Finset.sum_union hdisj
          _ ≤ 2⁻¹ + 2⁻¹ := add_le_add (key false) (key true)
          _ = 1 := by norm_num

/-- **Kraft's inequality**: any finite prefix-free binary code `S` (a finite set of
binary codewords, no one of which is a prefix of another) satisfies
`∑ w ∈ S, 2 ^ (-|w|) ≤ 1`. -/
theorem pcp_pigeon_bound (S : Finset (List Bool))
    (hpf : ∀ w ∈ S, ∀ v ∈ S, w <+: v → w = v) :
    ∑ w ∈ S, (2 : ℝ)⁻¹ ^ w.length ≤ 1 := by
  refine kraft_aux (S.sup List.length) S ?_ hpf
  intro w hw
  exact Finset.le_sup hw

end CS

