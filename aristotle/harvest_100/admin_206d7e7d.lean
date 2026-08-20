import Mathlib

/-!
# The `p`-biased measure on subsets of a finite set

Auxiliary measure-theoretic development for `RequestProject.Main` (Kahn–Kalai):
the distribution of the random subset `α_p`, its basic properties, and a block
factorisation which expresses independence over disjoint blocks.
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

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false
namespace Math2

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## The Kahn–Kalai setting

We fix a finite ground set `α`.  For `p ∈ [0,1]`, `α_p` denotes the random subset of `α`
containing each point independently with probability `p`; its distribution is given by the
weights `weight p S = p ^ |S| * (1 - p) ^ (n - |S|)`.

A family `H` of subsets is `q`-*small* if it admits a cover `G` — every member of `H`
contains a member of `G` — of total cost `∑_{g ∈ G} q ^ |g| ≤ 1/2`; the *expectation
threshold* `q(F)` is the largest `q` for which `F` is `q`-small, while the *threshold*
`p_c(F)` is the `p` at which `ℙ(α_p ∈ F) = 1/2`.

### Scope of this file

* `Math2.prob_le_half_of_isSmall` proves, for an **arbitrary** family, the easy direction
  `q(F) ≤ p_c(F)`: if `H` is `q`-small then `ℙ(α_q ∈ ⟨H⟩) ≤ 1/2`.
* `Math2.kahn_kalai` combines this with the converse (Park–Pham) direction for families of
  **pairwise disjoint** sets, for which threshold and expectation threshold are within a
  factor `2`, with no logarithmic loss.
* `Math2.bonferroni_le_prob` and `Math2.half_lt_prob_of_not_isSmall_of_smallOverlap` give the
  same converse direction for arbitrary families whose pairwise overlap term is small.
* The full Park–Pham theorem, `p_c(F) = O(q(F) · log ℓ(F))` for an arbitrary `ℓ`-bounded
  family, is **not** formalised here; in that generality only the easy direction is proved.
-/

/-- The `p`-biased weight of a subset `S` of the finite ground set `α`: the probability
that the random subset `α_p` is exactly `S`. -/
noncomputable def weight (p : ℝ) (S : Finset α) : ℝ :=
  p ^ S.card * (1 - p) ^ (Fintype.card α - S.card)

/-- The probability that the `p`-random subset `α_p` belongs to the family `A`. -/
noncomputable def prob (p : ℝ) (A : Finset (Finset α)) : ℝ := ∑ S ∈ A, weight p S

/-- The up-closure `⟨H⟩` of a family `H`: all sets containing some member of `H`. -/
def upClosure (H : Finset (Finset α)) : Finset (Finset α) :=
  Finset.univ.filter (fun S => ∃ T ∈ H, T ⊆ S)

/-- `H` is `q`-small: it admits a cover of total cost at most `1/2`. -/
def IsSmall (q : ℝ) (H : Finset (Finset α)) : Prop :=
  ∃ G : Finset (Finset α), (∀ T ∈ H, ∃ g ∈ G, g ⊆ T) ∧ ∑ g ∈ G, q ^ g.card ≤ 1 / 2

/-- `H` is `l`-bounded: all its members have at most `l` elements. -/
def Bounded (l : ℕ) (H : Finset (Finset α)) : Prop := ∀ T ∈ H, T.card ≤ l

/-! ### Basic properties of the `p`-biased measure -/

omit [Fintype α] in
lemma sum_pow_powerset (p : ℝ) (s : Finset α) :
    ∑ t ∈ s.powerset, p ^ t.card * (1 - p) ^ (s.card - t.card) = 1 := by
  have h := Finset.prod_add (fun _ : α => p) (fun _ : α => 1 - p) s
  simp only [Finset.prod_const, add_sub_cancel, one_pow] at h
  refine Eq.trans ?_ h.symm
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_powerset] at ht
  rw [Finset.card_sdiff_of_subset ht]

omit [DecidableEq α] in
lemma weight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset α) : 0 ≤ weight p S :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

omit [DecidableEq α] in
lemma prob_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset (Finset α)) :
    0 ≤ prob p A :=
  Finset.sum_nonneg fun S _ => weight_nonneg hp0 hp1 S

omit [DecidableEq α] in
lemma prob_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {A B : Finset (Finset α)} (h : A ⊆ B) :
    prob p A ≤ prob p B :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun S _ _ => weight_nonneg hp0 hp1 S

lemma prob_univ (p : ℝ) : prob p (Finset.univ : Finset (Finset α)) = 1 := by
  have h : (Finset.univ : Finset (Finset α)) = (Finset.univ : Finset α).powerset := by
    rw [Finset.powerset_univ]
  rw [prob, h]
  simpa [weight, Finset.card_univ] using sum_pow_powerset p (Finset.univ : Finset α)

/-- The probability that `α_p` contains a fixed set `G` is `p ^ |G|`. -/
lemma prob_superset (p : ℝ) (G : Finset α) :
    prob p (Finset.univ.filter (fun S => G ⊆ S)) = p ^ G.card := by
  have key : ∑ S ∈ Finset.univ.filter (fun S : Finset α => G ⊆ S), weight p S
      = ∑ t ∈ (Gᶜ : Finset α).powerset, weight p (t ∪ G) := by
    refine Finset.sum_nbij' (fun S => S \ G) (fun t => t ∪ G) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter] at hS
      simp only [Finset.mem_powerset]
      intro x hx
      simp only [Finset.mem_sdiff] at hx
      simpa using hx.2
    · intro t _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.subset_union_right
    · intro S hS
      simp only [Finset.mem_filter] at hS
      exact Finset.sdiff_union_of_subset hS.2
    · intro t ht
      simp only [Finset.mem_powerset] at ht
      show (t ∪ G) \ G = t
      rw [Finset.union_sdiff_right]
      exact Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_left.2 fun x hx hxG =>
        (Finset.mem_compl.1 (ht hx)) hxG)
    · intro S hS
      simp only [Finset.mem_filter] at hS
      rw [Finset.sdiff_union_of_subset hS.2]
  rw [prob, key]
  have hcard : ∀ t ∈ (Gᶜ : Finset α).powerset, weight p (t ∪ G)
      = p ^ G.card * (p ^ t.card * (1 - p) ^ ((Gᶜ : Finset α).card - t.card)) := by
    intro t ht
    simp only [Finset.mem_powerset] at ht
    have hdisj : Disjoint t G :=
      Finset.disjoint_left.2 fun x hx hxG => (Finset.mem_compl.1 (ht hx)) hxG
    have h1 : (t ∪ G).card = t.card + G.card := Finset.card_union_of_disjoint hdisj
    unfold weight
    rw [h1, Finset.card_compl, pow_add]
    have h2 : Fintype.card α - (t.card + G.card) = Fintype.card α - G.card - t.card := by omega
    rw [h2]
    ring
  rw [Finset.sum_congr rfl hcard, ← Finset.mul_sum, sum_pow_powerset]
  ring

/-- The probability that `α_p` misses a fixed set `T` is `(1 - p) ^ |T|`. -/
lemma prob_disjoint (p : ℝ) (T : Finset α) :
    prob p (Finset.univ.filter (fun S => Disjoint S T)) = (1 - p) ^ T.card := by
  have hcompl : ∀ (r : ℝ) (S : Finset α), weight r Sᶜ = weight (1 - r) S := by
    intro r S
    unfold weight
    rw [Finset.card_compl]
    have h1 : Fintype.card α - (Fintype.card α - S.card) = S.card := by
      have := Finset.card_le_univ S
      omega
    rw [h1]
    have h2 : 1 - (1 - r) = r := by ring
    rw [h2]
    ring
  have key : prob p (Finset.univ.filter (fun S : Finset α => Disjoint S T))
      = ∑ S ∈ Finset.univ.filter (fun S : Finset α => T ⊆ S), weight (1 - p) S := by
    rw [prob]
    refine Finset.sum_nbij' (fun S => Sᶜ) (fun S => Sᶜ) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      intro x hx
      simp only [Finset.mem_compl]
      exact fun hxS => (Finset.disjoint_left.1 hS hxS) hx
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      refine Finset.disjoint_left.2 fun x hx hxT => ?_
      exact (Finset.mem_compl.1 hx) (hS hxT)
    · intro S _
      simp
    · intro S _
      simp
    · intro S _
      have := hcompl (1 - p) S
      simpa using this.symm
  rw [key]
  have := prob_superset (1 - p) T
  rw [prob] at this
  rw [this]

lemma prob_compl {p : ℝ} (A : Finset (Finset α)) :
    prob p A + prob p (Finset.univ \ A) = 1 := by
  rw [prob, prob, ← Finset.sum_union (Finset.disjoint_sdiff)]
  have h : A ∪ (Finset.univ \ A) = Finset.univ := by
    ext S; simp [Finset.mem_union]
  rw [h]
  exact prob_univ p

lemma sum_biUnion_le {β γ : Type*} [DecidableEq β] [DecidableEq γ] (s : Finset β)
    (t : β → Finset γ) (f : γ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      have h1 : ∑ x ∈ t a ∪ s.biUnion t, f x ≤ ∑ x ∈ t a, f x + ∑ x ∈ s.biUnion t, f x := by
        have h2 := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
        have h3 : 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, f x := Finset.sum_nonneg fun x _ => hf x
        linarith
      linarith

/-! ### A block factorisation of the `p`-biased measure

For a family of *pairwise disjoint* sets the events "`α_p` does not contain `T`" are
independent, and the probability that `α_p` contains no member factorises as a product.
We prove this by an explicit factorisation of the `p`-biased weights along a block. -/

/-- The `p`-biased weight of `u` relative to a ground set `B`. -/
noncomputable def wt (p : ℝ) (B u : Finset α) : ℝ := p ^ u.card * (1 - p) ^ (B.card - u.card)

omit [DecidableEq α] in
lemma wt_univ (p : ℝ) (S : Finset α) : wt p Finset.univ S = weight p S := by
  simp [wt, weight, Finset.card_univ]

omit [Fintype α] in
lemma sum_wt (p : ℝ) (B : Finset α) : ∑ u ∈ B.powerset, wt p B u = 1 := sum_pow_powerset p B

omit [Fintype α] [DecidableEq α] in
lemma wt_self (p : ℝ) (B : Finset α) : wt p B B = p ^ B.card := by
  simp [wt]

omit [Fintype α] in
lemma sum_split {T B : Finset α} (h : T ⊆ B) (f g : Finset α → ℝ) :
    ∑ v ∈ B.powerset, f (v ∩ T) * g (v \ T)
      = (∑ u ∈ T.powerset, f u) * (∑ w ∈ (B \ T).powerset, g w) := by
  have hprod : (∑ u ∈ T.powerset, f u) * (∑ w ∈ (B \ T).powerset, g w)
      = ∑ x ∈ T.powerset ×ˢ (B \ T).powerset, f x.1 * g x.2 := by
    rw [Finset.sum_product, Finset.sum_mul_sum]
  rw [hprod]
  refine Finset.sum_nbij' (fun v => (v ∩ T, v \ T)) (fun x => x.1 ∪ x.2) ?_ ?_ ?_ ?_ ?_
  · rintro v hv
    simp only [Finset.mem_powerset] at hv
    simp only [Finset.mem_product, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.sdiff_subset_sdiff hv (le_refl T)⟩
  · rintro ⟨u, w⟩ hx
    simp only [Finset.mem_product, Finset.mem_powerset] at hx
    simp only [Finset.mem_powerset]
    exact Finset.union_subset (hx.1.trans h) (hx.2.trans Finset.sdiff_subset)
  · intro v _
    show (v ∩ T) ∪ (v \ T) = v
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  · rintro ⟨u, w⟩ hx
    simp only [Finset.mem_product, Finset.mem_powerset] at hx
    have hw : Disjoint w T := Finset.disjoint_left.2 fun x hx' hxT =>
      (Finset.mem_sdiff.1 (hx.2 hx')).2 hxT
    show ((u ∪ w) ∩ T, (u ∪ w) \ T) = (u, w)
    have h1 : (u ∪ w) ∩ T = u := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hu | hw', hT⟩
        · exact hu
        · exact absurd hT (Finset.disjoint_left.1 hw hw')
      · intro hu; exact ⟨Or.inl hu, hx.1 hu⟩
    have h2 : (u ∪ w) \ T = w := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hu | hw', hT⟩
        · exact absurd (hx.1 hu) hT
        · exact hw'
      · intro hw'; exact ⟨Or.inr hw', fun hT => (Finset.disjoint_left.1 hw hw') hT⟩
    rw [h1, h2]
  · intro v _
    rfl

omit [Fintype α] in
lemma wt_split (p : ℝ) {T B : Finset α} (hTB : T ⊆ B) {v : Finset α} (hv : v ⊆ B) :
    wt p B v = wt p T (v ∩ T) * wt p (B \ T) (v \ T) := by
  have hcards : (v ∩ T).card + (v \ T).card = v.card :=
    Finset.card_inter_add_card_sdiff v T
  have h1 : (v ∩ T).card ≤ T.card := Finset.card_le_card Finset.inter_subset_right
  have h2 : (v \ T).card ≤ (B \ T).card :=
    Finset.card_le_card (Finset.sdiff_subset_sdiff hv (le_refl T))
  have h3 : (B \ T).card = B.card - T.card := Finset.card_sdiff_of_subset hTB
  have h4 : T.card ≤ B.card := Finset.card_le_card hTB
  have h5 : v.card ≤ B.card := Finset.card_le_card hv
  unfold wt
  rw [show v.card = (v ∩ T).card + (v \ T).card from hcards.symm,
    show B.card - ((v ∩ T).card + (v \ T).card)
      = (T.card - (v ∩ T).card) + ((B \ T).card - (v \ T).card) by omega,
    pow_add, pow_add]
  ring

/-- If the members of `H` are pairwise disjoint subsets of `B`, the `B`-relative probability
that a random subset of `B` contains no member of `H` is `∏_{T ∈ H} (1 - p ^ |T|)`. -/
lemma sum_wt_no_member (p : ℝ) (H : Finset (Finset α)) :
    ∀ B : Finset α, (∀ T ∈ H, T ⊆ B) → ((H : Set (Finset α)).Pairwise Disjoint) →
      ∑ v ∈ B.powerset, (if ∀ T ∈ H, ¬ T ⊆ v then wt p B v else 0)
        = ∏ T ∈ H, (1 - p ^ T.card) := by
  classical
  induction H using Finset.induction with
  | empty =>
      intro B _ _
      simpa using sum_wt p B
  | insert T₀ H' hT₀ ih =>
      intro B hHB hdisj
      have hT₀B : T₀ ⊆ B := hHB T₀ (Finset.mem_insert_self _ _)
      have hH'B : ∀ T ∈ H', T ⊆ B \ T₀ := by
        intro T hT
        have hTB : T ⊆ B := hHB T (Finset.mem_insert_of_mem hT)
        have hne : T ≠ T₀ := fun h => hT₀ (h ▸ hT)
        have hd : Disjoint T T₀ :=
          hdisj (by simp [hT]) (by simp) hne
        intro x hx
        exact Finset.mem_sdiff.2 ⟨hTB hx, fun hxT₀ => (Finset.disjoint_left.1 hd hx) hxT₀⟩
      have hdisj' : ((H' : Set (Finset α)).Pairwise Disjoint) := by
        intro x hx y hy hxy
        exact hdisj (by simp [hx]) (by simp [hy]) hxy
      set f : Finset α → ℝ := fun u => if ¬ T₀ ⊆ u then wt p T₀ u else 0 with hf
      set g : Finset α → ℝ :=
        fun w => if ∀ T ∈ H', ¬ T ⊆ w then wt p (B \ T₀) w else 0 with hg
      have hpoint : ∀ v ∈ B.powerset,
          (if ∀ T ∈ insert T₀ H', ¬ T ⊆ v then wt p B v else 0) = f (v ∩ T₀) * g (v \ T₀) := by
        intro v hv
        rw [Finset.mem_powerset] at hv
        have hA : T₀ ⊆ v ∩ T₀ ↔ T₀ ⊆ v := by
          constructor
          · intro h x hx; exact (Finset.mem_inter.1 (h hx)).1
          · intro h x hx; exact Finset.mem_inter.2 ⟨h hx, hx⟩
        have hB : ∀ T ∈ H', (T ⊆ v \ T₀ ↔ T ⊆ v) := by
          intro T hT
          have hne : T ≠ T₀ := fun h => hT₀ (h ▸ hT)
          have hd : Disjoint T T₀ := hdisj (by simp [hT]) (by simp) hne
          constructor
          · intro h x hx; exact (Finset.mem_sdiff.1 (h hx)).1
          · intro h x hx
            exact Finset.mem_sdiff.2 ⟨h hx, fun hxT₀ => (Finset.disjoint_left.1 hd hx) hxT₀⟩
        by_cases hc₀ : T₀ ⊆ v
        · have h1 : ¬ (∀ T ∈ insert T₀ H', ¬ T ⊆ v) := by
            intro h; exact h T₀ (Finset.mem_insert_self _ _) hc₀
          simp only [hf, hg, if_neg h1]
          rw [if_neg (by simpa [hA] using hc₀)]
          ring
        · by_cases hc1 : ∀ T ∈ H', ¬ T ⊆ v
          · have h1 : ∀ T ∈ insert T₀ H', ¬ T ⊆ v := by
              intro T hT
              rcases Finset.mem_insert.1 hT with h | h
              · exact h ▸ hc₀
              · exact hc1 T h
            have h2 : ∀ T ∈ H', ¬ T ⊆ v \ T₀ := fun T hT h => hc1 T hT ((hB T hT).1 h)
            simp only [hf, hg, if_pos h1, if_pos h2,
              if_pos (show ¬ T₀ ⊆ v ∩ T₀ from fun h => hc₀ (hA.1 h))]
            exact wt_split p hT₀B hv
          · push_neg at hc1
            obtain ⟨T, hT, hTv⟩ := hc1
            have h1 : ¬ (∀ T ∈ insert T₀ H', ¬ T ⊆ v) := by
              intro h; exact h T (Finset.mem_insert_of_mem hT) hTv
            have h2 : ¬ (∀ T ∈ H', ¬ T ⊆ v \ T₀) := by
              intro h; exact h T hT ((hB T hT).2 hTv)
            simp only [hf, hg, if_neg h1, if_neg h2]
            ring
      rw [Finset.sum_congr rfl hpoint, sum_split hT₀B f g]
      have hfirst : (∑ u ∈ T₀.powerset, f u) = 1 - p ^ T₀.card := by
        have hkey : ∀ u ∈ T₀.powerset, f u = wt p T₀ u - (if u = T₀ then wt p T₀ T₀ else 0) := by
          intro u hu
          rw [Finset.mem_powerset] at hu
          by_cases h : u = T₀
          · subst h
            simp [hf]
          · have hns : ¬ T₀ ⊆ u := fun hsub => h (Finset.Subset.antisymm hu hsub)
            simp only [hf, if_pos hns, if_neg h, sub_zero]
        rw [Finset.sum_congr rfl hkey, Finset.sum_sub_distrib, sum_wt,
          Finset.sum_ite_eq' T₀.powerset T₀ (fun _ => wt p T₀ T₀)]
        simp [Finset.mem_powerset, wt_self]
      rw [hfirst, ih (B \ T₀) hH'B hdisj', Finset.prod_insert hT₀]

/-- For a family of pairwise disjoint sets, the probability that `α_p` contains no member
is the product `∏_{T ∈ H} (1 - p ^ |T|)`. -/
lemma prob_no_member (p : ℝ) {H : Finset (Finset α)}
    (hdisj : ((H : Set (Finset α)).Pairwise Disjoint)) :
    prob p (Finset.univ.filter (fun S => ∀ T ∈ H, ¬ T ⊆ S)) = ∏ T ∈ H, (1 - p ^ T.card) := by
  have h := sum_wt_no_member p H Finset.univ (fun T _ => Finset.subset_univ T) hdisj
  rw [Finset.powerset_univ] at h
  rw [prob, Finset.sum_filter]
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hc : ∀ T ∈ H, ¬ T ⊆ S
  · simp [wt_univ]
  · simp [hc]

/-- The up-closure is the complement of the event that no member is contained. -/
lemma upClosure_eq_compl (H : Finset (Finset α)) :
    upClosure H
      = Finset.univ \ Finset.univ.filter (fun S => ∀ T ∈ H, ¬ T ⊆ S) := by
  ext S
  simp only [upClosure, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  push_neg
  tauto

/-! ### Monotonicity in `p` for increasing families

The probability of an increasing (up-closed) family is nondecreasing in `p`.  We prove this
by induction on the ground set, using the recursion obtained by conditioning on one point. -/

/-- The probability, relative to a ground set `B`, that a random subset of `B` (each point of
`B` included independently with probability `p`) satisfies `P`. -/
noncomputable def relProb (p : ℝ) (B : Finset α) (P : Finset α → Prop) : ℝ :=
  ∑ u ∈ B.powerset, (if P u then wt p B u else 0)

omit [Fintype α] [DecidableEq α] in
lemma wt_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (B u : Finset α) : 0 ≤ wt p B u :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

omit [Fintype α] in
/-- Conditioning on the point `x`. -/
lemma relProb_insert (p : ℝ) {x : α} {B : Finset α} (hx : x ∉ B) (P : Finset α → Prop) :
    relProb p (insert x B) P
      = (1 - p) * relProb p B P + p * relProb p B (fun v => P (insert x v)) := by
  have hdisj : Disjoint B.powerset (B.powerset.image (insert x)) := by
    refine Finset.disjoint_left.2 ?_
    intro u hu hu2
    simp only [Finset.mem_powerset] at hu
    simp only [Finset.mem_image, Finset.mem_powerset] at hu2
    obtain ⟨v, _, rfl⟩ := hu2
    exact hx (hu (Finset.mem_insert_self x v))
  have hinj : ∀ v ∈ B.powerset, ∀ v' ∈ B.powerset, insert x v = insert x v' → v = v' := by
    intro v hv v' hv' hvv
    rw [Finset.mem_powerset] at hv hv'
    have h1 : (insert x v).erase x = v := Finset.erase_insert (fun hxv => hx (hv hxv))
    have h2 : (insert x v').erase x = v' := Finset.erase_insert (fun hxv => hx (hv' hxv))
    rw [← h1, ← h2, hvv]
  have hw0 : ∀ u ∈ B.powerset, wt p (insert x B) u = (1 - p) * wt p B u := by
    intro u hu
    rw [Finset.mem_powerset] at hu
    have hcard : (insert x B).card = B.card + 1 := Finset.card_insert_of_notMem hx
    have hle : u.card ≤ B.card := Finset.card_le_card hu
    unfold wt
    rw [hcard, show B.card + 1 - u.card = (B.card - u.card) + 1 by omega, pow_succ]
    ring
  have hw1 : ∀ v ∈ B.powerset, wt p (insert x B) (insert x v) = p * wt p B v := by
    intro v hv
    rw [Finset.mem_powerset] at hv
    have hxv : x ∉ v := fun hxv => hx (hv hxv)
    have hcard : (insert x B).card = B.card + 1 := Finset.card_insert_of_notMem hx
    have hcard' : (insert x v).card = v.card + 1 := Finset.card_insert_of_notMem hxv
    have hle : v.card ≤ B.card := Finset.card_le_card hv
    unfold wt
    rw [hcard, hcard', show B.card + 1 - (v.card + 1) = B.card - v.card by omega, pow_succ]
    ring
  rw [relProb, Finset.powerset_insert, Finset.sum_union hdisj,
    Finset.sum_image hinj]
  have e0 : ∑ u ∈ B.powerset, (if P u then wt p (insert x B) u else 0)
      = (1 - p) * relProb p B P := by
    rw [relProb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    by_cases hc : P u
    · rw [if_pos hc, if_pos hc, hw0 u hu]
    · rw [if_neg hc, if_neg hc, mul_zero]
  have e1 : ∑ v ∈ B.powerset, (if P (insert x v) then wt p (insert x B) (insert x v) else 0)
      = p * relProb p B (fun v => P (insert x v)) := by
    rw [relProb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    by_cases hc : P (insert x v)
    · rw [if_pos hc, if_pos hc, hw1 v hv]
    · rw [if_neg hc, if_neg hc, mul_zero]
  rw [e0, e1]

omit [Fintype α] in
/-- For an up-closed predicate, adding a point can only help. -/
lemma relProb_le_relProb_insert {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (B : Finset α) (x : α)
    (P : Finset α → Prop) (hup : ∀ u v : Finset α, u ⊆ v → P u → P v) :
    relProb p B P ≤ relProb p B (fun v => P (insert x v)) := by
  refine Finset.sum_le_sum fun u _ => ?_
  by_cases hc : P u
  · rw [if_pos hc, if_pos (hup u (insert x u) (Finset.subset_insert x u) hc)]
  · rw [if_neg hc]
    by_cases hc' : P (insert x u)
    · rw [if_pos hc']
      exact wt_nonneg hp0 hp1 B u
    · rw [if_neg hc']

omit [Fintype α] in
/-- The relative probability of an up-closed predicate is nondecreasing in `p`. -/
lemma relProb_mono {p p' : ℝ} (hp0 : 0 ≤ p) (hpp : p ≤ p') (hp1' : p' ≤ 1) (B : Finset α) :
    ∀ P : Finset α → Prop, (∀ u v : Finset α, u ⊆ v → P u → P v) →
      relProb p B P ≤ relProb p' B P := by
  classical
  have hp1 : p ≤ 1 := le_trans hpp hp1'
  have hp0' : 0 ≤ p' := le_trans hp0 hpp
  induction B using Finset.induction with
  | empty =>
      intro P _
      simp only [relProb, Finset.powerset_empty, Finset.sum_singleton]
      by_cases hc : P ∅
      · rw [if_pos hc, if_pos hc]
        simp [wt]
      · rw [if_neg hc, if_neg hc]
  | insert x B hx ih =>
      intro P hup
      have hup' : ∀ u v : Finset α, u ⊆ v → P (insert x u) → P (insert x v) := by
        intro u v huv h
        exact hup _ _ (Finset.insert_subset_insert x huv) h
      have h0 := ih P hup
      have h1 := ih (fun v => P (insert x v)) hup'
      have hle := relProb_le_relProb_insert hp0 hp1 B x P hup
      rw [relProb_insert p hx P, relProb_insert p' hx P]
      nlinarith [hle, h0, h1]

omit [DecidableEq α] in
lemma prob_eq_relProb (p : ℝ) (A : Finset (Finset α)) :
    prob p A = relProb p Finset.univ (fun S => S ∈ A) := by
  classical
  rw [relProb, Finset.powerset_univ, Finset.sum_ite_mem, Finset.univ_inter, prob]
  exact Finset.sum_congr rfl fun S _ => (wt_univ p S).symm

/-- **Monotonicity of the threshold function**: the probability that `α_p` lies in the
increasing family `⟨H⟩` is nondecreasing in `p`. -/
theorem prob_upClosure_mono {p p' : ℝ} (hp0 : 0 ≤ p) (hpp : p ≤ p') (hp1' : p' ≤ 1)
    (H : Finset (Finset α)) :
    prob p (upClosure H) ≤ prob p' (upClosure H) := by
  rw [prob_eq_relProb, prob_eq_relProb]
  refine relProb_mono hp0 hpp hp1' Finset.univ _ ?_
  intro u v huv hu
  simp only [upClosure, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  obtain ⟨T, hT, hTu⟩ := hu
  exact ⟨T, hT, hTu.trans huv⟩

end Math2

import Mathlib
import RequestProject.Measure

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
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

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### The easy direction: the expectation threshold is at most the threshold -/

/-- If `H` is `q`-small then the `q`-random subset lies in `⟨H⟩` with probability at most `1/2`.
Consequently the expectation threshold `q(F)` never exceeds the threshold `p_c(F)`:
this is the easy half of the Kahn–Kalai relation, proved by the union bound over a cover. -/
theorem prob_le_half_of_isSmall {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {H : Finset (Finset α)} (h : IsSmall q H) :
    prob q (upClosure H) ≤ 1 / 2 := by
  obtain ⟨G, hcov, hcost⟩ := h
  have hsub : upClosure H ⊆ G.biUnion (fun g => Finset.univ.filter (fun S => g ⊆ S)) := by
    intro S hS
    simp only [upClosure, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    obtain ⟨T, hT, hTS⟩ := hS
    obtain ⟨g, hg, hgT⟩ := hcov T hT
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨g, hg, hgT.trans hTS⟩
  calc prob q (upClosure H)
      ≤ prob q (G.biUnion (fun g => Finset.univ.filter (fun S => g ⊆ S))) :=
        prob_mono hq0 hq1 hsub
    _ ≤ ∑ g ∈ G, prob q (Finset.univ.filter (fun S => g ⊆ S)) :=
        sum_biUnion_le G _ _ (weight_nonneg hq0 hq1)
    _ = ∑ g ∈ G, q ^ g.card := Finset.sum_congr rfl fun g _ => prob_superset q g
    _ ≤ 1 / 2 := hcost

/-- A crude general upper bound for the threshold: if some member `T₀` of `H` satisfies
`p ^ |T₀| > 1/2`, then `α_p` lies in `⟨H⟩` with probability more than `1/2`.  In particular
the threshold of an `ℓ`-bounded nonempty family is at most `2 ^ (-1/ℓ)`. -/
theorem half_lt_prob_of_mem {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {H : Finset (Finset α)}
    {T₀ : Finset α} (hT₀ : T₀ ∈ H) (hlarge : 1 / 2 < p ^ T₀.card) :
    1 / 2 < prob p (upClosure H) := by
  have hsub : Finset.univ.filter (fun S => T₀ ⊆ S) ⊆ upClosure H := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [upClosure, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨T₀, hT₀, hS⟩
  have := prob_mono hp0 hp1 hsub
  rw [prob_superset] at this
  linarith

/-! ### The hard direction for families of pairwise disjoint sets

For a family of pairwise disjoint sets which is not `q`-small, the `2q`-random set already
contains a member with probability more than `1/2`: threshold and expectation threshold are
within a factor `2`, with no logarithmic loss. -/

omit [Fintype α] [DecidableEq α] in
/-- Non-`q`-smallness, applied to the cover `H` itself, gives `∑_{T ∈ H} q ^ |T| > 1/2`. -/
lemma half_lt_sum_of_not_isSmall {q : ℝ} {H : Finset (Finset α)} (h : ¬ IsSmall q H) :
    1 / 2 < ∑ T ∈ H, q ^ T.card := by
  by_contra hcon
  push_neg at hcon
  exact h ⟨H, fun T hT => ⟨T, hT, Finset.Subset.refl T⟩, hcon⟩

/-- **Park–Pham direction for pairwise disjoint families.** -/
theorem half_lt_prob_of_not_isSmall_of_pairwiseDisjoint {q : ℝ} (hq0 : 0 < q)
    {H : Finset (Finset α)} (hdisj : ((H : Set (Finset α)).Pairwise Disjoint))
    (h : ¬ IsSmall q H) :
    1 / 2 < prob (min 1 (2 * q)) (upClosure H) := by
  set p : ℝ := min 1 (2 * q) with hp
  have hp0 : 0 ≤ p := le_min (by norm_num) (by linarith)
  have hp1 : p ≤ 1 := min_le_left _ _
  have hsum : 1 / 2 < ∑ T ∈ H, q ^ T.card := half_lt_sum_of_not_isSmall h
  by_cases hemp : ∅ ∈ H
  · have huniv : upClosure H = (Finset.univ : Finset (Finset α)) := by
      ext S
      simp only [upClosure, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact ⟨∅, hemp, Finset.empty_subset S⟩
    rw [huniv, prob_univ]
    norm_num
  · have hne : H.Nonempty := by
      rcases Finset.eq_empty_or_nonempty H with hh | hh
      · rw [hh] at hsum; simp at hsum; linarith
      · exact hh
    have hcard : ∀ T ∈ H, 1 ≤ T.card := by
      intro T hT
      rcases Nat.eq_zero_or_pos T.card with h0 | h0
      · exact absurd (Finset.card_eq_zero.1 h0 ▸ hT) hemp
      · exact h0
    rw [upClosure_eq_compl]
    have hc := prob_compl (p := p) (Finset.univ.filter (fun S : Finset α => ∀ T ∈ H, ¬ T ⊆ S))
    rw [prob_no_member p hdisj] at hc
    have hlt : ∏ T ∈ H, (1 - p ^ T.card) < 1 / 2 := by
      rcases le_or_gt 1 (2 * q) with hcase | hcase
      · have hp1' : p = 1 := by simp [hp, min_eq_left hcase]
        obtain ⟨T₀, hT₀⟩ := hne
        have hzero : (1 : ℝ) - p ^ T₀.card = 0 := by rw [hp1']; simp
        have : ∏ T ∈ H, (1 - p ^ T.card) = 0 :=
          Finset.prod_eq_zero hT₀ hzero
        rw [this]; norm_num
      · have hpq : p = 2 * q := by simp [hp, min_eq_right hcase.le]
        have hq1 : q < 1 / 2 := by linarith
        -- each factor is bounded by an exponential
        have hstep : ∀ T ∈ H, (1 : ℝ) - p ^ T.card ≤ Real.exp (-(p ^ T.card)) := by
          intro T _
          have := Real.add_one_le_exp (-(p ^ T.card))
          linarith
        have hnonneg : ∀ T ∈ H, (0 : ℝ) ≤ 1 - p ^ T.card := by
          intro T _
          have : p ^ T.card ≤ 1 := pow_le_one₀ hp0 hp1
          linarith
        have hprod : ∏ T ∈ H, (1 - p ^ T.card) ≤ ∏ T ∈ H, Real.exp (-(p ^ T.card)) :=
          Finset.prod_le_prod hnonneg hstep
        have hexp : ∏ T ∈ H, Real.exp (-(p ^ T.card)) = Real.exp (-∑ T ∈ H, p ^ T.card) := by
          rw [← Real.exp_sum]
          congr 1
          rw [← Finset.sum_neg_distrib]
        have hbig : 1 < ∑ T ∈ H, p ^ T.card := by
          have hterm : ∀ T ∈ H, 2 * q ^ T.card ≤ p ^ T.card := by
            intro T hT
            have h1 : (1 : ℕ) ≤ T.card := hcard T hT
            have h2 : p ^ T.card = 2 ^ T.card * q ^ T.card := by
              rw [hpq, mul_pow]
            rw [h2]
            have h3 : (2 : ℝ) ≤ 2 ^ T.card := by
              calc (2 : ℝ) = 2 ^ (1 : ℕ) := by norm_num
                _ ≤ 2 ^ T.card := by
                    exact pow_le_pow_right₀ (by norm_num) h1
            have h4 : (0 : ℝ) ≤ q ^ T.card := pow_nonneg hq0.le _
            nlinarith
          have := Finset.sum_le_sum hterm
          rw [← Finset.mul_sum] at this
          linarith
        have hexplt : Real.exp (-∑ T ∈ H, p ^ T.card) < 1 / 2 := by
          have h6 : Real.exp (-∑ T ∈ H, p ^ T.card) < Real.exp (-1) :=
            Real.exp_lt_exp.2 (by linarith)
          have h7 : Real.exp (-1 : ℝ) < 1 / 2 := by
            have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
            have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
            rw [Real.exp_neg, inv_lt_iff_one_lt_mul₀ hpos]
            linarith
          linarith
        rw [hexp] at hprod
        linarith
    linarith

/-! ### The hard direction for `1`-bounded families

A `1`-bounded family (all members of size at most one) is automatically pairwise disjoint,
so the previous theorem applies. -/

omit [Fintype α] [DecidableEq α] in
lemma pairwiseDisjoint_of_bounded_one {H : Finset (Finset α)} (hb : Bounded 1 H) :
    ((H : Set (Finset α)).Pairwise Disjoint) := by
  intro S hS T hT hST
  refine Finset.disjoint_left.2 fun x hxS hxT => hST ?_
  have hS1 : S.card ≤ 1 := hb S (by simpa using hS)
  have hT1 : T.card ≤ 1 := hb T (by simpa using hT)
  have hSx : S = {x} := Finset.eq_singleton_iff_unique_mem.2
    ⟨hxS, fun y hy => Finset.card_le_one.1 hS1 y hy x hxS⟩
  have hTx : T = {x} := Finset.eq_singleton_iff_unique_mem.2
    ⟨hxT, fun y hy => Finset.card_le_one.1 hT1 y hy x hxT⟩
  rw [hSx, hTx]

/-- For a `1`-bounded family which is *not* `q`-small, the `min 1 (2q)`-random subset lies in
`⟨H⟩` with probability more than `1/2`. -/
theorem half_lt_prob_of_not_isSmall_of_bounded_one {q : ℝ} (hq0 : 0 < q)
    {H : Finset (Finset α)} (hb : Bounded 1 H) (h : ¬ IsSmall q H) :
    1 / 2 < prob (min 1 (2 * q)) (upClosure H) :=
  half_lt_prob_of_not_isSmall_of_pairwiseDisjoint hq0 (pairwiseDisjoint_of_bounded_one hb) h

/-! ### A Bonferroni bound: the hard direction beyond disjoint families

For an arbitrary family the second Bonferroni inequality gives the lower bound
`ℙ(α_p ∈ ⟨H⟩) ≥ ∑_T p ^ |T| - ∑_{T ≠ T'} p ^ |T ∪ T'| / 2`, which yields the Park–Pham
direction (again with constant `2` and no logarithmic loss) whenever the pairwise overlap
term is small. -/

lemma pow_card_eq_sum (p : ℝ) (T : Finset α) :
    p ^ T.card = ∑ S : Finset α, (if T ⊆ S then weight p S else 0) := by
  rw [← prob_superset p T, prob, Finset.sum_filter]

lemma sum_pow_card_eq (p : ℝ) (H : Finset (Finset α)) :
    ∑ T ∈ H, p ^ T.card
      = ∑ S : Finset α, weight p S * ((H.filter (fun T => T ⊆ S)).card : ℝ) := by
  rw [Finset.sum_congr rfl (fun T (_ : T ∈ H) => pow_card_eq_sum p T), Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

lemma sum_pair_eq (p : ℝ) (H : Finset (Finset α)) :
    ∑ T ∈ H, ∑ T' ∈ H.erase T, p ^ (T ∪ T').card
      = ∑ S : Finset α, weight p S *
          (((H.filter (fun T => T ⊆ S)).card : ℝ) * ((H.filter (fun T => T ⊆ S)).card - 1)) := by
  have hstep : ∀ T ∈ H, ∀ T' ∈ H.erase T,
      p ^ (T ∪ T').card = ∑ S : Finset α, (if T ⊆ S ∧ T' ⊆ S then weight p S else 0) := by
    intro T _ T' _
    rw [pow_card_eq_sum p (T ∪ T')]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hc : T ⊆ S ∧ T' ⊆ S
    · rw [if_pos (Finset.union_subset hc.1 hc.2), if_pos hc]
    · rw [if_neg hc, if_neg]
      intro hsub
      exact hc ⟨Finset.Subset.trans Finset.subset_union_left hsub,
        Finset.Subset.trans Finset.subset_union_right hsub⟩
  rw [Finset.sum_congr rfl fun T hT => Finset.sum_congr rfl fun T' hT' => hstep T hT T' hT']
  have e2 : ∀ T ∈ H,
      (∑ T' ∈ H.erase T, ∑ S : Finset α, (if T ⊆ S ∧ T' ⊆ S then weight p S else 0))
        = ∑ S : Finset α, ∑ T' ∈ H.erase T, (if T ⊆ S ∧ T' ⊆ S then weight p S else 0) :=
    fun T _ => Finset.sum_comm
  rw [Finset.sum_congr rfl e2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  set k : ℕ := (H.filter (fun T => T ⊆ S)).card with hk
  have hinner : ∀ T ∈ H, (∑ T' ∈ H.erase T, (if T ⊆ S ∧ T' ⊆ S then weight p S else 0))
      = (if T ⊆ S then ((k : ℝ) - 1) * weight p S else 0) := by
    intro T hT
    by_cases hTS : T ⊆ S
    · rw [if_pos hTS]
      have : ∀ T' ∈ H.erase T, (if T ⊆ S ∧ T' ⊆ S then weight p S else 0)
          = (if T' ⊆ S then weight p S else 0) := by
        intro T' _
        by_cases hT'S : T' ⊆ S
        · rw [if_pos ⟨hTS, hT'S⟩, if_pos hT'S]
        · rw [if_neg (fun h => hT'S h.2), if_neg hT'S]
      rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hcard : ((H.erase T).filter (fun T' => T' ⊆ S)).card = k - 1 := by
        have : (H.erase T).filter (fun T' => T' ⊆ S)
            = (H.filter (fun T' => T' ⊆ S)).erase T := by
          ext T'
          simp only [Finset.mem_filter, Finset.mem_erase]
          tauto
        rw [this, Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨hT, hTS⟩), hk]
      have hkpos : 1 ≤ k := by
        rw [hk]
        exact Finset.card_pos.2 ⟨T, Finset.mem_filter.2 ⟨hT, hTS⟩⟩
      rw [hcard]
      have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        have : (1 : ℕ) ≤ k := hkpos
        push_cast [Nat.cast_sub this]
        ring
      rw [this]
    · rw [if_neg hTS]
      refine Finset.sum_eq_zero fun T' _ => ?_
      rw [if_neg (fun h => hTS h.1)]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← hk]
  ring

/-- The second Bonferroni inequality for the events "`α_p` contains `T`". -/
theorem bonferroni_le_prob {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (H : Finset (Finset α)) :
    (∑ T ∈ H, p ^ T.card) - (∑ T ∈ H, ∑ T' ∈ H.erase T, p ^ (T ∪ T').card) / 2
      ≤ prob p (upClosure H) := by
  rw [sum_pow_card_eq, sum_pair_eq]
  have h2 : ∀ S : Finset α, (S ∈ upClosure H) ↔ 1 ≤ (H.filter (fun T => T ⊆ S)).card := by
    intro S
    simp only [upClosure, Finset.mem_filter, Finset.mem_univ, true_and,
      Nat.one_le_iff_ne_zero, ne_eq, Finset.card_eq_zero]
    constructor
    · rintro ⟨T, hT, hTS⟩ hempty
      have hmem : T ∈ H.filter (fun T => T ⊆ S) := Finset.mem_filter.2 ⟨hT, hTS⟩
      rw [hempty] at hmem
      exact absurd hmem (Finset.notMem_empty T)
    · intro hne
      obtain ⟨T, hT⟩ := Finset.nonempty_of_ne_empty hne
      exact ⟨T, (Finset.mem_filter.1 hT).1, (Finset.mem_filter.1 hT).2⟩
  have hset : Finset.univ.filter
      (fun S : Finset α => 1 ≤ (H.filter (fun T => T ⊆ S)).card) = upClosure H := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (h2 S).symm
  have hprob : prob p (upClosure H)
      = ∑ S : Finset α, weight p S * (if 1 ≤ (H.filter (fun T => T ⊆ S)).card then 1 else 0) := by
    rw [prob, ← hset, Finset.sum_filter]
    refine Finset.sum_congr rfl fun S _ => ?_
    split_ifs <;> ring
  rw [hprob, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun S _ => ?_
  set k : ℕ := (H.filter (fun T => T ⊆ S)).card with hk
  have hw : 0 ≤ weight p S := weight_nonneg hp0 hp1 S
  have hkey : (k : ℝ) - (k : ℝ) * ((k : ℝ) - 1) / 2 ≤ (if 1 ≤ k then (1 : ℝ) else 0) := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0]
      norm_num
    · have h0' : 1 ≤ k := h0
      rw [if_pos h0']
      rcases eq_or_lt_of_le h0' with h1 | h1
      · rw [← h1]
        norm_num
      · have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
        nlinarith
  calc weight p S * (k : ℝ) - weight p S * ((k : ℝ) * ((k : ℝ) - 1)) / 2
      = weight p S * ((k : ℝ) - (k : ℝ) * ((k : ℝ) - 1) / 2) := by ring
    _ ≤ weight p S * (if 1 ≤ k then (1 : ℝ) else 0) := by
        exact mul_le_mul_of_nonneg_left hkey hw

/-- **Park–Pham direction under a small-overlap hypothesis.**  If `H` has no empty member,
is not `q`-small, and the pairwise overlap sum at `p = min 1 (2q)` is less than `1`, then
`ℙ(α_p ∈ ⟨H⟩) > 1/2`. -/
theorem half_lt_prob_of_not_isSmall_of_smallOverlap {q : ℝ} (hq0 : 0 < q)
    {H : Finset (Finset α)} (hemp : ∅ ∉ H) (h : ¬ IsSmall q H)
    (hover : ∑ T ∈ H, ∑ T' ∈ H.erase T, (min 1 (2 * q)) ^ (T ∪ T').card < 1) :
    1 / 2 < prob (min 1 (2 * q)) (upClosure H) := by
  set p : ℝ := min 1 (2 * q) with hp
  have hp0 : 0 ≤ p := le_min (by norm_num) (by linarith)
  have hp1 : p ≤ 1 := min_le_left _ _
  have hsum : 1 / 2 < ∑ T ∈ H, q ^ T.card := half_lt_sum_of_not_isSmall h
  have hne : H.Nonempty := by
    rcases Finset.eq_empty_or_nonempty H with hh | hh
    · rw [hh] at hsum; simp at hsum; linarith
    · exact hh
  have hcard : ∀ T ∈ H, 1 ≤ T.card := by
    intro T hT
    rcases Nat.eq_zero_or_pos T.card with h0 | h0
    · exact absurd (Finset.card_eq_zero.1 h0 ▸ hT) hemp
    · exact h0
  rcases le_or_gt 1 (2 * q) with hcase | hcase
  · obtain ⟨T₀, hT₀⟩ := hne
    have hp1' : p = 1 := by simp [hp, min_eq_left hcase]
    refine half_lt_prob_of_mem hp0 hp1 hT₀ ?_
    rw [hp1']
    norm_num
  · have hpq : p = 2 * q := by simp [hp, min_eq_right hcase.le]
    have hbig : 1 < ∑ T ∈ H, p ^ T.card := by
      have hterm : ∀ T ∈ H, 2 * q ^ T.card ≤ p ^ T.card := by
        intro T hT
        have h1 : (1 : ℕ) ≤ T.card := hcard T hT
        have h2 : p ^ T.card = 2 ^ T.card * q ^ T.card := by rw [hpq, mul_pow]
        have h3 : (2 : ℝ) ≤ 2 ^ T.card := by
          calc (2 : ℝ) = 2 ^ (1 : ℕ) := by norm_num
            _ ≤ 2 ^ T.card := pow_le_pow_right₀ (by norm_num) h1
        have h4 : (0 : ℝ) ≤ q ^ T.card := pow_nonneg hq0.le _
        rw [h2]
        nlinarith
      have := Finset.sum_le_sum hterm
      rw [← Finset.mul_sum] at this
      linarith
    have := bonferroni_le_prob hp0 hp1 H
    linarith

/-! ### Main statement -/

/-- **Kahn–Kalai for families of pairwise disjoint sets.**

Let `H` be a family of pairwise disjoint subsets of a finite set, and let `0 < q ≤ 1`.
Then the threshold of the increasing family `⟨H⟩` and the expectation threshold agree up to a
factor `2` (for such families no logarithmic loss is needed):

* if `H` is `q`-small then `ℙ(α_q ∈ ⟨H⟩) ≤ 1/2`, i.e. `q ≤ p_c(⟨H⟩)`;
* if `H` is not `q`-small then `ℙ(α_p ∈ ⟨H⟩) > 1/2` for `p = min 1 (2q)`, i.e.
  `p_c(⟨H⟩) ≤ 2q`.

The first half is the easy direction of the Kahn–Kalai relation and is proved for *arbitrary*
families in `prob_le_half_of_isSmall` (union bound over a cover).  The second half is the
Park–Pham direction; it is proved here for pairwise disjoint families (which includes every
`1`-bounded family, see `half_lt_prob_of_not_isSmall_of_bounded_one`), where the events
"`α_p` contains `T`" are independent and the probability that no member is contained
factorises as `∏_{T ∈ H} (1 - p ^ |T|)`.  For families that are not disjoint but have a
small pairwise overlap term, see `half_lt_prob_of_not_isSmall_of_smallOverlap`. -/
theorem kahn_kalai {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    {H : Finset (Finset α)} (hdisj : ((H : Set (Finset α)).Pairwise Disjoint)) :
    (IsSmall q H → prob q (upClosure H) ≤ 1 / 2) ∧
      (¬ IsSmall q H → 1 / 2 < prob (min 1 (2 * q)) (upClosure H)) :=
  ⟨fun h => prob_le_half_of_isSmall hq0.le hq1 h,
    fun h => half_lt_prob_of_not_isSmall_of_pairwiseDisjoint hq0 hdisj h⟩

end Math2

