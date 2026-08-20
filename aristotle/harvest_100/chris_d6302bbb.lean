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

/-
Covers, costs, and minimum fragments (Park–Pham).
-/
import Mathlib
import RequestProject.KahnKalai.Measure

open Finset
open scoped Classical

namespace Math2

variable {α : Type*} [DecidableEq α]

/-! ## Covers and their costs -/

/-- `G` is a cover of `H`: every member of `H` contains a member of `G`. -/
def IsCover (G H : Finset (Finset α)) : Prop := ∀ S ∈ H, ∃ T ∈ G, T ⊆ S

/-- The cost `∑_{T ∈ G} q ^ |T|` of a family `G`. -/
noncomputable def cost (q : ℝ) (G : Finset (Finset α)) : ℝ := ∑ T ∈ G, q ^ T.card

/-- Talagrand's notion: `F` is `q`-small if it has a cover of cost at most `1/2`. -/
def IsSmall (q : ℝ) (F : Finset (Finset α)) : Prop :=
  ∃ G : Finset (Finset α), IsCover G F ∧ cost q G ≤ 1 / 2

/-- The minimal cost of a cover of `H`. -/
noncomputable def covCost (q : ℝ) (H : Finset (Finset α)) : ℝ :=
  sInf {x : ℝ | ∃ G : Finset (Finset α), IsCover G H ∧ x = cost q G}

lemma cost_nonneg {q : ℝ} (hq : 0 ≤ q) (G : Finset (Finset α)) : 0 ≤ cost q G :=
  Finset.sum_nonneg fun _ _ => pow_nonneg hq _

lemma cost_union_le {q : ℝ} (hq : 0 ≤ q) (G G' : Finset (Finset α)) :
    cost q (G ∪ G') ≤ cost q G + cost q G' := by
  classical
  have : cost q (G ∪ G') = cost q G + ∑ T ∈ G' \ G, q ^ T.card := by
    rw [cost, cost, ← Finset.sum_union (Finset.disjoint_sdiff)]
    congr 1
    ext T
    simp [Finset.mem_union]
  rw [this]
  have h2 : ∑ T ∈ G' \ G, q ^ T.card ≤ cost q G' :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
      (fun T _ _ => pow_nonneg hq _)
  linarith

lemma isCover_self (H : Finset (Finset α)) : IsCover H H := fun S hS => ⟨S, hS, subset_rfl⟩

lemma covCost_set_nonempty (q : ℝ) (H : Finset (Finset α)) :
    {x : ℝ | ∃ G : Finset (Finset α), IsCover G H ∧ x = cost q G}.Nonempty :=
  ⟨cost q H, H, isCover_self H, rfl⟩

lemma covCost_set_bddBelow {q : ℝ} (hq : 0 ≤ q) (H : Finset (Finset α)) :
    BddBelow {x : ℝ | ∃ G : Finset (Finset α), IsCover G H ∧ x = cost q G} := by
  refine ⟨0, ?_⟩
  rintro x ⟨G, -, rfl⟩
  exact cost_nonneg hq G

lemma covCost_le_cost {q : ℝ} (hq : 0 ≤ q) {G H : Finset (Finset α)} (h : IsCover G H) :
    covCost q H ≤ cost q G :=
  csInf_le (covCost_set_bddBelow hq H) ⟨G, h, rfl⟩

lemma le_covCost {q : ℝ} {H : Finset (Finset α)} {c : ℝ}
    (h : ∀ G : Finset (Finset α), IsCover G H → c ≤ cost q G) : c ≤ covCost q H := by
  refine le_csInf (covCost_set_nonempty q H) ?_
  rintro x ⟨G, hG, rfl⟩
  exact h G hG

lemma covCost_nonneg {q : ℝ} (hq : 0 ≤ q) (H : Finset (Finset α)) : 0 ≤ covCost q H :=
  le_covCost fun G _ => cost_nonneg hq G

lemma covCost_empty {q : ℝ} (hq : 0 ≤ q) : covCost q (∅ : Finset (Finset α)) = 0 := by
  refine le_antisymm ?_ (covCost_nonneg hq _)
  have : covCost q (∅ : Finset (Finset α)) ≤ cost q ∅ :=
    covCost_le_cost hq (by intro S hS; simp at hS)
  simpa [cost] using this

/-! ## Minimum fragments -/

/-- The candidate fragments of `S` with respect to `W`: sets of the form `S' \ W` for
edges `S'` of `H` inside `W ∪ S`. -/
noncomputable def cands (H : Finset (Finset α)) (S W : Finset α) : Finset (Finset α) :=
  (H.filter (fun S' => S' ⊆ W ∪ S)).image (fun S' => S' \ W)

lemma cands_nonempty {H : Finset (Finset α)} {S : Finset α} (hS : S ∈ H) (W : Finset α) :
    (cands H S W).Nonempty := by
  refine ⟨S \ W, ?_⟩
  refine Finset.mem_image.mpr ⟨S, ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨hS, Finset.subset_union_right⟩

/-- A minimum `(S, W)`-fragment: a smallest set of the form `S' \ W` with `S' ∈ H`,
`S' ⊆ W ∪ S`. -/
noncomputable def frag (H : Finset (Finset α)) (S W : Finset α) : Finset α :=
  if h : (cands H S W).Nonempty then
    (Finset.exists_min_image (cands H S W) Finset.card h).choose
  else ∅

lemma frag_mem {H : Finset (Finset α)} {S : Finset α} (hS : S ∈ H) (W : Finset α) :
    frag H S W ∈ cands H S W := by
  rw [frag, dif_pos (cands_nonempty hS W)]
  exact (Finset.exists_min_image (cands H S W) Finset.card (cands_nonempty hS W)).choose_spec.1

lemma frag_min {H : Finset (Finset α)} {S : Finset α} (hS : S ∈ H) (W : Finset α) :
    ∀ T ∈ cands H S W, (frag H S W).card ≤ T.card := by
  rw [frag, dif_pos (cands_nonempty hS W)]
  exact (Finset.exists_min_image (cands H S W) Finset.card (cands_nonempty hS W)).choose_spec.2

/-- A minimum fragment of `S` is a subset of `S`. -/
lemma frag_subset {H : Finset (Finset α)} {S : Finset α} (hS : S ∈ H) (W : Finset α) :
    frag H S W ⊆ S := by
  obtain ⟨S', hS', hEq⟩ := Finset.mem_image.mp (frag_mem hS W)
  rw [Finset.mem_filter] at hS'
  rw [← hEq]
  intro x hx
  rw [Finset.mem_sdiff] at hx
  rcases Finset.mem_union.mp (hS'.2 hx.1) with h | h
  · exact absurd h hx.2
  · exact h

/-- `W ∪ frag H S W` contains an edge of `H`. -/
lemma frag_capture {H : Finset (Finset α)} {S : Finset α} (hS : S ∈ H) (W : Finset α) :
    ∃ S' ∈ H, S' ⊆ W ∪ frag H S W := by
  obtain ⟨S', hS', hEq⟩ := Finset.mem_image.mp (frag_mem hS W)
  rw [Finset.mem_filter] at hS'
  refine ⟨S', hS'.1, ?_⟩
  intro x hx
  by_cases hxW : x ∈ W
  · exact Finset.mem_union_left _ hxW
  · exact Finset.mem_union_right _ (by rw [← hEq]; exact Finset.mem_sdiff.mpr ⟨hx, hxW⟩)

/-- Minimality: any edge of `H` inside `W ∪ frag H S W` contains the fragment. -/
lemma frag_subset_of_edge {H : Finset (Finset α)} {S : Finset α} (hS : S ∈ H) (W : Finset α)
    {Sh : Finset α} (hSh : Sh ∈ H) (hsub : Sh ⊆ W ∪ frag H S W) : frag H S W ⊆ Sh := by
  have hfragS : frag H S W ⊆ S := frag_subset hS W
  have hcand : Sh \ W ∈ cands H S W := by
    refine Finset.mem_image.mpr ⟨Sh, Finset.mem_filter.mpr ⟨hSh, ?_⟩, rfl⟩
    intro x hx
    rcases Finset.mem_union.mp (hsub hx) with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (hfragS h)
  have hle : (frag H S W).card ≤ (Sh \ W).card := frag_min hS W _ hcand
  have hsub2 : Sh \ W ⊆ frag H S W := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rcases Finset.mem_union.mp (hsub hx.1) with h | h
    · exact absurd h hx.2
    · exact h
  have : Sh \ W = frag H S W := Finset.eq_of_subset_of_card_le hsub2 hle
  rw [← this]
  exact Finset.sdiff_subset

/-! ## One step of the iteration -/

/-- The cover produced at one step: the minimum fragments that are too big. -/
noncomputable def Ucov (H : Finset (Finset α)) (b : ℕ) (W : Finset α) : Finset (Finset α) :=
  (H.filter (fun S => b < (frag H S W).card)).image (fun S => frag H S W)

/-- The hypergraph passed to the next step: the minimum fragments that are small. -/
noncomputable def Hnext (H : Finset (Finset α)) (b : ℕ) (W : Finset α) : Finset (Finset α) :=
  (H.filter (fun S => (frag H S W).card ≤ b)).image (fun S => frag H S W)

lemma Hnext_bounded (H : Finset (Finset α)) (b : ℕ) (W : Finset α) :
    ∀ T ∈ Hnext H b W, T.card ≤ b := by
  intro T hT
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
  exact (Finset.mem_filter.mp hS).2

lemma Hnext_capture (H : Finset (Finset α)) (b : ℕ) (W : Finset α) :
    ∀ T ∈ Hnext H b W, ∃ S' ∈ H, S' ⊆ W ∪ T := by
  intro T hT
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
  exact frag_capture (Finset.mem_filter.mp hS).1 W

/-- A cover of the next hypergraph, together with the step's cover, covers `H`. -/
lemma isCover_step {G H : Finset (Finset α)} {b : ℕ} {W : Finset α}
    (hG : IsCover G (Hnext H b W)) : IsCover (G ∪ Ucov H b W) H := by
  intro S hS
  by_cases hbig : b < (frag H S W).card
  · refine ⟨frag H S W, ?_, frag_subset hS W⟩
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨hS, hbig⟩, rfl⟩)
  · have hmem : frag H S W ∈ Hnext H b W :=
      Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨hS, not_lt.mp hbig⟩, rfl⟩
    obtain ⟨T, hT, hTsub⟩ := hG _ hmem
    exact ⟨T, Finset.mem_union_left _ hT, hTsub.trans (frag_subset hS W)⟩

/-- Cost recursion: the minimal cover cost of `H` is at most the cost of the step cover plus
the minimal cover cost of the next hypergraph. -/
lemma covCost_le_step {q : ℝ} (hq : 0 ≤ q) (H : Finset (Finset α)) (b : ℕ) (W : Finset α) :
    covCost q H ≤ cost q (Ucov H b W) + covCost q (Hnext H b W) := by
  have h : ∀ G : Finset (Finset α), IsCover G (Hnext H b W) →
      covCost q H - cost q (Ucov H b W) ≤ cost q G := by
    intro G hG
    have h1 : covCost q H ≤ cost q (G ∪ Ucov H b W) := covCost_le_cost hq (isCover_step hG)
    have h2 : cost q (G ∪ Ucov H b W) ≤ cost q G + cost q (Ucov H b W) :=
      cost_union_le hq _ _
    linarith
  have := le_covCost (q := q) (H := Hnext H b W) h
  linarith

end Math2

/-
The `p`-biased product measure on subsets of a finite set, as a finite sum.
-/
import Mathlib

open Finset

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The weight of the set `A` under the `p`-biased product measure on subsets of `α`:
each element is included independently with probability `p`. -/
noncomputable def nu (p : ℝ) (A : Finset α) : ℝ := ∏ x : α, (if x ∈ A then p else 1 - p)

/-- The `p`-biased measure of a family `F` of subsets of `α`. -/
noncomputable def mu (p : ℝ) (F : Finset (Finset α)) : ℝ := ∑ A ∈ F, nu p A

lemma nu_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (A : Finset α) : 0 ≤ nu p A := by
  refine Finset.prod_nonneg fun x _ => ?_
  by_cases hx : x ∈ A <;> simp [hx] <;> linarith

lemma mu_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (F : Finset (Finset α)) : 0 ≤ mu p F :=
  Finset.sum_nonneg fun A _ => nu_nonneg h0 h1 A

/-- Closed form for `nu`. -/
lemma nu_eq (p : ℝ) (A : Finset α) :
    nu p A = p ^ A.card * (1 - p) ^ (Fintype.card α - A.card) := by
  classical
  rw [nu, Finset.prod_ite]
  have h1 : (Finset.univ.filter (fun x : α => x ∈ A)) = A := by
    ext x; simp
  have h2 : (Finset.univ.filter (fun x : α => x ∉ A)) = Finset.univ \ A := by
    ext x; simp
  rw [h1, h2, Finset.prod_const, Finset.prod_const, Finset.card_univ_diff A]

/-- The total mass is `1`. -/
lemma sum_nu (p : ℝ) : ∑ A : Finset α, nu p A = 1 := by
  classical
  have := Finset.prod_add (fun _ : α => p) (fun _ : α => 1 - p) Finset.univ
  simp only [Finset.prod_const] at this
  have h1 : ∀ A : Finset α, nu p A = p ^ A.card * (1 - p) ^ (Finset.univ \ A).card := by
    intro A
    rw [nu_eq, Finset.card_univ_diff A]
  calc ∑ A : Finset α, nu p A
      = ∑ A ∈ (Finset.univ : Finset α).powerset, p ^ A.card * (1 - p) ^ (Finset.univ \ A).card := by
        rw [Finset.powerset_univ]
        exact Finset.sum_congr rfl fun A _ => h1 A
    _ = (p + (1 - p)) ^ (Finset.univ : Finset α).card := by
        rw [← this]
    _ = 1 := by norm_num

/-- Sum over a family, bounded by the total mass. -/
lemma mu_le_one {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (F : Finset (Finset α)) : mu p F ≤ 1 := by
  rw [← sum_nu (α := α) p]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
    (fun A _ _ => nu_nonneg h0 h1 A)

omit [Fintype α] in
/-- Auxiliary version of the "union of two independent random sets" identity, over an
arbitrary ground finset `X`. -/
lemma sum_powerset_union_aux (r s : ℝ) :
    ∀ (X : Finset α) (g : Finset α → ℝ),
      ∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
          (∏ x ∈ X, (if x ∈ W then r else 1 - r)) *
          (∏ x ∈ X, (if x ∈ V then s else 1 - s)) * g (W ∪ V)
        = ∑ U ∈ X.powerset,
          (∏ x ∈ X, (if x ∈ U then r + s - r * s else 1 - (r + s - r * s))) * g U := by
  classical
  intro X
  induction X using Finset.induction_on with
  | empty => intro g; simp
  | insert a X ha ih =>
      intro g
      have key : ∀ (c : ℝ) (W : Finset α), W ⊆ X →
          ((∏ x ∈ insert a X, (if x ∈ W then c else 1 - c))
              = (1 - c) * ∏ x ∈ X, (if x ∈ W then c else 1 - c))
            ∧ ((∏ x ∈ insert a X, (if x ∈ insert a W then c else 1 - c))
              = c * ∏ x ∈ X, (if x ∈ W then c else 1 - c)) := by
        intro c W hW
        have haW : a ∉ W := fun h => ha (hW h)
        have hcongr : ∀ x ∈ X, (if x ∈ insert a W then c else 1 - c)
            = (if x ∈ W then c else 1 - c) := by
          intro x hx
          have hxa : x ≠ a := fun h => ha (h ▸ hx)
          simp [Finset.mem_insert, hxa]
        refine ⟨?_, ?_⟩
        · rw [Finset.prod_insert ha]; simp [haW]
        · rw [Finset.prod_insert ha, Finset.prod_congr rfl hcongr]; simp
      have expand : ∀ (h : Finset α → ℝ) (c d : ℝ),
          (∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
            (c * ∏ x ∈ X, (if x ∈ W then r else 1 - r)) *
            (d * ∏ x ∈ X, (if x ∈ V then s else 1 - s)) * h (W ∪ V))
          = c * d * ∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
              (∏ x ∈ X, (if x ∈ W then r else 1 - r)) *
              (∏ x ∈ X, (if x ∈ V then s else 1 - s)) * h (W ∪ V) := by
        intro h c d
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun W _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun V _ => ?_
        ring
      have expand' : ∀ (h : Finset α → ℝ) (c : ℝ),
          (∑ U ∈ X.powerset, (c * ∏ x ∈ X, (if x ∈ U then r + s - r * s
              else 1 - (r + s - r * s))) * h U)
          = c * ∑ U ∈ X.powerset, (∏ x ∈ X, (if x ∈ U then r + s - r * s
              else 1 - (r + s - r * s))) * h U := by
        intro h c
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun U _ => ?_
        ring
      have e1 : (∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
            (∏ x ∈ insert a X, (if x ∈ W then r else 1 - r)) *
            (∏ x ∈ insert a X, (if x ∈ V then s else 1 - s)) * g (W ∪ V))
          = (1 - r) * (1 - s) * (∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
              (∏ x ∈ X, (if x ∈ W then r else 1 - r)) *
              (∏ x ∈ X, (if x ∈ V then s else 1 - s)) * g (W ∪ V)) := by
        rw [← expand g (1 - r) (1 - s)]
        refine Finset.sum_congr rfl fun W hW => Finset.sum_congr rfl fun V hV => ?_
        rw [(key r W (Finset.mem_powerset.mp hW)).1, (key s V (Finset.mem_powerset.mp hV)).1]
      have e2 : (∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
            (∏ x ∈ insert a X, (if x ∈ W then r else 1 - r)) *
            (∏ x ∈ insert a X, (if x ∈ insert a V then s else 1 - s)) * g (W ∪ insert a V))
          = (1 - r) * s * (∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
              (∏ x ∈ X, (if x ∈ W then r else 1 - r)) *
              (∏ x ∈ X, (if x ∈ V then s else 1 - s)) * g (insert a (W ∪ V))) := by
        rw [← expand (fun U => g (insert a U)) (1 - r) s]
        refine Finset.sum_congr rfl fun W hW => Finset.sum_congr rfl fun V hV => ?_
        rw [(key r W (Finset.mem_powerset.mp hW)).1, (key s V (Finset.mem_powerset.mp hV)).2,
          Finset.union_insert]
      have e3 : (∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
            (∏ x ∈ insert a X, (if x ∈ insert a W then r else 1 - r)) *
            (∏ x ∈ insert a X, (if x ∈ V then s else 1 - s)) * g (insert a W ∪ V))
          = r * (1 - s) * (∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
              (∏ x ∈ X, (if x ∈ W then r else 1 - r)) *
              (∏ x ∈ X, (if x ∈ V then s else 1 - s)) * g (insert a (W ∪ V))) := by
        rw [← expand (fun U => g (insert a U)) r (1 - s)]
        refine Finset.sum_congr rfl fun W hW => Finset.sum_congr rfl fun V hV => ?_
        rw [(key r W (Finset.mem_powerset.mp hW)).2, (key s V (Finset.mem_powerset.mp hV)).1,
          Finset.insert_union]
      have e4 : (∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
            (∏ x ∈ insert a X, (if x ∈ insert a W then r else 1 - r)) *
            (∏ x ∈ insert a X, (if x ∈ insert a V then s else 1 - s)) *
              g (insert a W ∪ insert a V))
          = r * s * (∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
              (∏ x ∈ X, (if x ∈ W then r else 1 - r)) *
              (∏ x ∈ X, (if x ∈ V then s else 1 - s)) * g (insert a (W ∪ V))) := by
        rw [← expand (fun U => g (insert a U)) r s]
        refine Finset.sum_congr rfl fun W hW => Finset.sum_congr rfl fun V hV => ?_
        rw [(key r W (Finset.mem_powerset.mp hW)).2, (key s V (Finset.mem_powerset.mp hV)).2,
          Finset.insert_union, Finset.union_insert, Finset.insert_idem]
      have e5 : (∑ U ∈ X.powerset, (∏ x ∈ insert a X, (if x ∈ U then r + s - r * s
              else 1 - (r + s - r * s))) * g U)
          = (1 - (r + s - r * s)) * ∑ U ∈ X.powerset,
              (∏ x ∈ X, (if x ∈ U then r + s - r * s else 1 - (r + s - r * s))) * g U := by
        rw [← expand' g (1 - (r + s - r * s))]
        refine Finset.sum_congr rfl fun U hU => ?_
        rw [(key (r + s - r * s) U (Finset.mem_powerset.mp hU)).1]
      have e6 : (∑ U ∈ X.powerset, (∏ x ∈ insert a X, (if x ∈ insert a U then r + s - r * s
              else 1 - (r + s - r * s))) * g (insert a U))
          = (r + s - r * s) * ∑ U ∈ X.powerset,
              (∏ x ∈ X, (if x ∈ U then r + s - r * s else 1 - (r + s - r * s)))
                * g (insert a U) := by
        rw [← expand' (fun U => g (insert a U)) (r + s - r * s)]
        refine Finset.sum_congr rfl fun U hU => ?_
        rw [(key (r + s - r * s) U (Finset.mem_powerset.mp hU)).2]
      simp only [Finset.sum_powerset_insert ha, Finset.sum_add_distrib]
      rw [e1, e2, e3, e4, e5, e6, ih g, ih fun U => g (insert a U)]
      ring

/-- If `W` is `r`-random and `V` is `s`-random, independently, then `W ∪ V` is
`(r + s - r*s)`-random. -/
lemma sum_nu_union (r s : ℝ) (g : Finset α → ℝ) :
    ∑ W : Finset α, ∑ V : Finset α, nu r W * nu s V * g (W ∪ V)
      = ∑ U : Finset α, nu (r + s - r * s) U * g U := by
  classical
  have h := sum_powerset_union_aux (α := α) r s Finset.univ g
  simpa [Finset.powerset_univ, nu] using h

end Math2

/-
The iteration of Park–Pham: at each round the bound on the size of the edges is halved.
-/
import Mathlib
import RequestProject.KahnKalai.KeyLemma

open Finset
open scoped Classical

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The number of halving rounds needed to get from `b` down to `0`
(so `rounds b = ⌊log₂ b⌋ + 1` for `b ≥ 1`). -/
def rounds : ℕ → ℕ
  | 0 => 0
  | (n + 1) => rounds ((n + 1) / 2) + 1
decreasing_by omega

/-- The probability that a `p`-random subset contains no edge of `H`. -/
noncomputable def Fail (p : ℝ) (H : Finset (Finset α)) : ℝ :=
  ∑ V : Finset α, nu p V * (if ∃ S ∈ H, S ⊆ V then 0 else 1)

/-- The density of the union of `rounds b` independent `r`-random subsets. -/
noncomputable def pp (r : ℝ) (b : ℕ) : ℝ := 1 - (1 - r) ^ (rounds b)

/-- The expected total cost of the covers produced along the iteration. -/
noncomputable def Psi (r q : ℝ) (H : Finset (Finset α)) (b : ℕ) : ℝ :=
  match b with
  | 0 => 0
  | (n + 1) => ∑ W : Finset α, nu r W *
      (cost q (Ucov H ((n + 1) / 2) W) + Psi r q (Hnext H ((n + 1) / 2) W) ((n + 1) / 2))
termination_by b
decreasing_by omega

lemma Psi_zero (r q : ℝ) (H : Finset (Finset α)) : Psi r q H 0 = 0 := by rw [Psi]

lemma Psi_succ (r q : ℝ) (H : Finset (Finset α)) (n : ℕ) :
    Psi r q H (n + 1) = ∑ W : Finset α, nu r W *
      (cost q (Ucov H ((n + 1) / 2) W) + Psi r q (Hnext H ((n + 1) / 2) W) ((n + 1) / 2)) := by
  rw [Psi]

lemma pp_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b : ℕ) : 0 ≤ pp r b := by
  have : (1 - r) ^ (rounds b) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  simp only [pp]
  linarith

lemma pp_le_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b : ℕ) : pp r b ≤ 1 := by
  have : 0 ≤ (1 - r) ^ (rounds b) := pow_nonneg (by linarith) _
  simp only [pp]
  linarith

lemma pp_succ (r : ℝ) (n : ℕ) :
    pp r (n + 1) = r + pp r ((n + 1) / 2) - r * pp r ((n + 1) / 2) := by
  simp only [pp, rounds]
  ring

lemma Fail_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (H : Finset (Finset α)) : 0 ≤ Fail p H :=
  Finset.sum_nonneg fun V _ => mul_nonneg (nu_nonneg h0 h1 V) (by split <;> norm_num)

lemma Fail_le_one {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (H : Finset (Finset α)) : Fail p H ≤ 1 := by
  calc Fail p H ≤ ∑ V : Finset α, nu p V * 1 := by
        refine Finset.sum_le_sum fun V _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (nu_nonneg h0 h1 V)
        split <;> norm_num
    _ = 1 := by simpa using sum_nu (α := α) p

/-- One round of the process: failing to contain an edge of `H` after all the rounds implies
failing to contain an edge of the next hypergraph after the remaining rounds. -/
lemma Fail_step {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (H : Finset (Finset α)) (n : ℕ) :
    Fail (pp r (n + 1)) H
      ≤ ∑ W : Finset α, nu r W * Fail (pp r ((n + 1) / 2)) (Hnext H ((n + 1) / 2) W) := by
  classical
  set b' := (n + 1) / 2 with hb'
  set s := pp r b' with hs
  have hs0 : 0 ≤ s := pp_nonneg hr0 hr1 b'
  have hs1 : s ≤ 1 := pp_le_one hr0 hr1 b'
  have hrew : Fail (pp r (n + 1)) H
      = ∑ W : Finset α, ∑ V : Finset α,
          nu r W * nu s V * (if ∃ S ∈ H, S ⊆ W ∪ V then 0 else 1) := by
    rw [pp_succ, Fail, ← hs]
    exact (sum_nu_union r s (fun U => if ∃ S ∈ H, S ⊆ U then 0 else 1)).symm
  rw [hrew]
  refine Finset.sum_le_sum fun W _ => ?_
  rw [Fail, Finset.mul_sum]
  refine Finset.sum_le_sum fun V _ => ?_
  have hnu : 0 ≤ nu r W * nu s V := mul_nonneg (nu_nonneg hr0 hr1 W) (nu_nonneg hs0 hs1 V)
  have hind : (if ∃ S ∈ H, S ⊆ W ∪ V then (0:ℝ) else 1)
      ≤ (if ∃ T ∈ Hnext H b' W, T ⊆ V then (0:ℝ) else 1) := by
    by_cases hT : ∃ T ∈ Hnext H b' W, T ⊆ V
    · obtain ⟨T, hTmem, hTV⟩ := hT
      obtain ⟨S', hS', hS'sub⟩ := Hnext_capture H b' W T hTmem
      have : ∃ S ∈ H, S ⊆ W ∪ V := by
        refine ⟨S', hS', hS'sub.trans ?_⟩
        exact Finset.union_subset_union_right hTV
      simp only [this, if_true]
      split <;> norm_num
    · simp [hT]
      split <;> norm_num
  calc nu r W * nu s V * (if ∃ S ∈ H, S ⊆ W ∪ V then (0:ℝ) else 1)
      ≤ nu r W * nu s V * (if ∃ T ∈ Hnext H b' W, T ⊆ V then (0:ℝ) else 1) :=
        mul_le_mul_of_nonneg_left hind hnu
    _ = nu r W * (nu s V * (if ∃ T ∈ Hnext H b' W, T ⊆ V then (0:ℝ) else 1)) := by ring

/-- **The main induction.** For a `b`-bounded hypergraph `H`, the failure probability after
`rounds b` rounds, weighted by the minimal cover cost, is at most `Psi`. -/
theorem covCost_mul_Fail_le {q r : ℝ} (hq : 0 ≤ q) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b : ℕ) :
    ∀ H : Finset (Finset α), (∀ S ∈ H, S.card ≤ b) →
      covCost q H * Fail (pp r b) H ≤ Psi r q H b := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    match b with
    | 0 =>
      intro H hH
      rw [Psi_zero]
      by_cases hemp : H = ∅
      · subst hemp
        rw [covCost_empty hq]
        simp
      · obtain ⟨S, hS⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
        have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (hH S hS))
        have hFail : Fail (pp r 0) H = 0 := by
          rw [Fail]
          refine Finset.sum_eq_zero fun V _ => ?_
          have : ∃ S' ∈ H, S' ⊆ V := ⟨S, hS, by rw [hS0]; exact Finset.empty_subset V⟩
          simp [this]
        rw [hFail, mul_zero]
    | (n + 1) =>
      intro H hH
      set b' := (n + 1) / 2 with hb'
      have hb'lt : b' < n + 1 := by omega
      have hs0 : 0 ≤ pp r b' := pp_nonneg hr0 hr1 b'
      have hs1 : pp r b' ≤ 1 := pp_le_one hr0 hr1 b'
      calc covCost q H * Fail (pp r (n + 1)) H
          ≤ covCost q H * ∑ W : Finset α, nu r W * Fail (pp r b') (Hnext H b' W) :=
            mul_le_mul_of_nonneg_left (Fail_step hr0 hr1 H n) (covCost_nonneg hq H)
        _ = ∑ W : Finset α, nu r W * (covCost q H * Fail (pp r b') (Hnext H b' W)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun W _ => by ring
        _ ≤ ∑ W : Finset α, nu r W * (cost q (Ucov H b' W) + Psi r q (Hnext H b' W) b') := by
            refine Finset.sum_le_sum fun W _ => ?_
            refine mul_le_mul_of_nonneg_left ?_ (nu_nonneg hr0 hr1 W)
            have hstep := covCost_le_step hq H b' W
            have hIH := ih b' hb'lt (Hnext H b' W) (Hnext_bounded H b' W)
            have hF0 := Fail_nonneg hs0 hs1 (Hnext H b' W)
            have hF1 := Fail_le_one hs0 hs1 (Hnext H b' W)
            have hc := cost_nonneg hq (Ucov H b' W)
            have e1 : covCost q H * Fail (pp r b') (Hnext H b' W)
                ≤ (cost q (Ucov H b' W) + covCost q (Hnext H b' W))
                    * Fail (pp r b') (Hnext H b' W) :=
              mul_le_mul_of_nonneg_right hstep hF0
            rw [add_mul] at e1
            have e2 : cost q (Ucov H b' W) * Fail (pp r b') (Hnext H b' W)
                ≤ cost q (Ucov H b' W) := mul_le_of_le_one_right hc hF1
            linarith
        _ = Psi r q H (n + 1) := (Psi_succ r q H n).symm

/-! ## Bounding `Psi` -/

lemma geom_sum_two_bound {y : ℝ} (h0 : 0 ≤ y) (h : y ≤ 1 / 2) (b : ℕ) :
    ∑ m ∈ Finset.range b, y ^ m ≤ 2 := by
  have h1 : ∑ m ∈ Finset.range b, y ^ m ≤ ∑ m ∈ Finset.range b, ((1 : ℝ) / 2) ^ m := by
    gcongr with i hi
  exact le_trans h1 (sum_geometric_two_le b)

/-- The arithmetic estimate behind one step of the bound on `Psi`. -/
lemma geom_step_bound {q r : ℝ} (hq : 0 < q) (hr : 64 * q ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    (2 : ℝ) ^ (n + 1) * ∑ m ∈ Finset.Ico ((n + 1) / 2 + 1) (n + 2), (q / r) ^ m
      ≤ (4 * q / r) ^ ((n + 1) / 2 + 1) := by
  set b' := (n + 1) / 2 with hb'
  have hr0 : 0 < r := lt_of_lt_of_le (by linarith) hr
  set ρ : ℝ := q / r with hρ
  have hρ0 : 0 < ρ := div_pos hq hr0
  have hρle : ρ ≤ 1 / 64 := by
    rw [hρ, div_le_iff₀ hr0]
    linarith
  have hsum : ∑ m ∈ Finset.Ico (b' + 1) (n + 2), ρ ^ m
      = ρ ^ (b' + 1) * ∑ j ∈ Finset.range (n + 2 - (b' + 1)), ρ ^ j := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_add]
  have hgeom : ∑ j ∈ Finset.range (n + 2 - (b' + 1)), ρ ^ j ≤ 2 :=
    geom_sum_two_bound hρ0.le (by linarith) _
  have hpow : (2 : ℝ) ^ (n + 1) * 2 ≤ 4 ^ (b' + 1) := by
    have h4 : (4 : ℝ) ^ (b' + 1) = 2 ^ (2 * (b' + 1)) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [h4, show (2 : ℝ) ^ (n + 1) * 2 = 2 ^ (n + 2) by ring]
    refine pow_le_pow_right₀ (by norm_num) ?_
    omega
  have hfinal : (4 * q / r) ^ (b' + 1) = 4 ^ (b' + 1) * ρ ^ (b' + 1) := by
    rw [hρ, ← mul_pow]
    congr 1
    field_simp
  rw [hsum, hfinal]
  have hpos : (0 : ℝ) < ρ ^ (b' + 1) := pow_pos hρ0 _
  calc (2 : ℝ) ^ (n + 1) * (ρ ^ (b' + 1) * ∑ j ∈ Finset.range (n + 2 - (b' + 1)), ρ ^ j)
      ≤ (2 : ℝ) ^ (n + 1) * (ρ ^ (b' + 1) * 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hgeom hpos.le
    _ = ((2 : ℝ) ^ (n + 1) * 2) * ρ ^ (b' + 1) := by ring
    _ ≤ 4 ^ (b' + 1) * ρ ^ (b' + 1) := mul_le_mul_of_nonneg_right hpow hpos.le

/-- **The bound on `Psi`.** -/
theorem Psi_le {q r : ℝ} (hq : 0 < q) (hr : 64 * q ≤ r) (hr1 : r ≤ 1) (b : ℕ) :
    ∀ H : Finset (Finset α), (∀ S ∈ H, S.card ≤ b) →
      Psi r q H b ≤ ∑ m ∈ Finset.range b, (4 * q / r) ^ (m + 1) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by linarith) hr
  have hy0 : 0 ≤ 4 * q / r := by positivity
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    match b with
    | 0 => intro H hH; rw [Psi_zero]; simp
    | (n + 1) =>
      intro H hH
      set b' := (n + 1) / 2 with hb'
      have hb'lt : b' < n + 1 := by omega
      rw [Psi_succ]
      have hsplit : ∑ W : Finset α, nu r W *
            (cost q (Ucov H b' W) + Psi r q (Hnext H b' W) b')
          = (∑ W : Finset α, nu r W * cost q (Ucov H b' W))
            + ∑ W : Finset α, nu r W * Psi r q (Hnext H b' W) b' := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun W _ => by ring
      have hfirst : ∑ W : Finset α, nu r W * cost q (Ucov H b' W)
          ≤ (4 * q / r) ^ (b' + 1) := by
        refine le_trans (expected_cost_le hH hq.le hr0 hr1 b') ?_
        exact geom_step_bound hq hr hr1 n
      have hsecond : ∑ W : Finset α, nu r W * Psi r q (Hnext H b' W) b'
          ≤ ∑ m ∈ Finset.range b', (4 * q / r) ^ (m + 1) := by
        calc ∑ W : Finset α, nu r W * Psi r q (Hnext H b' W) b'
            ≤ ∑ W : Finset α, nu r W * ∑ m ∈ Finset.range b', (4 * q / r) ^ (m + 1) := by
              refine Finset.sum_le_sum fun W _ => ?_
              exact mul_le_mul_of_nonneg_left
                (ih b' hb'lt (Hnext H b' W) (Hnext_bounded H b' W))
                (nu_nonneg hr0.le hr1 W)
          _ = ∑ m ∈ Finset.range b', (4 * q / r) ^ (m + 1) := by
              rw [← Finset.sum_mul, sum_nu, one_mul]
      have hcomb : ∑ m ∈ Finset.range b', (4 * q / r) ^ (m + 1) + (4 * q / r) ^ (b' + 1)
          = ∑ m ∈ Finset.range (b' + 1), (4 * q / r) ^ (m + 1) := by
        rw [Finset.sum_range_succ]
      have hmono : ∑ m ∈ Finset.range (b' + 1), (4 * q / r) ^ (m + 1)
          ≤ ∑ m ∈ Finset.range (n + 1), (4 * q / r) ^ (m + 1) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => by positivity)
        intro m hm
        simp only [Finset.mem_range] at hm ⊢
        omega
      rw [hsplit]
      linarith

/-- The total bound: `Psi` is at most `8 * q / r`. -/
theorem Psi_le_const {q r : ℝ} (hq : 0 < q) (hr : 64 * q ≤ r) (hr1 : r ≤ 1) (b : ℕ)
    (H : Finset (Finset α)) (hH : ∀ S ∈ H, S.card ≤ b) : Psi r q H b ≤ 8 * q / r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by linarith) hr
  have hy0 : 0 ≤ 4 * q / r := by positivity
  have hy : 4 * q / r ≤ 1 / 2 := by
    rw [div_le_iff₀ hr0]
    linarith
  have h1 : ∑ m ∈ Finset.range b, (4 * q / r) ^ (m + 1)
      = (4 * q / r) * ∑ m ∈ Finset.range b, (4 * q / r) ^ m := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [pow_succ]; ring
  have h2 : ∑ m ∈ Finset.range b, (4 * q / r) ^ m ≤ 2 := geom_sum_two_bound hy0 hy b
  have h3 : ∑ m ∈ Finset.range b, (4 * q / r) ^ (m + 1) ≤ 8 * q / r := by
    rw [h1]
    calc (4 * q / r) * ∑ m ∈ Finset.range b, (4 * q / r) ^ m
        ≤ (4 * q / r) * 2 := mul_le_mul_of_nonneg_left h2 hy0
      _ = 8 * q / r := by ring
  exact le_trans (Psi_le hq hr hr1 b H hH) h3

end Math2

/-
The key lemma of Park–Pham: the cover produced at one step of the iteration has small
expected cost.
-/
import Mathlib
import RequestProject.KahnKalai.Cover

open Finset
open scoped Classical

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A canonical edge of `H` contained in `Z` (or `∅` if there is none). -/
noncomputable def pick (H : Finset (Finset α)) (Z : Finset α) : Finset α :=
  if h : ∃ S ∈ H, S ⊆ Z then h.choose else ∅

lemma pick_spec {H : Finset (Finset α)} {Z : Finset α} (h : ∃ S ∈ H, S ⊆ Z) :
    pick H Z ∈ H ∧ pick H Z ⊆ Z := by
  rw [pick, dif_pos h]
  exact ⟨h.choose_spec.1, h.choose_spec.2⟩

lemma card_pick_le {H : Finset (Finset α)} {l : ℕ} (hH : ∀ S ∈ H, S.card ≤ l) (Z : Finset α) :
    (pick H Z).card ≤ l := by
  by_cases h : ∃ S ∈ H, S ⊆ Z
  · exact hH _ (pick_spec h).1
  · rw [pick, dif_neg h]; simp

lemma frag_disjoint {H : Finset (Finset α)} {S : Finset α} (hS : S ∈ H) (W : Finset α) :
    Disjoint W (frag H S W) := by
  obtain ⟨S', -, hEq⟩ := Finset.mem_image.mp (frag_mem hS W)
  rw [← hEq]
  exact Finset.disjoint_sdiff

/-- Reweighting: adding a disjoint set of size `m` to `W` multiplies the weight by
`(r / (1-r))^m`. -/
lemma nu_split {r : ℝ} (hr : 0 < r) {W U : Finset α} (hd : Disjoint W U) :
    nu r W = nu r (W ∪ U) * ((1 - r) / r) ^ U.card := by
  have hcard : (W ∪ U).card = W.card + U.card := Finset.card_union_of_disjoint hd
  have hle : (W ∪ U).card ≤ Fintype.card α := Finset.card_le_univ _
  rw [nu_eq, nu_eq, hcard]
  have h1 : Fintype.card α - W.card = (Fintype.card α - (W.card + U.card)) + U.card := by
    omega
  rw [h1, pow_add, pow_add, div_pow]
  field_simp

/-- Every member of the step cover has size in `(b, l]`. -/
lemma Ucov_card_mem {H : Finset (Finset α)} {l : ℕ} (hH : ∀ S ∈ H, S.card ≤ l) (b : ℕ)
    (W : Finset α) : ∀ U ∈ Ucov H b W, U.card ∈ Finset.Ico (b + 1) (l + 1) := by
  intro U hU
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hU
  rw [Finset.mem_filter] at hS
  have h1 : b < (frag H S W).card := hS.2
  have h2 : (frag H S W).card ≤ l :=
    le_trans (Finset.card_le_card (frag_subset hS.1 W)) (hH _ hS.1)
  simp only [Finset.mem_Ico]
  omega

/-- Decomposition of the cost of the step cover by the size of its members. -/
lemma cost_Ucov_eq {H : Finset (Finset α)} {l : ℕ} (hH : ∀ S ∈ H, S.card ≤ l) (q : ℝ) (b : ℕ)
    (W : Finset α) :
    cost q (Ucov H b W)
      = ∑ m ∈ Finset.Ico (b + 1) (l + 1),
          (((Ucov H b W).filter (fun U => U.card = m)).card : ℝ) * q ^ m := by
  classical
  rw [cost, ← Finset.sum_fiberwise_of_maps_to (Ucov_card_mem hH b W) (fun U => q ^ U.card)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hcard : ∀ U ∈ (Ucov H b W).filter (fun U => U.card = m), q ^ U.card = q ^ m := by
    intro U hU
    rw [(Finset.mem_filter.mp hU).2]
  refine (Finset.sum_congr rfl hcard).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-- The "double counting" bound: the pairs `(W, U)` with `U` a minimum fragment of size `m`
carry total weight at most `2 ^ l`. -/
lemma double_sum_bound {H : Finset (Finset α)} {l : ℕ} (hH : ∀ S ∈ H, S.card ≤ l)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b m : ℕ) :
    ∑ W : Finset α, ∑ U ∈ (Ucov H b W).filter (fun U => U.card = m), nu r (W ∪ U) ≤ 2 ^ l := by
  classical
  set D : Finset (Finset α × Finset α) :=
    (Finset.univ : Finset (Finset α × Finset α)).filter
      (fun z => z.2 ∈ Ucov H b z.1 ∧ z.2.card = m) with hD
  set E : Finset (Finset α × Finset α) :=
    (Finset.univ : Finset (Finset α × Finset α)).filter (fun z => z.2 ⊆ pick H z.1) with hE
  have hDsum : ∑ W : Finset α, ∑ U ∈ (Ucov H b W).filter (fun U => U.card = m), nu r (W ∪ U)
      = ∑ z ∈ D, nu r (z.1 ∪ z.2) := by
    rw [hD, Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun W _ => ?_
    dsimp only
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun U _ => rfl)
    ext U
    simp [Finset.mem_filter]
  -- the injection
  have hinj : Set.InjOn (fun z : Finset α × Finset α => (z.1 ∪ z.2, z.2)) D := by
    intro z hz z' hz' heq
    simp only [Prod.mk.injEq] at heq
    have h2 : z.2 = z'.2 := heq.2
    have hdz : Disjoint z.1 z.2 := by
      rw [hD, Finset.mem_coe, Finset.mem_filter] at hz
      obtain ⟨S, hS, hSe⟩ := Finset.mem_image.mp hz.2.1
      rw [← hSe]
      exact frag_disjoint (Finset.mem_filter.mp hS).1 z.1
    have hdz' : Disjoint z'.1 z'.2 := by
      rw [hD, Finset.mem_coe, Finset.mem_filter] at hz'
      obtain ⟨S, hS, hSe⟩ := Finset.mem_image.mp hz'.2.1
      rw [← hSe]
      exact frag_disjoint (Finset.mem_filter.mp hS).1 z'.1
    have h1 : z.1 = z'.1 := by
      have e1 : (z.1 ∪ z.2) \ z.2 = z.1 := by
        rw [Finset.union_sdiff_right]
        exact Finset.sdiff_eq_self_of_disjoint hdz
      have e2 : (z'.1 ∪ z'.2) \ z'.2 = z'.1 := by
        rw [Finset.union_sdiff_right]
        exact Finset.sdiff_eq_self_of_disjoint hdz'
      rw [← e1, ← e2, heq.1, h2]
    exact Prod.ext h1 h2
  have himage : D.image (fun z : Finset α × Finset α => (z.1 ∪ z.2, z.2)) ⊆ E := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    rw [hD, Finset.mem_filter] at hz
    obtain ⟨S, hS, hSe⟩ := Finset.mem_image.mp hz.2.1
    have hSH : S ∈ H := (Finset.mem_filter.mp hS).1
    have hcap : ∃ S' ∈ H, S' ⊆ z.1 ∪ z.2 := by
      rw [← hSe]; exact frag_capture hSH z.1
    have hpick := pick_spec hcap
    have hsub : pick H (z.1 ∪ z.2) ⊆ z.1 ∪ frag H S z.1 := by
      rw [hSe]; exact hpick.2
    have hfin : frag H S z.1 ⊆ pick H (z.1 ∪ z.2) := frag_subset_of_edge hSH z.1 hpick.1 hsub
    rw [hSe] at hfin
    rw [hE, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hfin⟩
  have hstep1 : ∑ z ∈ D, nu r (z.1 ∪ z.2)
      = ∑ w ∈ D.image (fun z : Finset α × Finset α => (z.1 ∪ z.2, z.2)), nu r w.1 := by
    rw [Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
  have hstep2 : ∑ w ∈ D.image (fun z : Finset α × Finset α => (z.1 ∪ z.2, z.2)), nu r w.1
      ≤ ∑ w ∈ E, nu r w.1 :=
    Finset.sum_le_sum_of_subset_of_nonneg himage (fun w _ _ => nu_nonneg hr0 hr1 w.1)
  have hstep3 : ∑ w ∈ E, nu r w.1 ≤ 2 ^ l := by
    have hEsum : ∑ w ∈ E, nu r w.1
        = ∑ Z : Finset α, nu r Z * ((2 : ℝ) ^ (pick H Z).card) := by
      rw [hE, Finset.sum_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun Z _ => ?_
      dsimp only
      rw [← Finset.sum_filter]
      have hset : (Finset.univ.filter (fun U : Finset α => U ⊆ pick H Z))
          = (pick H Z).powerset := by
        ext U; simp
      rw [hset, Finset.sum_const, nsmul_eq_mul, Finset.card_powerset]
      push_cast
      ring
    rw [hEsum]
    calc ∑ Z : Finset α, nu r Z * ((2 : ℝ) ^ (pick H Z).card)
        ≤ ∑ Z : Finset α, nu r Z * (2 ^ l : ℝ) := by
          refine Finset.sum_le_sum fun Z _ => ?_
          have h1 : ((2 : ℝ) ^ (pick H Z).card) ≤ (2 ^ l : ℝ) := by
            exact pow_le_pow_right₀ (by norm_num) (card_pick_le hH Z)
          exact mul_le_mul_of_nonneg_left h1 (nu_nonneg hr0 hr1 Z)
      _ = 2 ^ l := by rw [← Finset.sum_mul, sum_nu, one_mul]
  rw [hDsum, hstep1]
  linarith [hstep2, hstep3]

/-- For each fragment size `m`, the expected contribution to the cost is at most
`2 ^ l * (q / r) ^ m`. -/
lemma per_size_bound {H : Finset (Finset α)} {l : ℕ} (hH : ∀ S ∈ H, S.card ≤ l)
    {q r : ℝ} (hq : 0 ≤ q) (hr0 : 0 < r) (hr1 : r ≤ 1) (b m : ℕ) :
    ∑ W : Finset α, nu r W * ((((Ucov H b W).filter (fun U => U.card = m)).card : ℝ) * q ^ m)
      ≤ 2 ^ l * (q / r) ^ m := by
  classical
  have hkey : ∀ W : Finset α,
      nu r W * ((((Ucov H b W).filter (fun U => U.card = m)).card : ℝ) * q ^ m)
        ≤ (q ^ m * (1 / r) ^ m) *
            ∑ U ∈ (Ucov H b W).filter (fun U => U.card = m), nu r (W ∪ U) := by
    intro W
    have hexp : ∀ U ∈ (Ucov H b W).filter (fun U => U.card = m),
        nu r W = nu r (W ∪ U) * ((1 - r) / r) ^ m := by
      intro U hU
      rw [Finset.mem_filter] at hU
      obtain ⟨S, hS, hSe⟩ := Finset.mem_image.mp hU.1
      have hd : Disjoint W U := by
        rw [← hSe]; exact frag_disjoint (Finset.mem_filter.mp hS).1 W
      rw [nu_split hr0 hd, hU.2]
    have hsum : nu r W * (((Ucov H b W).filter (fun U => U.card = m)).card : ℝ)
        = ∑ U ∈ (Ucov H b W).filter (fun U => U.card = m), nu r (W ∪ U) * ((1 - r) / r) ^ m := by
      rw [← Finset.sum_congr rfl hexp, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hrle : ((1 - r) / r) ^ m ≤ (1 / r) ^ m := by
      gcongr
      · exact div_nonneg (by linarith) hr0.le
      · linarith
    calc nu r W * ((((Ucov H b W).filter (fun U => U.card = m)).card : ℝ) * q ^ m)
        = (nu r W * (((Ucov H b W).filter (fun U => U.card = m)).card : ℝ)) * q ^ m := by ring
      _ = (∑ U ∈ (Ucov H b W).filter (fun U => U.card = m),
            nu r (W ∪ U) * ((1 - r) / r) ^ m) * q ^ m := by rw [hsum]
      _ ≤ (∑ U ∈ (Ucov H b W).filter (fun U => U.card = m),
            nu r (W ∪ U) * (1 / r) ^ m) * q ^ m := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hq m)
          refine Finset.sum_le_sum fun U _ => ?_
          exact mul_le_mul_of_nonneg_left hrle (nu_nonneg (le_of_lt hr0) hr1 _)
      _ = (q ^ m * (1 / r) ^ m) *
            ∑ U ∈ (Ucov H b W).filter (fun U => U.card = m), nu r (W ∪ U) := by
          rw [← Finset.sum_mul]; ring
  calc ∑ W : Finset α, nu r W * ((((Ucov H b W).filter (fun U => U.card = m)).card : ℝ) * q ^ m)
      ≤ ∑ W : Finset α, (q ^ m * (1 / r) ^ m) *
          ∑ U ∈ (Ucov H b W).filter (fun U => U.card = m), nu r (W ∪ U) :=
        Finset.sum_le_sum fun W _ => hkey W
    _ = (q ^ m * (1 / r) ^ m) * ∑ W : Finset α,
          ∑ U ∈ (Ucov H b W).filter (fun U => U.card = m), nu r (W ∪ U) := by
        rw [← Finset.mul_sum]
    _ ≤ (q ^ m * (1 / r) ^ m) * 2 ^ l := by
        refine mul_le_mul_of_nonneg_left (double_sum_bound hH (le_of_lt hr0) hr1 b m) ?_
        positivity
    _ = 2 ^ l * (q / r) ^ m := by
        rw [div_pow, div_pow]; ring

/-- **Key lemma** (Park–Pham). The expected cost of the cover produced at one step of the
iteration is small. -/
theorem expected_cost_le {H : Finset (Finset α)} {l : ℕ} (hH : ∀ S ∈ H, S.card ≤ l)
    {q r : ℝ} (hq : 0 ≤ q) (hr0 : 0 < r) (hr1 : r ≤ 1) (b : ℕ) :
    ∑ W : Finset α, nu r W * cost q (Ucov H b W)
      ≤ 2 ^ l * ∑ m ∈ Finset.Ico (b + 1) (l + 1), (q / r) ^ m := by
  classical
  calc ∑ W : Finset α, nu r W * cost q (Ucov H b W)
      = ∑ W : Finset α, ∑ m ∈ Finset.Ico (b + 1) (l + 1),
          nu r W * ((((Ucov H b W).filter (fun U => U.card = m)).card : ℝ) * q ^ m) := by
        refine Finset.sum_congr rfl fun W _ => ?_
        rw [cost_Ucov_eq hH q b W, Finset.mul_sum]
    _ = ∑ m ∈ Finset.Ico (b + 1) (l + 1), ∑ W : Finset α,
          nu r W * ((((Ucov H b W).filter (fun U => U.card = m)).card : ℝ) * q ^ m) :=
        Finset.sum_comm
    _ ≤ ∑ m ∈ Finset.Ico (b + 1) (l + 1), 2 ^ l * (q / r) ^ m :=
        Finset.sum_le_sum fun m _ => per_size_bound hH hq hr0 hr1 b m
    _ = 2 ^ l * ∑ m ∈ Finset.Ico (b + 1) (l + 1), (q / r) ^ m := by rw [Finset.mul_sum]

end Math2

