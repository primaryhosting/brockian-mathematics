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
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Basic definitions for the Kahn–Kalai theorem (Park–Pham proof):
the Bernoulli product measure on subsets of a finite ground set, covers,
`p`-smallness, up-sets, and the parameters `q(F)`, `p_c(F)`, `ℓ(F)`.
-/

namespace Math2

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Bernoulli(`p`) product weight of a subset `A` inside the ground set `g`. -/
noncomputable def wg (g : Finset α) (p : ℝ) (A : Finset α) : ℝ :=
  p ^ A.card * (1 - p) ^ (g.card - A.card)

/-- Bernoulli(`p`) product weight of a subset `A` of the whole (finite) type. -/
noncomputable def w (p : ℝ) (A : Finset α) : ℝ :=
  p ^ A.card * (1 - p) ^ (Fintype.card α - A.card)

lemma w_eq_wg (p : ℝ) (A : Finset α) : w p A = wg Finset.univ p A := by
  simp [w, wg, Finset.card_univ]

/-- The measure `μ_p (F) = ∑_{A ∈ F} p^{|A|} (1-p)^{n - |A|}`. -/
noncomputable def mu (p : ℝ) (F : Finset (Finset α)) : ℝ := ∑ A ∈ F, w p A

/-- `G` is a cover of the family `H`: every member of `H` contains a member of `G`. -/
def IsCover (G H : Finset (Finset α)) : Prop := ∀ S ∈ H, ∃ T ∈ G, T ⊆ S

/-- The cost `∑_{T ∈ G} p^{|T|}` of the family `G`. -/
noncomputable def cost (p : ℝ) (G : Finset (Finset α)) : ℝ := ∑ T ∈ G, p ^ T.card

/-- `H` is `p`-small: it admits a cover of cost at most `1/2`. -/
def IsSmall (p : ℝ) (H : Finset (Finset α)) : Prop :=
  ∃ G : Finset (Finset α), IsCover G H ∧ cost p G ≤ 1 / 2

/-- The up-set (upward closure) `⟨H⟩` of a family `H`. -/
noncomputable def upSet (H : Finset (Finset α)) : Finset (Finset α) :=
  Finset.univ.filter (fun A => ∃ S ∈ H, S ⊆ A)

/-- A family is increasing if it is closed under taking supersets. -/
def IsIncreasing (F : Finset (Finset α)) : Prop := ∀ A ∈ F, ∀ B : Finset α, A ⊆ B → B ∈ F

/-- The minimal members of a family. -/
noncomputable def minimalMembers (F : Finset (Finset α)) : Finset (Finset α) :=
  F.filter (fun S => ∀ T ∈ F, T ⊆ S → T = S)

/-- `ℓ(F)`: the maximum of `2` and the largest size of a minimal member of `F`. -/
noncomputable def ell (F : Finset (Finset α)) : ℕ :=
  max 2 ((minimalMembers F).sup Finset.card)

/-- The expectation threshold `q(F)`: the supremum of the `p` for which `F` is `p`-small. -/
noncomputable def expThreshold (F : Finset (Finset α)) : ℝ :=
  sSup {p : ℝ | 0 ≤ p ∧ p ≤ 1 ∧ IsSmall p F}

/-- The threshold `p_c(F)`: the least `p` with `μ_p(F) ≥ 1/2`. -/
noncomputable def thresholdProb (F : Finset (Finset α)) : ℝ :=
  sInf {p : ℝ | 0 ≤ p ∧ p ≤ 1 ∧ 1 / 2 ≤ mu p F}

end Math2

/-
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Math2.Basic

/-!
The Bernoulli product measure on subsets of a finite type: total mass one,
expectations, and the key "union of two independent random subsets is again a
random subset" identity.
-/

namespace Math2

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma wg_insert_notMem {x : α} {g₀ A : Finset α} (hx : x ∉ g₀) (hA : A ⊆ g₀) (p : ℝ) :
    wg (insert x g₀) p A = (1 - p) * wg g₀ p A := by
  have h1 : (insert x g₀).card = g₀.card + 1 := Finset.card_insert_of_notMem hx
  have h2 : A.card ≤ g₀.card := Finset.card_le_card hA
  simp only [wg, h1]
  rw [show g₀.card + 1 - A.card = (g₀.card - A.card) + 1 by omega, pow_succ]
  ring

lemma wg_insert_mem {x : α} {g₀ A : Finset α} (hx : x ∉ g₀) (hA : A ⊆ g₀) (p : ℝ) :
    wg (insert x g₀) p (insert x A) = p * wg g₀ p A := by
  have hxA : x ∉ A := fun h => hx (hA h)
  have h1 : (insert x g₀).card = g₀.card + 1 := Finset.card_insert_of_notMem hx
  have h3 : (insert x A).card = A.card + 1 := Finset.card_insert_of_notMem hxA
  have h2 : A.card ≤ g₀.card := Finset.card_le_card hA
  simp only [wg, h1, h3]
  rw [show g₀.card + 1 - (A.card + 1) = g₀.card - A.card by omega, pow_succ]
  ring

/-- Union of two independent Bernoulli random subsets: the union of a `s`-random and an
independent `t`-random subset is `(s + t - s t)`-random. -/
lemma wg_union (s t : ℝ) (g : Finset α) : ∀ f : Finset α → ℝ,
    ∑ A ∈ g.powerset, ∑ B ∈ g.powerset, wg g s A * (wg g t B * f (A ∪ B))
      = ∑ C ∈ g.powerset, wg g (s + t - s * t) C * f C := by
  induction g using Finset.induction_on with
  | empty => intro f; simp [wg]
  | insert x g₀ hx ih =>
      intro f
      have hL : ∑ A ∈ (insert x g₀).powerset, ∑ B ∈ (insert x g₀).powerset,
            wg (insert x g₀) s A * (wg (insert x g₀) t B * f (A ∪ B))
          = (1 - s) * (1 - t) *
              (∑ A ∈ g₀.powerset, ∑ B ∈ g₀.powerset, wg g₀ s A * (wg g₀ t B * f (A ∪ B)))
            + (s + t - s * t) *
              (∑ A ∈ g₀.powerset, ∑ B ∈ g₀.powerset,
                wg g₀ s A * (wg g₀ t B * f (insert x (A ∪ B)))) := by
        simp only [Finset.sum_powerset_insert hx, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun A hA => ?_
        rw [Finset.mem_powerset] at hA
        refine Finset.sum_congr rfl fun B hB => ?_
        rw [Finset.mem_powerset] at hB
        simp only [wg_insert_notMem hx hA, wg_insert_mem hx hA, wg_insert_notMem hx hB,
          wg_insert_mem hx hB, Finset.union_insert, Finset.insert_union, Finset.insert_idem]
        ring
      rw [hL, ih f, ih (fun C => f (insert x C))]
      rw [Finset.sum_powerset_insert hx, Finset.mul_sum, Finset.mul_sum]
      refine congrArg₂ (· + ·) ?_ ?_ <;>
        refine Finset.sum_congr rfl fun C hC => ?_ <;> rw [Finset.mem_powerset] at hC
      · rw [wg_insert_notMem hx hC]; ring_nf
      · rw [wg_insert_mem hx hC]; ring

lemma sum_wg (g : Finset α) (p : ℝ) : ∑ A ∈ g.powerset, wg g p A = 1 := by
  have h := Finset.prod_add (fun _ : α => p) (fun _ : α => 1 - p) g
  simp only [Finset.prod_const] at h
  rw [show (p + (1 - p)) = 1 by ring, one_pow] at h
  rw [h]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [Finset.mem_powerset] at hA
  rw [wg, Finset.card_sdiff_of_subset hA]

lemma sum_w (p : ℝ) : ∑ A : Finset α, w p A = 1 := by
  have h := sum_wg (Finset.univ : Finset α) p
  rw [Finset.powerset_univ] at h
  simpa only [w_eq_wg] using h

lemma w_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset α) : 0 ≤ w p A := by
  apply mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

/-- The expectation of `f` under the Bernoulli(`p`) product measure. -/
noncomputable def Emeas (p : ℝ) (f : Finset α → ℝ) : ℝ := ∑ C : Finset α, w p C * f C

lemma Emeas_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f g : Finset α → ℝ}
    (h : ∀ A, f A ≤ g A) : Emeas p f ≤ Emeas p g := by
  refine Finset.sum_le_sum fun A _ => ?_
  exact mul_le_mul_of_nonneg_left (h A) (w_nonneg hp0 hp1 A)

lemma Emeas_const (p : ℝ) (c : ℝ) : Emeas (α := α) p (fun _ => c) = c := by
  rw [Emeas, ← Finset.sum_mul, sum_w, one_mul]

lemma Emeas_add (p : ℝ) (f g : Finset α → ℝ) :
    Emeas p (fun A => f A + g A) = Emeas p f + Emeas p g := by
  simp only [Emeas, mul_add, Finset.sum_add_distrib]

lemma Emeas_add_const (p : ℝ) (c : ℝ) (f : Finset α → ℝ) :
    Emeas p (fun A => c + f A) = c + Emeas p f := by
  rw [Emeas_add p (fun _ => c) f, Emeas_const]

lemma Emeas_zero (f : Finset α → ℝ) : Emeas (0 : ℝ) f = f ∅ := by
  rw [Emeas]
  rw [Finset.sum_eq_single (∅ : Finset α)]
  · simp [w]
  · intro b _ hb
    have : b.card ≠ 0 := fun h => hb (Finset.card_eq_zero.mp h)
    simp [w, zero_pow this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Splitting off one independent Bernoulli(`ρ`) round. -/
lemma Emeas_split (ρ t : ℝ) (f : Finset α → ℝ) :
    Emeas (ρ + t - ρ * t) f = ∑ W : Finset α, w ρ W * Emeas t (fun V => f (W ∪ V)) := by
  have h := wg_union (α := α) ρ t Finset.univ f
  rw [Finset.powerset_univ] at h
  simp only [← w_eq_wg] at h
  rw [Emeas, ← h]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Emeas, Finset.mul_sum]

end Math2

/-
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Math2.Measure

/-!
Minimum fragments (Park–Pham) and the key counting lemma: the cover produced from the
edges with a large minimum fragment has small expected cost.
-/

namespace Math2

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The candidate fragments of `S` with respect to `W`: the sets `S' \ W` for edges
`S' ∈ H` contained in `W ∪ S`. -/
noncomputable def cands (H : Finset (Finset α)) (S W : Finset α) : Finset (Finset α) :=
  (H.filter (fun S' => S' ⊆ W ∪ S)).image (fun S' => S' \ W)

lemma cands_nonempty {H : Finset (Finset α)} {S : Finset α} (W : Finset α) (hS : S ∈ H) :
    (cands H S W).Nonempty := by
  refine ⟨S \ W, ?_⟩
  simp only [cands, Finset.mem_image, Finset.mem_filter]
  exact ⟨S, ⟨hS, Finset.subset_union_right⟩, rfl⟩

lemma mem_cands {H : Finset (Finset α)} {S W T : Finset α} :
    T ∈ cands H S W ↔ ∃ S' ∈ H, S' ⊆ W ∪ S ∧ S' \ W = T := by
  simp only [cands, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨S', ⟨h1, h2⟩, h3⟩; exact ⟨S', h1, h2, h3⟩
  · rintro ⟨S', h1, h2, h3⟩; exact ⟨S', ⟨h1, h2⟩, h3⟩

/-- A minimum `(S, W)`-fragment: a smallest set of the form `S' \ W` with `S' ∈ H`,
`S' ⊆ W ∪ S`. -/
noncomputable def frag (H : Finset (Finset α)) (S W : Finset α) : Finset α :=
  if h : (cands H S W).Nonempty then
    Classical.choose (Finset.exists_min_image (cands H S W) Finset.card h)
  else ∅

lemma frag_mem_cands {H : Finset (Finset α)} {S : Finset α} (W : Finset α) (hS : S ∈ H) :
    frag H S W ∈ cands H S W := by
  have h := cands_nonempty W hS
  rw [frag, dif_pos h]
  exact (Classical.choose_spec (Finset.exists_min_image (cands H S W) Finset.card h)).1

lemma frag_min {H : Finset (Finset α)} {S : Finset α} (W : Finset α) (hS : S ∈ H)
    {T : Finset α} (hT : T ∈ cands H S W) : (frag H S W).card ≤ T.card := by
  have h := cands_nonempty W hS
  rw [frag, dif_pos h]
  exact (Classical.choose_spec (Finset.exists_min_image (cands H S W) Finset.card h)).2 T hT

lemma frag_spec {H : Finset (Finset α)} {S : Finset α} (W : Finset α) (hS : S ∈ H) :
    ∃ S' ∈ H, S' ⊆ W ∪ S ∧ S' \ W = frag H S W := mem_cands.mp (frag_mem_cands W hS)

lemma frag_subset {H : Finset (Finset α)} {S : Finset α} (W : Finset α) (hS : S ∈ H) :
    frag H S W ⊆ S := by
  obtain ⟨S', _, hsub, heq⟩ := frag_spec W hS
  rw [← heq]
  intro x hx
  rw [Finset.mem_sdiff] at hx
  rcases Finset.mem_union.mp (hsub hx.1) with h | h
  · exact absurd h hx.2
  · exact h

lemma frag_disjoint {H : Finset (Finset α)} {S : Finset α} (W : Finset α) (hS : S ∈ H) :
    Disjoint (frag H S W) W := by
  obtain ⟨S', _, _, heq⟩ := frag_spec W hS
  rw [← heq]
  exact Finset.sdiff_disjoint

/-- The edges of `H` whose minimum fragment (with respect to `W`) is large. -/
noncomputable def bigG (H : Finset (Finset α)) (k : ℕ) (W : Finset α) : Finset (Finset α) :=
  H.filter (fun S => k < 2 * (frag H S W).card)

/-- The cover of `bigG H k W` given by the minimum fragments. -/
noncomputable def coverU (H : Finset (Finset α)) (k : ℕ) (W : Finset α) : Finset (Finset α) :=
  (bigG H k W).image (fun S => frag H S W)

/-- The hypergraph carried to the next iteration step: the small minimum fragments. -/
noncomputable def nextH (H : Finset (Finset α)) (k : ℕ) (W : Finset α) : Finset (Finset α) :=
  (H.filter (fun S => ¬ k < 2 * (frag H S W).card)).image (fun S => frag H S W)

lemma nextH_bounded (H : Finset (Finset α)) (k : ℕ) (W : Finset α) :
    ∀ T ∈ nextH H k W, T.card ≤ k / 2 := by
  intro T hT
  simp only [nextH, Finset.mem_image, Finset.mem_filter] at hT
  obtain ⟨S, ⟨_, hS2⟩, rfl⟩ := hT
  omega

lemma nextH_capture {H : Finset (Finset α)} {k : ℕ} {W T : Finset α} (hT : T ∈ nextH H k W) :
    W ∪ T ∈ upSet H := by
  simp only [nextH, Finset.mem_image, Finset.mem_filter] at hT
  obtain ⟨S, ⟨hS1, _⟩, rfl⟩ := hT
  obtain ⟨S', hS'H, hS'sub, heq⟩ := frag_spec W hS1
  rw [upSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, S', hS'H, ?_⟩
  rw [← heq]
  intro x hx
  by_cases hxW : x ∈ W
  · exact Finset.mem_union_left _ hxW
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hxW⟩)

/-- Splitting `H`: edges with a large fragment are covered by `coverU`, the others are
covered by any cover of `nextH`. -/
lemma isCover_union {H : Finset (Finset α)} {k : ℕ} {W : Finset α} {G : Finset (Finset α)}
    (hG : IsCover G (nextH H k W)) : IsCover (coverU H k W ∪ G) H := by
  intro S hS
  by_cases hbig : k < 2 * (frag H S W).card
  · refine ⟨frag H S W, ?_, frag_subset W hS⟩
    refine Finset.mem_union_left _ ?_
    simp only [coverU, Finset.mem_image]
    exact ⟨S, by simp [bigG, Finset.mem_filter, hS, hbig], rfl⟩
  · have hmem : frag H S W ∈ nextH H k W := by
      simp only [nextH, Finset.mem_image, Finset.mem_filter]
      exact ⟨S, ⟨hS, hbig⟩, rfl⟩
    obtain ⟨T, hTG, hTsub⟩ := hG _ hmem
    exact ⟨T, Finset.mem_union_right _ hTG, hTsub.trans (frag_subset W hS)⟩

/-- A chosen edge of `H` inside `Z` (used to encode fragments). -/
noncomputable def shat (H : Finset (Finset α)) (Z : Finset α) : Finset α :=
  if h : ∃ S ∈ H, S ⊆ Z then Classical.choose h else ∅

lemma shat_subset (H : Finset (Finset α)) (Z : Finset α) : shat H Z ⊆ Z := by
  rw [shat]
  split
  · next h => exact (Classical.choose_spec h).2
  · exact Finset.empty_subset _

lemma shat_mem {H : Finset (Finset α)} {Z : Finset α} (h : ∃ S ∈ H, S ⊆ Z) : shat H Z ∈ H := by
  rw [shat, dif_pos h]
  exact (Classical.choose_spec h).1

lemma shat_card_le {H : Finset (Finset α)} {k : ℕ} (hk : ∀ S ∈ H, S.card ≤ k) (Z : Finset α) :
    (shat H Z).card ≤ k := by
  rw [shat]
  split
  · next h => exact hk _ (Classical.choose_spec h).1
  · simp

/-- The encoding step of Park–Pham: a minimum fragment `T` of `W` is a subset of the chosen
edge inside `W ∪ T`. -/
lemma coverU_encode {H : Finset (Finset α)} {k : ℕ} {W T : Finset α} (hk : ∀ S ∈ H, S.card ≤ k)
    (hT : T ∈ coverU H k W) :
    Disjoint T W ∧ T ⊆ shat H (W ∪ T) ∧ k < 2 * T.card ∧ T.card ≤ k := by
  simp only [coverU, Finset.mem_image, bigG, Finset.mem_filter] at hT
  obtain ⟨S, ⟨hSH, hSbig⟩, rfl⟩ := hT
  set T := frag H S W with hTdef
  have hdisj : Disjoint T W := frag_disjoint W hSH
  have hTS : T ⊆ S := frag_subset W hSH
  obtain ⟨S', hS'H, hS'sub, hS'eq⟩ := frag_spec W hSH
  have hS'Z : S' ⊆ W ∪ T := by
    intro x hx
    by_cases hxW : x ∈ W
    · exact Finset.mem_union_left _ hxW
    · refine Finset.mem_union_right _ ?_
      rw [hTdef, ← hS'eq]
      exact Finset.mem_sdiff.mpr ⟨hx, hxW⟩
  have hex : ∃ S₀ ∈ H, S₀ ⊆ W ∪ T := ⟨S', hS'H, hS'Z⟩
  have hShatH : shat H (W ∪ T) ∈ H := shat_mem hex
  have hShatZ : shat H (W ∪ T) ⊆ W ∪ T := shat_subset _ _
  have hcand : shat H (W ∪ T) \ W ∈ cands H S W := by
    refine mem_cands.mpr ⟨shat H (W ∪ T), hShatH, ?_, rfl⟩
    exact hShatZ.trans (Finset.union_subset_union_right hTS)
  have hcardle : T.card ≤ (shat H (W ∪ T) \ W).card := frag_min W hSH hcand
  have hsub : shat H (W ∪ T) \ W ⊆ T := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rcases Finset.mem_union.mp (hShatZ hx.1) with h | h
    · exact absurd h hx.2
    · exact h
  have heq : shat H (W ∪ T) \ W = T := Finset.eq_of_subset_of_card_le hsub hcardle
  refine ⟨hdisj, ?_, hSbig, le_trans (Finset.card_le_card hTS) (hk S hSH)⟩
  intro x hx
  have hx' : x ∈ shat H (W ∪ T) \ W := by rw [heq]; exact hx
  exact (Finset.mem_sdiff.mp hx').1

/-- Rewriting a sum over pairs `(W, T)` with `T ∈ coverU H k W` as an iterated sum. -/
lemma sum_pairs_eq (H : Finset (Finset α)) (k : ℕ) (f : Finset α → Finset α → ℝ) :
    ∑ z ∈ (Finset.univ.filter (fun z : Finset α × Finset α => z.2 ∈ coverU H k z.1)), f z.1 z.2
      = ∑ W : Finset α, ∑ T ∈ coverU H k W, f W T := by
  rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun W _ => ?_
  simp only [Finset.sum_ite_mem, Finset.univ_inter]

lemma w_sdiff_le {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {p : ℝ} (hp0 : 0 ≤ p)
    {Z T : Finset α} (hTZ : T ⊆ Z) :
    w ρ (Z \ T) * p ^ T.card ≤ w ρ Z * (p / ρ) ^ T.card := by
  have hc : Z.card ≤ Fintype.card α := by
    simpa using Finset.card_le_card (Finset.subset_univ Z)
  have ht : T.card ≤ Z.card := Finset.card_le_card hTZ
  have hcard : (Z \ T).card = Z.card - T.card := Finset.card_sdiff_of_subset hTZ
  have hrho : (0:ℝ) ≤ 1 - ρ := by linarith
  have hpow : (1 - ρ) ^ (Fintype.card α - (Z.card - T.card)) ≤ (1 - ρ) ^ (Fintype.card α - Z.card) := by
    apply pow_le_pow_of_le_one hrho (by linarith)
    omega
  have hsplit : ρ ^ Z.card = ρ ^ (Z.card - T.card) * ρ ^ T.card := by
    rw [← pow_add]
    congr 1
    omega
  have hdiv : (p / ρ) ^ T.card = p ^ T.card / ρ ^ T.card := div_pow p ρ T.card
  rw [w, w, hcard, hdiv, hsplit]
  have hrpos : (0:ℝ) < ρ ^ T.card := pow_pos hρ0 _
  rw [div_eq_mul_inv]
  have key : ρ ^ (Z.card - T.card) * ρ ^ T.card * (1 - ρ) ^ (Fintype.card α - Z.card) *
      (p ^ T.card * (ρ ^ T.card)⁻¹)
      = ρ ^ (Z.card - T.card) * (1 - ρ) ^ (Fintype.card α - Z.card) * p ^ T.card := by
    field_simp
  rw [key]
  have hnn : (0:ℝ) ≤ ρ ^ (Z.card - T.card) * p ^ T.card :=
    mul_nonneg (pow_nonneg hρ0.le _) (pow_nonneg hp0 _)
  calc ρ ^ (Z.card - T.card) * (1 - ρ) ^ (Fintype.card α - (Z.card - T.card)) * p ^ T.card
      = ρ ^ (Z.card - T.card) * p ^ T.card * (1 - ρ) ^ (Fintype.card α - (Z.card - T.card)) := by
        ring
    _ ≤ ρ ^ (Z.card - T.card) * p ^ T.card * (1 - ρ) ^ (Fintype.card α - Z.card) :=
        mul_le_mul_of_nonneg_left hpow hnn
    _ = ρ ^ (Z.card - T.card) * (1 - ρ) ^ (Fintype.card α - Z.card) * p ^ T.card := by ring

lemma expected_cost_le (H : Finset (Finset α)) (k : ℕ) (hk : ∀ S ∈ H, S.card ≤ k)
    {p ρ : ℝ} (hp0 : 0 ≤ p) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hpρ : p ≤ ρ) :
    Emeas ρ (fun W => cost p (coverU H k W)) ≤ 2 ^ k * (p / ρ) ^ (k / 2 + 1) := by
  classical
  have hratio0 : (0:ℝ) ≤ p / ρ := div_nonneg hp0 hρ0.le
  have hratio1 : p / ρ ≤ 1 := (div_le_one hρ0).mpr hpρ
  -- the pair sets
  set Lp : Finset (Finset α × Finset α) :=
    Finset.univ.filter (fun z : Finset α × Finset α => z.2 ∈ coverU H k z.1) with hLp
  set Rp : Finset (Finset α × Finset α) :=
    Finset.univ.filter (fun z : Finset α × Finset α =>
      z.2 ⊆ shat H z.1 ∧ k < 2 * z.2.card) with hRp
  have step1 : Emeas ρ (fun W => cost p (coverU H k W))
      = ∑ z ∈ Lp, w ρ z.1 * p ^ z.2.card := by
    rw [hLp, sum_pairs_eq H k (fun W T => w ρ W * p ^ T.card), Emeas]
    exact Finset.sum_congr rfl fun W _ => by rw [cost, Finset.mul_sum]
  -- the encoding map
  have hinj : Set.InjOn (fun z : Finset α × Finset α => (z.1 ∪ z.2, z.2)) ↑Lp := by
    rintro ⟨W₁, T₁⟩ h₁ ⟨W₂, T₂⟩ h₂ heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hLp, Finset.mem_coe, Finset.mem_filter] at h₁ h₂
    obtain ⟨hd₁, -, -, -⟩ := coverU_encode hk h₁.2
    obtain ⟨hd₂, -, -, -⟩ := coverU_encode hk h₂.2
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hu, ht⟩ := heq
    subst ht
    have e₁ : (W₁ ∪ T₁) \ T₁ = W₁ := by
      rw [Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint hd₁.symm]
    have e₂ : (W₂ ∪ T₁) \ T₁ = W₂ := by
      rw [Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint hd₂.symm]
    rw [Prod.mk.injEq]
    exact ⟨by rw [← e₁, ← e₂, hu], rfl⟩
  have step2 : ∑ z ∈ Lp, w ρ z.1 * p ^ z.2.card
      = ∑ y ∈ Lp.image (fun z => (z.1 ∪ z.2, z.2)), w ρ (y.1 \ y.2) * p ^ y.2.card := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun z hz => ?_
    simp only [hLp, Finset.mem_filter] at hz
    obtain ⟨hd, -, -, -⟩ := coverU_encode hk hz.2
    congr 1
    rw [Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint hd.symm]
  have hsub : Lp.image (fun z => (z.1 ∪ z.2, z.2)) ⊆ Rp := by
    intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simp only [hLp, Finset.mem_filter] at hz
    obtain ⟨-, hshat, hbig, -⟩ := coverU_encode hk hz.2
    simp only [hRp, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hshat, hbig⟩
  have step3 : ∑ y ∈ Lp.image (fun z => (z.1 ∪ z.2, z.2)), w ρ (y.1 \ y.2) * p ^ y.2.card
      ≤ ∑ y ∈ Rp, w ρ y.1 * (p / ρ) ^ y.2.card := by
    calc ∑ y ∈ Lp.image (fun z => (z.1 ∪ z.2, z.2)), w ρ (y.1 \ y.2) * p ^ y.2.card
        ≤ ∑ y ∈ Lp.image (fun z => (z.1 ∪ z.2, z.2)), w ρ y.1 * (p / ρ) ^ y.2.card := by
          refine Finset.sum_le_sum fun y hy => ?_
          have hyR := hsub hy
          simp only [hRp, Finset.mem_filter] at hyR
          exact w_sdiff_le hρ0 hρ1 hp0 (hyR.2.1.trans (shat_subset H y.1))
      _ ≤ ∑ y ∈ Rp, w ρ y.1 * (p / ρ) ^ y.2.card := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun y _ _ => ?_
          exact mul_nonneg (w_nonneg hρ0.le hρ1 _) (pow_nonneg hratio0 _)
  have step4 : ∑ y ∈ Rp, w ρ y.1 * (p / ρ) ^ y.2.card ≤ 2 ^ k * (p / ρ) ^ (k / 2 + 1) := by
    have inner : ∀ Z : Finset α,
        ∑ T : Finset α, (if T ⊆ shat H Z ∧ k < 2 * T.card then w ρ Z * (p / ρ) ^ T.card else 0)
          ≤ w ρ Z * (2 ^ k * (p / ρ) ^ (k / 2 + 1)) := by
      intro Z
      rw [← Finset.sum_filter]
      have hsubp : (Finset.univ.filter (fun T : Finset α => T ⊆ shat H Z ∧ k < 2 * T.card))
          ⊆ (shat H Z).powerset := by
        intro T hT
        simp only [Finset.mem_filter] at hT
        exact Finset.mem_powerset.mpr hT.2.1
      have hterm : ∀ T ∈ (Finset.univ.filter
          (fun T : Finset α => T ⊆ shat H Z ∧ k < 2 * T.card)),
          w ρ Z * (p / ρ) ^ T.card ≤ w ρ Z * (p / ρ) ^ (k / 2 + 1) := by
        intro T hT
        simp only [Finset.mem_filter] at hT
        refine mul_le_mul_of_nonneg_left ?_ (w_nonneg hρ0.le hρ1 _)
        apply pow_le_pow_of_le_one hratio0 hratio1
        omega
      calc ∑ T ∈ (Finset.univ.filter (fun T : Finset α => T ⊆ shat H Z ∧ k < 2 * T.card)),
              w ρ Z * (p / ρ) ^ T.card
          ≤ ∑ T ∈ (Finset.univ.filter (fun T : Finset α => T ⊆ shat H Z ∧ k < 2 * T.card)),
              w ρ Z * (p / ρ) ^ (k / 2 + 1) := Finset.sum_le_sum hterm
        _ ≤ ∑ _T ∈ (shat H Z).powerset, w ρ Z * (p / ρ) ^ (k / 2 + 1) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsubp fun _ _ _ => ?_
            exact mul_nonneg (w_nonneg hρ0.le hρ1 _) (pow_nonneg hratio0 _)
        _ = (2 ^ (shat H Z).card : ℝ) * (w ρ Z * (p / ρ) ^ (k / 2 + 1)) := by
            rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
            push_cast
            ring
        _ ≤ (2 ^ k : ℝ) * (w ρ Z * (p / ρ) ^ (k / 2 + 1)) := by
            refine mul_le_mul_of_nonneg_right ?_ ?_
            · exact pow_le_pow_right₀ (by norm_num) (shat_card_le hk Z)
            · exact mul_nonneg (w_nonneg hρ0.le hρ1 _) (pow_nonneg hratio0 _)
        _ = w ρ Z * (2 ^ k * (p / ρ) ^ (k / 2 + 1)) := by ring
    calc ∑ y ∈ Rp, w ρ y.1 * (p / ρ) ^ y.2.card
        = ∑ Z : Finset α, ∑ T : Finset α,
            (if T ⊆ shat H Z ∧ k < 2 * T.card then w ρ Z * (p / ρ) ^ T.card else 0) := by
          rw [hRp, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
      _ ≤ ∑ _Z : Finset α, w ρ _Z * (2 ^ k * (p / ρ) ^ (k / 2 + 1)) :=
          Finset.sum_le_sum fun Z _ => inner Z
      _ = 2 ^ k * (p / ρ) ^ (k / 2 + 1) := by
          rw [← Finset.sum_mul, sum_w, one_mul]
  rw [step1, step2]
  exact le_trans step3 step4

end Math2

