/-
Minimum fragments (Park-Pham) and the key lemma: the cover built from the large
minimum fragments has small expected cost.
-/
import RequestProject.Basic

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α]

/-! ### Minimum fragments -/

/-- The candidate fragments of `S` relative to `W`: the sets `S' \ W` for edges `S'` of `H`
contained in `W ∪ S`. -/
noncomputable def cands (H : Finset (Finset α)) (W S : Finset α) : Finset (Finset α) :=
  (H.filter (fun S' => S' ⊆ W ∪ S)).image (fun S' => S' \ W)

lemma cands_nonempty {H : Finset (Finset α)} {W S : Finset α} (hS : S ∈ H) :
    (cands H W S).Nonempty := by
  refine ⟨S \ W, ?_⟩
  simp only [cands, Finset.mem_image, Finset.mem_filter]
  exact ⟨S, ⟨hS, Finset.subset_union_right⟩, rfl⟩

/-- A minimum `(S,W)`-fragment: a smallest set of the form `S' \ W` with `S' ∈ H`
and `S' ⊆ W ∪ S`. -/
noncomputable def minFrag (H : Finset (Finset α)) (W S : Finset α) : Finset α :=
  if h : (cands H W S).Nonempty then
    Classical.choose (Finset.exists_min_image (cands H W S) Finset.card h)
  else ∅

lemma minFrag_spec {H : Finset (Finset α)} {W S : Finset α} (hS : S ∈ H) :
    minFrag H W S ∈ cands H W S ∧
      ∀ T ∈ cands H W S, (minFrag H W S).card ≤ T.card := by
  have h := cands_nonempty (H := H) (W := W) hS
  rw [minFrag, dif_pos h]
  have := Classical.choose_spec (Finset.exists_min_image (cands H W S) Finset.card h)
  obtain ⟨h1, h2⟩ := this
  exact ⟨h1, h2⟩

/-- The defining property of a minimum fragment: it is `S' \ W` for some edge `S'` inside
`W ∪ S`. -/
lemma minFrag_eq {H : Finset (Finset α)} {W S : Finset α} (hS : S ∈ H) :
    ∃ S' ∈ H, S' ⊆ W ∪ S ∧ minFrag H W S = S' \ W := by
  have h := (minFrag_spec (H := H) (W := W) hS).1
  simp only [cands, Finset.mem_image, Finset.mem_filter] at h
  obtain ⟨S', ⟨hS'H, hS'sub⟩, hEq⟩ := h
  exact ⟨S', hS'H, hS'sub, hEq.symm⟩

lemma minFrag_min {H : Finset (Finset α)} {W S : Finset α} (hS : S ∈ H) {S' : Finset α}
    (hS'H : S' ∈ H) (hS'sub : S' ⊆ W ∪ S) : (minFrag H W S).card ≤ (S' \ W).card := by
  refine (minFrag_spec hS).2 _ ?_
  simp only [cands, Finset.mem_image, Finset.mem_filter]
  exact ⟨S', ⟨hS'H, hS'sub⟩, rfl⟩

lemma minFrag_subset {H : Finset (Finset α)} {W S : Finset α} (hS : S ∈ H) :
    minFrag H W S ⊆ S := by
  obtain ⟨S', _, hsub, hEq⟩ := minFrag_eq hS
  rw [hEq]
  intro x hx
  rw [Finset.mem_sdiff] at hx
  rcases Finset.mem_union.1 (hsub hx.1) with h | h
  · exact absurd h hx.2
  · exact h

lemma minFrag_disjoint {H : Finset (Finset α)} {W S : Finset α} (hS : S ∈ H) :
    Disjoint W (minFrag H W S) := by
  obtain ⟨S', _, _, hEq⟩ := minFrag_eq hS
  rw [hEq]
  exact Finset.disjoint_sdiff

/-- If `V` contains a minimum fragment of `S`, then `W ∪ V` contains an edge of `H`. -/
lemma minFrag_capture [Fintype α] {H : Finset (Finset α)} {W S : Finset α} (hS : S ∈ H) {V : Finset α}
    (hV : minFrag H W S ⊆ V) : W ∪ V ∈ upset H := by
  obtain ⟨S', hS'H, _, hEq⟩ := minFrag_eq hS
  refine mem_upset.2 ⟨S', hS'H, ?_⟩
  intro x hx
  rw [Finset.mem_union]
  by_cases hxW : x ∈ W
  · exact Or.inl hxW
  · exact Or.inr (hV (by rw [hEq, Finset.mem_sdiff]; exact ⟨hx, hxW⟩))

/-! ### One round of the process -/

/-- The edges of `H` whose minimum fragment is large. -/
noncomputable def bigG (H : Finset (Finset α)) (W : Finset α) (m : ℕ) : Finset (Finset α) :=
  H.filter (fun S => m ≤ 2 * (minFrag H W S).card)

/-- The cover of `bigG H W m` given by the (large) minimum fragments. -/
noncomputable def Ufam (H : Finset (Finset α)) (W : Finset α) (m : ℕ) : Finset (Finset α) :=
  (bigG H W m).image (minFrag H W)

/-- The hypergraph carried to the next round: the small minimum fragments. -/
noncomputable def Hnext (H : Finset (Finset α)) (W : Finset α) (m : ℕ) : Finset (Finset α) :=
  (H.filter (fun S => ¬ (m ≤ 2 * (minFrag H W S).card))).image (minFrag H W)

lemma Ufam_cover_bigG (H : Finset (Finset α)) (W : Finset α) (m : ℕ) :
    IsCover (bigG H W m) (Ufam H W m) := by
  intro S hS
  refine ⟨minFrag H W S, ?_, ?_⟩
  · exact Finset.mem_image_of_mem _ hS
  · exact minFrag_subset (Finset.mem_filter.1 hS).1

lemma Hnext_card_le {H : Finset (Finset α)} {W : Finset α} {m : ℕ} {T : Finset α}
    (hT : T ∈ Hnext H W m) : 2 * T.card < m := by
  simp only [Hnext, Finset.mem_image, Finset.mem_filter] at hT
  obtain ⟨S, ⟨_, hS2⟩, hEq⟩ := hT
  rw [← hEq]
  omega

lemma Hnext_capture [Fintype α] {H : Finset (Finset α)} {W : Finset α} {m : ℕ} {V : Finset α}
    (hV : V ∈ upset (Hnext H W m)) : W ∪ V ∈ upset H := by
  rw [mem_upset] at hV
  obtain ⟨T, hT, hTV⟩ := hV
  simp only [Hnext, Finset.mem_image, Finset.mem_filter] at hT
  obtain ⟨S, ⟨hSH, _⟩, hEq⟩ := hT
  exact minFrag_capture hSH (by rw [hEq]; exact hTV)

/-- Combining a cover of the next-round hypergraph with the fragment cover gives a cover
of `H`. -/
lemma cover_combine {H : Finset (Finset α)} {W : Finset α} {m : ℕ} {V : Finset (Finset α)}
    (hV : IsCover (Hnext H W m) V) : IsCover H (V ∪ Ufam H W m) := by
  intro S hS
  by_cases hbig : m ≤ 2 * (minFrag H W S).card
  · refine ⟨minFrag H W S, ?_, minFrag_subset hS⟩
    refine Finset.mem_union_right _ ?_
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hS, hbig⟩)
  · have hmem : minFrag H W S ∈ Hnext H W m :=
      Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hS, hbig⟩)
    obtain ⟨v, hv, hvsub⟩ := hV _ hmem
    exact ⟨v, Finset.mem_union_left _ hv, hvsub.trans (minFrag_subset hS)⟩

/-! ### The canonical edge inside a set -/

/-- A canonical edge of `H` inside `Z`, if there is one. -/
noncomputable def pick (H : Finset (Finset α)) (Z : Finset α) : Finset α :=
  if h : (H.filter (fun S => S ⊆ Z)).Nonempty then h.choose else ∅

lemma pick_mem {H : Finset (Finset α)} {Z : Finset α}
    (h : (H.filter (fun S => S ⊆ Z)).Nonempty) : pick H Z ∈ H ∧ pick H Z ⊆ Z := by
  rw [pick, dif_pos h]
  have := h.choose_spec
  rw [Finset.mem_filter] at this
  exact this

lemma pick_card_le {H : Finset (Finset α)} {m : ℕ} (hH : ∀ S ∈ H, S.card ≤ m) (Z : Finset α) :
    (pick H Z).card ≤ m := by
  by_cases h : (H.filter (fun S => S ⊆ Z)).Nonempty
  · exact hH _ (pick_mem h).1
  · rw [pick, dif_neg h]
    simp

/-- The crucial observation: a large minimum fragment is contained in the canonical edge
of `W ∪ T`. -/
lemma minFrag_subset_pick {H : Finset (Finset α)} {W S : Finset α} (hS : S ∈ H) :
    minFrag H W S ⊆ pick H (W ∪ minFrag H W S) := by
  set T := minFrag H W S with hT
  set Z := W ∪ T with hZ
  obtain ⟨S', hS'H, hS'sub, hEq⟩ := minFrag_eq (W := W) hS
  have hS'Z : S' ⊆ Z := by
    intro x hx
    rw [hZ, Finset.mem_union]
    by_cases hxW : x ∈ W
    · exact Or.inl hxW
    · exact Or.inr (by rw [hT, hEq, Finset.mem_sdiff]; exact ⟨hx, hxW⟩)
  have hne : (H.filter (fun S => S ⊆ Z)).Nonempty := ⟨S', Finset.mem_filter.2 ⟨hS'H, hS'Z⟩⟩
  obtain ⟨hPH, hPZ⟩ := pick_mem hne
  -- `pick H Z` is a candidate fragment for `S`
  have hTS : T ⊆ S := minFrag_subset hS
  have hPWS : pick H Z ⊆ W ∪ S := by
    intro x hx
    rcases Finset.mem_union.1 (hPZ hx) with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (hTS h)
  have hmin : T.card ≤ (pick H Z \ W).card := minFrag_min hS hPH hPWS
  have hsub : pick H Z \ W ⊆ T := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rcases Finset.mem_union.1 (hPZ hx.1) with h | h
    · exact absurd h hx.2
    · exact h
  have : pick H Z \ W = T := Finset.eq_of_subset_of_card_le hsub hmin
  rw [← this]
  exact Finset.sdiff_subset

end KahnKalai

/-
Basic set-up for the Kahn-Kalai theorem: the product measure `mu p` on the
powerset of a finite type, up-sets, covers and their costs.
-/
import RequestProject.Weights

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `wt p A` is the probability that the `p`-random subset of the ground type equals `A`. -/
noncomputable def wt (p : ℝ) (A : Finset α) : ℝ := wtOn Finset.univ p A

omit [DecidableEq α] in
lemma wt_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset α) : 0 ≤ wt p A :=
  wtOn_nonneg hp0 hp1 A

lemma sum_wt (p : ℝ) : ∑ A : Finset α, wt p A = 1 := by
  have h : (Finset.univ : Finset (Finset α)) = (Finset.univ : Finset α).powerset := by
    rw [Finset.powerset_univ]
  rw [h]
  exact sum_wtOn _ p

/-- The union of independent `a`- and `b`-random subsets is an `(a+b-a*b)`-random subset. -/
lemma union_wt (a b : ℝ) (f : Finset α → ℝ) :
    ∑ A : Finset α, ∑ B : Finset α, wt a A * wt b B * f (A ∪ B)
      = ∑ C : Finset α, wt (a + b - a * b) C * f C := by
  have h : (Finset.univ : Finset (Finset α)) = (Finset.univ : Finset α).powerset := by
    rw [Finset.powerset_univ]
  rw [h]
  exact union_wtOn a b _ f

/-- The measure of a family of sets. -/
noncomputable def mu (p : ℝ) (F : Finset (Finset α)) : ℝ := ∑ A ∈ F, wt p A

omit [DecidableEq α] in
lemma mu_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F : Finset (Finset α)) : 0 ≤ mu p F :=
  Finset.sum_nonneg fun A _ => wt_nonneg hp0 hp1 A

lemma mu_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F : Finset (Finset α)) : mu p F ≤ 1 := by
  rw [← sum_wt (α := α) p]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
    (fun A _ _ => wt_nonneg hp0 hp1 A)

lemma mu_eq_sum_ite (p : ℝ) (F : Finset (Finset α)) :
    mu p F = ∑ A : Finset α, if A ∈ F then wt p A else 0 := by
  rw [mu, ← Finset.sum_filter]
  exact Finset.sum_congr (by ext A; simp) (fun _ _ => rfl)

omit [DecidableEq α] in
lemma mu_mono_subset {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {F G : Finset (Finset α)}
    (h : F ⊆ G) : mu p F ≤ mu p G :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun A _ _ => wt_nonneg hp0 hp1 A)

lemma mu_univ (p : ℝ) : mu p (Finset.univ : Finset (Finset α)) = 1 := sum_wt p

/-- The up-set generated by a hypergraph. -/
noncomputable def upset (H : Finset (Finset α)) : Finset (Finset α) :=
  Finset.univ.filter (fun A => ∃ S ∈ H, S ⊆ A)

lemma mem_upset {H : Finset (Finset α)} {A : Finset α} :
    A ∈ upset H ↔ ∃ S ∈ H, S ⊆ A := by
  simp [upset]

lemma upset_upward_closed {H : Finset (Finset α)} {A B : Finset α} (hA : A ∈ upset H)
    (hAB : A ⊆ B) : B ∈ upset H := by
  rw [mem_upset] at hA ⊢
  obtain ⟨S, hS, hSA⟩ := hA
  exact ⟨S, hS, hSA.trans hAB⟩

/-- A family `F` is upward closed. -/
def IsUp (F : Finset (Finset α)) : Prop := ∀ A ∈ F, ∀ B : Finset α, A ⊆ B → B ∈ F

lemma isUp_upset (H : Finset (Finset α)) : IsUp (upset H) :=
  fun _ hA _ hAB => upset_upward_closed hA hAB

/-- Monotonicity of `mu` in the density, for upward closed families. -/
lemma mu_le_mu_union {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    {F : Finset (Finset α)} (hF : IsUp F) : mu a F ≤ mu (a + b - a * b) F := by
  classical
  have key := union_wt (α := α) a b (fun C => if C ∈ F then (1:ℝ) else 0)
  have hle : ∑ A : Finset α, ∑ B : Finset α,
      wt a A * wt b B * (if A ∈ F then (1:ℝ) else 0)
      ≤ ∑ A : Finset α, ∑ B : Finset α,
      wt a A * wt b B * (if A ∪ B ∈ F then (1:ℝ) else 0) := by
    refine Finset.sum_le_sum ?_
    intro A _
    refine Finset.sum_le_sum ?_
    intro B _
    have hw : 0 ≤ wt a A * wt b B :=
      mul_nonneg (wt_nonneg ha0 ha1 A) (wt_nonneg hb0 hb1 B)
    have : (if A ∈ F then (1:ℝ) else 0) ≤ (if A ∪ B ∈ F then (1:ℝ) else 0) := by
      by_cases hA : A ∈ F
      · have : A ∪ B ∈ F := hF A hA _ Finset.subset_union_left
        simp [hA, this]
      · simp [hA]
        positivity
    exact mul_le_mul_of_nonneg_left this hw
  have hsplit : ∑ A : Finset α, ∑ B : Finset α,
      wt a A * wt b B * (if A ∈ F then (1:ℝ) else 0) = mu a F := by
    rw [mu_eq_sum_ite]
    refine Finset.sum_congr rfl ?_
    intro A _
    have : ∀ B : Finset α, wt a A * wt b B * (if A ∈ F then (1:ℝ) else 0)
        = wt b B * (wt a A * (if A ∈ F then (1:ℝ) else 0)) := by
      intro B; ring
    simp only [this, ← Finset.sum_mul, sum_wt, one_mul]
    by_cases h : A ∈ F <;> simp [h]
  rw [hsplit] at hle
  rw [key] at hle
  calc mu a F ≤ ∑ C : Finset α, wt (a + b - a * b) C * (if C ∈ F then (1:ℝ) else 0) := hle
    _ = mu (a + b - a * b) F := by
        rw [mu_eq_sum_ite]
        exact Finset.sum_congr rfl (fun C _ => by by_cases h : C ∈ F <;> simp [h])

/-- Monotonicity of `mu` in the density. -/
lemma mu_mono {a c : ℝ} (ha0 : 0 ≤ a) (hac : a ≤ c) (hc1 : c ≤ 1)
    {F : Finset (Finset α)} (hF : IsUp F) : mu a F ≤ mu c F := by
  rcases eq_or_lt_of_le (le_trans ha0 hac) with h1 | h1
  · -- c = 0, hence a = 0
    have : a = c := by linarith [ha0, hac, h1.symm ▸ hc1]
    rw [this]
  rcases eq_or_lt_of_le hac with h | h
  · rw [h]
  by_cases ha1 : a = 1
  · exfalso; rw [ha1] at h; linarith
  have ha1' : a < 1 := lt_of_le_of_ne (le_trans hac hc1) ha1
  set b : ℝ := (c - a) / (1 - a) with hb
  have h1a : 0 < 1 - a := by linarith
  have hb0 : 0 ≤ b := div_nonneg (by linarith) (le_of_lt h1a)
  have hb1 : b ≤ 1 := by
    rw [hb, div_le_one h1a]; linarith
  have hcalc : a + b - a * b = c := by
    rw [hb]
    field_simp
    ring
  have := mu_le_mu_union (α := α) ha0 (le_of_lt ha1') hb0 hb1 hF
  rwa [hcalc] at this

/-- `U` is a cover of the hypergraph `H`. -/
def IsCover (H U : Finset (Finset α)) : Prop := ∀ S ∈ H, ∃ u ∈ U, u ⊆ S

/-- The cost `∑_{u ∈ U} p ^ |u|` of a cover. -/
noncomputable def cost (p : ℝ) (U : Finset (Finset α)) : ℝ := ∑ u ∈ U, p ^ u.card

omit [Fintype α] [DecidableEq α] in
lemma cost_nonneg {p : ℝ} (hp : 0 ≤ p) (U : Finset (Finset α)) : 0 ≤ cost p U :=
  Finset.sum_nonneg fun _ _ => pow_nonneg hp _

omit [Fintype α] in
lemma cost_union_le {p : ℝ} (hp : 0 ≤ p) (U V : Finset (Finset α)) :
    cost p (U ∪ V) ≤ cost p U + cost p V := by
  classical
  have h : U ∪ V = U ∪ (V \ U) := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  simp only [cost]
  rw [h, Finset.sum_union (Finset.disjoint_sdiff)]
  have h2 : ∑ u ∈ V \ U, p ^ u.card ≤ ∑ u ∈ V, p ^ u.card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset) (fun u _ _ => pow_nonneg hp _)
  linarith

/-- `H` is `p`-small: it has a cover of cost at most `1/2`. -/
def IsSmall (p : ℝ) (H : Finset (Finset α)) : Prop :=
  ∃ U : Finset (Finset α), IsCover H U ∧ cost p U ≤ 1 / 2

end KahnKalai

/-
The iteration: repeatedly extracting minimum fragments halves the size bound of the
hypergraph, and the accumulated cover cost stays bounded.
-/
import RequestProject.KeyLemma

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The density of a union of `k` independent `r`-random sets. -/
noncomputable def dens (r : ℝ) (k : ℕ) : ℝ := 1 - (1 - r) ^ k

lemma dens_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (k : ℕ) : 0 ≤ dens r k := by
  have : (1 - r) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  simp only [dens]; linarith

lemma dens_le_one {r : ℝ} (hr1 : r ≤ 1) (k : ℕ) : dens r k ≤ 1 := by
  have : 0 ≤ (1 - r) ^ k := pow_nonneg (by linarith) _
  simp only [dens]; linarith

lemma dens_succ (r : ℝ) (k : ℕ) : dens r (k + 1) = r + dens r k - r * dens r k := by
  simp only [dens]
  ring

lemma dens_le_mul (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (k : ℕ) : dens r k ≤ k * r := by
  induction k with
  | zero => simp [dens]
  | succ k ih =>
      rw [dens_succ]
      have h1 : 0 ≤ dens r k := dens_nonneg hr0 hr1 k
      have : r * dens r k ≥ 0 := mul_nonneg hr0 h1
      push_cast
      nlinarith

/-- The bound on the total expected cover cost, as a function of the size bound. -/
noncomputable def ebound (m : ℕ) : ℝ := (1 - (1 / 9 : ℝ) ^ m) / 8

lemma ebound_zero : ebound 0 = 0 := by simp [ebound]

lemma ebound_nonneg (m : ℕ) : 0 ≤ ebound m := by
  have : (1 / 9 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  simp only [ebound]; linarith

lemma ebound_le (m : ℕ) : ebound m ≤ 1 / 8 := by
  have : (0:ℝ) ≤ (1 / 9 : ℝ) ^ m := by positivity
  simp only [ebound]; linarith

lemma ebound_mono {m m' : ℕ} (h : m' ≤ m) : ebound m' ≤ ebound m := by
  have : (1 / 9 : ℝ) ^ m ≤ (1 / 9 : ℝ) ^ m' :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  simp only [ebound]; linarith

lemma ebound_step {m : ℕ} (hm : 1 ≤ m) : (1 / 9 : ℝ) ^ m + ebound (m - 1) = ebound m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  simp only [ebound, Nat.add_sub_cancel, pow_succ]
  ring

/-- The measure as a sum of indicators. -/
lemma mu_eq_sum_indicator (p : ℝ) (F : Finset (Finset α)) :
    mu p F = ∑ C : Finset α, wt p C * (if C ∈ F then (1:ℝ) else 0) := by
  rw [mu_eq_sum_ite]
  exact Finset.sum_congr rfl (fun C _ => by by_cases h : C ∈ F <;> simp [h])

/-- The main induction. If `H` is `m`-bounded with `m < 2^k`, and every cover of `H` costs
at least `θ`, then a `dens r k`-random set lies in `⟨H⟩` with probability at least
`1 - ebound m / θ`. -/
theorem main_induction {p r : ℝ} (hp : 0 < p) (hr : r = 324 * p) (hr1 : r ≤ 1) :
    ∀ (k m : ℕ), m < 2 ^ k → ∀ H : Finset (Finset α), (∀ S ∈ H, S.card ≤ m) →
      ∀ θ : ℝ, 0 ≤ θ → (∀ U : Finset (Finset α), IsCover H U → θ ≤ cost p U) →
        θ * (1 - mu (dens r k) (upset H)) ≤ ebound m := by
  have hr0 : 0 < r := by rw [hr]; linarith
  intro k
  induction k with
  | zero =>
      intro m hm H hH θ hθ0 hcov
      interval_cases m
      · -- `m = 0`: every edge is empty
        by_cases hHe : H = ∅
        · have : θ ≤ cost p (∅ : Finset (Finset α)) := by
            refine hcov ∅ ?_
            intro S hS
            rw [hHe] at hS
            exact absurd hS (Finset.notMem_empty S)
          rw [cost] at this
          simp only [Finset.sum_empty] at this
          have hθ : θ = 0 := le_antisymm this hθ0
          rw [hθ, ebound_zero]
          simp
        · obtain ⟨S, hS⟩ := Finset.nonempty_iff_ne_empty.2 hHe
          have hS0 : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 (hH S hS))
          have : upset H = (Finset.univ : Finset (Finset α)) := by
            ext A
            simp only [Finset.mem_univ, iff_true]
            exact mem_upset.2 ⟨S, hS, by rw [hS0]; exact Finset.empty_subset A⟩
          rw [this, mu_univ, ebound_zero]
          simp
  | succ k ih =>
      intro m hm H hH θ hθ0 hcov
      rcases Nat.eq_zero_or_pos m with hm0 | hm1
      · -- `m = 0` again
        subst hm0
        by_cases hHe : H = ∅
        · have : θ ≤ cost p (∅ : Finset (Finset α)) := by
            refine hcov ∅ ?_
            intro S hS
            rw [hHe] at hS
            exact absurd hS (Finset.notMem_empty S)
          rw [cost] at this
          simp only [Finset.sum_empty] at this
          have hθ : θ = 0 := le_antisymm this hθ0
          rw [hθ, ebound_zero]
          simp
        · obtain ⟨S, hS⟩ := Finset.nonempty_iff_ne_empty.2 hHe
          have hS0 : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 (hH S hS))
          have : upset H = (Finset.univ : Finset (Finset α)) := by
            ext A
            simp only [Finset.mem_univ, iff_true]
            exact mem_upset.2 ⟨S, hS, by rw [hS0]; exact Finset.empty_subset A⟩
          rw [this, mu_univ, ebound_zero]
          simp
      -- the main case
      set m' : ℕ := (m - 1) / 2 with hm'
      have hm'lt : m' < 2 ^ k := by
        have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        omega
      set b : ℝ := dens r k with hb
      have hb0 : 0 ≤ b := dens_nonneg (le_of_lt hr0) hr1 k
      have hb1 : b ≤ 1 := dens_le_one hr1 k
      -- one round, for each `W`
      have hstepW : ∀ W : Finset α,
          θ * (1 - mu b (upset (Hnext H W m))) ≤ ebound m' + cost p (Ufam H W m) := by
        intro W
        set κ : ℝ := cost p (Ufam H W m) with hκ
        have hκ0 : 0 ≤ κ := cost_nonneg (le_of_lt hp) _
        set θ' : ℝ := max 0 (θ - κ) with hθ'
        have hθ'0 : 0 ≤ θ' := le_max_left _ _
        have hθ'le : θ ≤ θ' + κ := by
          rcases le_total θ κ with h | h
          · have : 0 ≤ θ' := hθ'0
            linarith
          · have : θ - κ ≤ θ' := le_max_right _ _
            linarith
        have hcov' : ∀ V : Finset (Finset α), IsCover (Hnext H W m) V → θ' ≤ cost p V := by
          intro V hV
          have h1 : θ ≤ cost p (V ∪ Ufam H W m) := hcov _ (cover_combine hV)
          have h2 : cost p (V ∪ Ufam H W m) ≤ cost p V + κ :=
            cost_union_le (le_of_lt hp) V (Ufam H W m)
          have h3 : θ - κ ≤ cost p V := by linarith
          exact max_le (cost_nonneg (le_of_lt hp) _) h3
        have hbound : ∀ T ∈ Hnext H W m, T.card ≤ m' := by
          intro T hT
          have := Hnext_card_le hT
          omega
        have hIH := ih m' hm'lt (Hnext H W m) hbound θ' hθ'0 hcov'
        have hmu0 : 0 ≤ mu b (upset (Hnext H W m)) := mu_nonneg hb0 hb1 _
        have hmu1 : mu b (upset (Hnext H W m)) ≤ 1 := mu_le_one hb0 hb1 _
        nlinarith [hIH, hθ'le, hκ0, hθ0]
      -- average over `W`
      have hsum1 : ∑ W : Finset α, wt r W * (θ * (1 - mu b (upset (Hnext H W m))))
          ≤ ∑ W : Finset α, wt r W * (ebound m' + cost p (Ufam H W m)) := by
        refine Finset.sum_le_sum ?_
        intro W _
        exact mul_le_mul_of_nonneg_left (hstepW W) (wt_nonneg (le_of_lt hr0) hr1 W)
      have hsum2 : ∑ W : Finset α, wt r W * (ebound m' + cost p (Ufam H W m))
          = ebound m' + ∑ W : Finset α, wt r W * cost p (Ufam H W m) := by
        have : ∀ W : Finset α, wt r W * (ebound m' + cost p (Ufam H W m))
            = wt r W * ebound m' + wt r W * cost p (Ufam H W m) := by
          intro W; ring
        simp only [this]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_wt, one_mul]
      have hkey : ∑ W : Finset α, wt r W * cost p (Ufam H W m) ≤ (1 / 9 : ℝ) ^ m := by
        have := expected_cost_le (H := H) (m := m) hH (p := p) (r := r) (c := 18)
          hp (by norm_num) (by rw [hr]; norm_num) hr1
        calc ∑ W : Finset α, wt r W * cost p (Ufam H W m) ≤ (2 / 18 : ℝ) ^ m := this
          _ = (1 / 9 : ℝ) ^ m := by norm_num
      have hsum3 : ∑ W : Finset α, wt r W * (θ * (1 - mu b (upset (Hnext H W m))))
          = θ * (1 - ∑ W : Finset α, wt r W * mu b (upset (Hnext H W m))) := by
        have : ∀ W : Finset α, wt r W * (θ * (1 - mu b (upset (Hnext H W m))))
            = θ * wt r W - θ * (wt r W * mu b (upset (Hnext H W m))) := by
          intro W; ring
        simp only [this]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_wt]
        ring
      -- the union of the fresh set `W` with a `b`-random set
      have hcapture : ∑ W : Finset α, wt r W * mu b (upset (Hnext H W m))
          ≤ mu (dens r (k + 1)) (upset H) := by
        have hexp : ∀ W : Finset α, wt r W * mu b (upset (Hnext H W m))
            = ∑ V : Finset α, wt r W * wt b V * (if V ∈ upset (Hnext H W m) then (1:ℝ) else 0) := by
          intro W
          rw [mu_eq_sum_indicator, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun V _ => by ring)
        have hle : ∀ W : Finset α,
            (∑ V : Finset α, wt r W * wt b V * (if V ∈ upset (Hnext H W m) then (1:ℝ) else 0))
              ≤ ∑ V : Finset α, wt r W * wt b V * (if W ∪ V ∈ upset H then (1:ℝ) else 0) := by
          intro W
          refine Finset.sum_le_sum ?_
          intro V _
          have hw : 0 ≤ wt r W * wt b V :=
            mul_nonneg (wt_nonneg (le_of_lt hr0) hr1 W) (wt_nonneg hb0 hb1 V)
          have : (if V ∈ upset (Hnext H W m) then (1:ℝ) else 0)
              ≤ (if W ∪ V ∈ upset H then (1:ℝ) else 0) := by
            by_cases h : V ∈ upset (Hnext H W m)
            · have : W ∪ V ∈ upset H := Hnext_capture h
              simp [h, this]
            · simp [h]
              positivity
          exact mul_le_mul_of_nonneg_left this hw
        calc ∑ W : Finset α, wt r W * mu b (upset (Hnext H W m))
            = ∑ W : Finset α, ∑ V : Finset α,
                wt r W * wt b V * (if V ∈ upset (Hnext H W m) then (1:ℝ) else 0) := by
              exact Finset.sum_congr rfl (fun W _ => hexp W)
          _ ≤ ∑ W : Finset α, ∑ V : Finset α,
                wt r W * wt b V * (if W ∪ V ∈ upset H then (1:ℝ) else 0) :=
              Finset.sum_le_sum (fun W _ => hle W)
          _ = ∑ C : Finset α, wt (r + b - r * b) C * (if C ∈ upset H then (1:ℝ) else 0) :=
              union_wt r b (fun C => if C ∈ upset H then (1:ℝ) else 0)
          _ = mu (dens r (k + 1)) (upset H) := by
              rw [dens_succ, hb, mu_eq_sum_indicator]
      -- put everything together
      have hfinal : θ * (1 - mu (dens r (k + 1)) (upset H))
          ≤ θ * (1 - ∑ W : Finset α, wt r W * mu b (upset (Hnext H W m))) := by
        have := hcapture
        nlinarith [hθ0]
      have hlast : ebound m' + (1 / 9 : ℝ) ^ m ≤ ebound m := by
        have h1 : ebound m' ≤ ebound (m - 1) := ebound_mono (by omega)
        have h2 := ebound_step (m := m) hm1
        linarith
      linarith [hfinal, hsum3, hsum1, hsum2, hkey, hlast]

end KahnKalai

import RequestProject.Iteration

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### The universal constant -/

/-- The universal constant in the Kahn-Kalai theorem produced by this proof. -/
noncomputable def Kconst : ℝ := 648 / Real.log 2

lemma log_two_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)

lemma Kconst_pos : 0 < Kconst := by
  rw [Kconst]; positivity

lemma Kconst_log_two : Kconst * Real.log 2 = 648 := by
  rw [Kconst]
  field_simp

/-! ### The main theorem for hypergraphs -/

/-- **Kahn-Kalai, hypergraph form.** If the `m`-bounded hypergraph `H` (with `m ≥ 2`) is not
`p`-small, then a `ρ`-random set lies in the up-set of `H` with probability more than `1/2`,
as soon as `ρ ≥ Kconst * p * log m`. -/
theorem mu_gt_half_of_not_isSmall {H : Finset (Finset α)} {m : ℕ} (hm2 : 2 ≤ m)
    (hH : ∀ S ∈ H, S.card ≤ m) {p ρ : ℝ} (hp : 0 < p) (hns : ¬ IsSmall p H)
    (hρ1 : ρ ≤ 1) (hρ : Kconst * p * Real.log m ≤ ρ) : 1 / 2 < mu ρ (upset H) := by
  have hlog2 : (0:ℝ) < Real.log 2 := log_two_pos
  have hlogm : Real.log 2 ≤ Real.log m :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
  have hlogm0 : 0 < Real.log m := lt_of_lt_of_le hlog2 hlogm
  -- first, `p` is small
  have h648 : 648 * p ≤ ρ := by
    have h1 : Kconst * p * Real.log 2 ≤ Kconst * p * Real.log m := by
      have : 0 ≤ Kconst * p := le_of_lt (mul_pos Kconst_pos hp)
      nlinarith
    have h2 : Kconst * p * Real.log 2 = 648 * p := by
      rw [mul_comm Kconst p, mul_assoc, Kconst_log_two]; ring
    linarith
  set r : ℝ := 324 * p with hrdef
  have hr1 : r ≤ 1 := by rw [hrdef]; linarith
  -- number of rounds
  set k : ℕ := Nat.log 2 m + 1 with hk
  have hmk : m < 2 ^ k := Nat.lt_pow_succ_log_self (by norm_num) m
  -- every cover of `H` is expensive
  have hcov : ∀ U : Finset (Finset α), IsCover H U → (1:ℝ) / 2 ≤ cost p U := by
    intro U hU
    by_contra hlt
    exact hns ⟨U, hU, le_of_lt (not_le.1 hlt)⟩
  have hind := main_induction (α := α) hp hrdef hr1 k m hmk H hH (1 / 2) (by norm_num) hcov
  have hmu34 : (3:ℝ) / 4 ≤ mu (dens r k) (upset H) := by
    have := ebound_le m
    linarith
  -- the density used in the induction is at most `ρ`
  have hklog : (k : ℝ) ≤ 2 * Real.log m / Real.log 2 := by
    have hm0 : m ≠ 0 := by omega
    have h1 : (2:ℝ) ^ (Nat.log 2 m) ≤ (m : ℝ) := by
      have := Nat.pow_log_le_self 2 hm0
      exact_mod_cast this
    have h2 : (Nat.log 2 m : ℝ) * Real.log 2 ≤ Real.log m := by
      have := Real.log_le_log (by positivity) h1
      rwa [Real.log_pow] at this
    have h3 : Real.log 2 ≤ Real.log m := hlogm
    rw [le_div_iff₀ hlog2, hk]
    push_cast
    linarith
  have hdensle : dens r k ≤ ρ := by
    have h1 : dens r k ≤ (k : ℝ) * r := dens_le_mul r (by linarith) hr1 k
    have h2 : (k : ℝ) * r ≤ Kconst * p * Real.log m := by
      rw [hrdef, Kconst]
      have h3 : (k : ℝ) * (324 * p) ≤ (2 * Real.log m / Real.log 2) * (324 * p) := by
        have : (0:ℝ) ≤ 324 * p := by linarith
        exact mul_le_mul_of_nonneg_right hklog this
      have h4 : (2 * Real.log m / Real.log 2) * (324 * p) = 648 / Real.log 2 * p * Real.log m := by
        field_simp
        ring
      linarith
    linarith
  have hdens0 : 0 ≤ dens r k := dens_nonneg (by linarith) hr1 k
  have hmono : mu (dens r k) (upset H) ≤ mu ρ (upset H) :=
    mu_mono hdens0 hdensle hρ1 (isUp_upset H)
  linarith

/-! ### Minimal elements, thresholds -/

/-- The minimal elements of a family. -/
noncomputable def minimalElts (F : Finset (Finset α)) : Finset (Finset α) :=
  F.filter (fun A => ∀ B ∈ F, B ⊆ A → B = A)

/-- `ell F` is the maximum of `2` and the largest size of a minimal element of `F`. -/
noncomputable def ell (F : Finset (Finset α)) : ℕ :=
  max 2 ((minimalElts F).sup Finset.card)

lemma two_le_ell (F : Finset (Finset α)) : 2 ≤ ell F := le_max_left _ _

lemma minimalElts_card_le {F : Finset (Finset α)} {S : Finset α} (hS : S ∈ minimalElts F) :
    S.card ≤ ell F :=
  le_trans (Finset.le_sup hS) (le_max_right _ _)

lemma exists_minimal_subset {F : Finset (Finset α)} {S : Finset α} (hS : S ∈ F) :
    ∃ A ∈ minimalElts F, A ⊆ S := by
  obtain ⟨A, hA, hAmin⟩ :=
    Finset.exists_min_image (F.filter (fun B => B ⊆ S)) Finset.card
      ⟨S, Finset.mem_filter.2 ⟨hS, Finset.Subset.refl S⟩⟩
  rw [Finset.mem_filter] at hA
  refine ⟨A, ?_, hA.2⟩
  rw [minimalElts, Finset.mem_filter]
  refine ⟨hA.1, ?_⟩
  intro B hB hBA
  have hmem : B ∈ F.filter (fun B => B ⊆ S) :=
    Finset.mem_filter.2 ⟨hB, hBA.trans hA.2⟩
  exact Finset.eq_of_subset_of_card_le hBA (hAmin B hmem)

lemma cover_of_cover_minimalElts {F : Finset (Finset α)} {U : Finset (Finset α)}
    (hU : IsCover (minimalElts F) U) : IsCover F U := by
  intro S hS
  obtain ⟨A, hA, hAS⟩ := exists_minimal_subset hS
  obtain ⟨u, hu, huA⟩ := hU A hA
  exact ⟨u, hu, huA.trans hAS⟩

lemma upset_minimalElts_subset {F : Finset (Finset α)} (hF : IsUp F) :
    upset (minimalElts F) ⊆ F := by
  intro A hA
  rw [mem_upset] at hA
  obtain ⟨S, hS, hSA⟩ := hA
  rw [minimalElts, Finset.mem_filter] at hS
  exact hF S hS.1 A hSA

/-- The expectation threshold: the largest `q` for which `F` is `q`-small. -/
noncomputable def qThreshold (F : Finset (Finset α)) : ℝ :=
  sSup {q : ℝ | 0 ≤ q ∧ q ≤ 1 ∧ IsSmall q F}

/-- The threshold: the largest `p` for which `mu p F ≤ 1/2`. -/
noncomputable def pThreshold (F : Finset (Finset α)) : ℝ :=
  sSup {p : ℝ | 0 ≤ p ∧ p ≤ 1 ∧ mu p F ≤ 1 / 2}

omit [Fintype α] [DecidableEq α] in
lemma qThreshold_nonneg (F : Finset (Finset α)) : 0 ≤ qThreshold F :=
  Real.sSup_nonneg (fun _ hx => hx.1)

omit [DecidableEq α] in
lemma pThreshold_bddAbove (F : Finset (Finset α)) :
    BddAbove {p : ℝ | 0 ≤ p ∧ p ≤ 1 ∧ mu p F ≤ 1 / 2} :=
  ⟨1, fun _ hx => hx.2.1⟩

/-- Below the threshold, the measure is at most `1/2`. -/
lemma mu_le_half_of_lt_pThreshold {F : Finset (Finset α)} (hF : IsUp F) {p : ℝ}
    (hp0 : 0 ≤ p) (h : p < pThreshold F) : mu p F ≤ 1 / 2 := by
  rcases Set.eq_empty_or_nonempty {p : ℝ | 0 ≤ p ∧ p ≤ 1 ∧ mu p F ≤ 1 / 2} with h0 | hne
  · rw [pThreshold, h0, Real.sSup_empty] at h
    linarith
  · obtain ⟨p', hp', hlt⟩ := exists_lt_of_lt_csSup hne h
    exact le_trans (mu_mono hp0 (le_of_lt hlt) hp'.2.1 hF) hp'.2.2

omit [DecidableEq α] in
/-- Above the threshold, the measure exceeds `1/2`. -/
lemma half_lt_mu_of_pThreshold_lt {F : Finset (Finset α)} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (h : pThreshold F < p) : 1 / 2 < mu p F := by
  by_contra hcon
  push_neg at hcon
  have : p ≤ pThreshold F := le_csSup (pThreshold_bddAbove F) ⟨hp0, hp1, hcon⟩
  linarith

omit [Fintype α] [DecidableEq α] in
lemma qThreshold_bddAbove (F : Finset (Finset α)) :
    BddAbove {q : ℝ | 0 ≤ q ∧ q ≤ 1 ∧ IsSmall q F} :=
  ⟨1, fun _ hx => hx.2.1⟩

end KahnKalai

namespace Math2

open KahnKalai

/-- **The Kahn-Kalai conjecture** (Park-Pham theorem): the threshold of an increasing
property is at most a universal constant times its expectation threshold times `log ℓ`,
where `ℓ` is the maximum of `2` and the size of a largest minimal element.

Here `mu p F = ∑_{A ∈ F} p^{|A|} (1-p)^{n-|A|}` is the product measure of `F`, the
threshold `pThreshold F` is the supremum of all `p ∈ [0,1]` with `mu p F ≤ 1/2`, and the
expectation threshold `qThreshold F` is the supremum of all `q ∈ [0,1]` such that `F` admits
a cover `U` (a family such that every member of `F` contains a member of `U`) with
`∑_{u ∈ U} q^{|u|} ≤ 1/2`. -/
theorem kahn_kalai :
    ∃ K : ℝ, 0 < K ∧
      ∀ {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Finset α)),
        IsUp F → pThreshold F ≤ K * qThreshold F * Real.log (ell F) := by
  refine ⟨Kconst, Kconst_pos, ?_⟩
  intro α _ _ F hF
  have hlog2 : (0:ℝ) < Real.log 2 := log_two_pos
  have hlogl : Real.log 2 ≤ Real.log (ell F) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast two_le_ell F)
  have hlogl0 : 0 < Real.log (ell F) := lt_of_lt_of_le hlog2 hlogl
  have hKl : 0 < Kconst * Real.log (ell F) := mul_pos Kconst_pos hlogl0
  have hqnn : 0 ≤ qThreshold F := qThreshold_nonneg F
  have hRHS : 0 ≤ Kconst * qThreshold F * Real.log (ell F) := by
    have : 0 ≤ Kconst * qThreshold F := mul_nonneg (le_of_lt Kconst_pos) hqnn
    positivity
  refine Real.sSup_le ?_ hRHS
  rintro p₀ ⟨hp₀0, hp₀1, hp₀mu⟩
  by_contra hcon
  push_neg at hcon
  -- choose `q` slightly above the expectation threshold
  set q : ℝ := p₀ / (Kconst * Real.log (ell F)) with hq
  have hqmul : q * (Kconst * Real.log (ell F)) = p₀ := by
    rw [hq, div_mul_cancel₀ _ (ne_of_gt hKl)]
  have hq0 : 0 < q := by
    have : 0 < p₀ := lt_of_le_of_lt hRHS hcon
    rw [hq]; positivity
  have hqbig : qThreshold F < q := by
    by_contra hle
    push_neg at hle
    have : q * (Kconst * Real.log (ell F)) ≤ qThreshold F * (Kconst * Real.log (ell F)) :=
      mul_le_mul_of_nonneg_right hle (le_of_lt hKl)
    rw [hqmul] at this
    nlinarith
  have hq1 : q ≤ 1 := by
    have h1 : Kconst * Real.log 2 = 648 := Kconst_log_two
    have h2 : (648:ℝ) ≤ Kconst * Real.log (ell F) := by nlinarith [Kconst_pos]
    rw [hq, div_le_one hKl]
    linarith
  -- `F` is not `q`-small
  have hnsF : ¬ IsSmall q F := by
    intro hsmall
    have : q ≤ qThreshold F :=
      le_csSup (qThreshold_bddAbove F) ⟨le_of_lt hq0, hq1, hsmall⟩
    linarith
  have hnsH : ¬ IsSmall q (minimalElts F) := by
    rintro ⟨U, hU, hcost⟩
    exact hnsF ⟨U, cover_of_cover_minimalElts hU, hcost⟩
  -- apply the hypergraph form
  have hmain := mu_gt_half_of_not_isSmall (α := α) (H := minimalElts F) (m := ell F)
    (two_le_ell F) (fun S hS => minimalElts_card_le hS) hq0 hnsH hp₀1
    (by rw [mul_comm Kconst q, mul_assoc, hqmul])
  have hsub : mu p₀ (upset (minimalElts F)) ≤ mu p₀ F :=
    mu_mono_subset hp₀0 hp₀1 (upset_minimalElts_subset hF)
  linarith

end Math2

/-
The key lemma of Park-Pham (in the Bernoulli setting): the cover made of the large
minimum fragments has small expected cost.
-/
import RequestProject.Fragments

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
lemma mem_Ufam_iff {H : Finset (Finset α)} {W U : Finset α} {m : ℕ} :
    U ∈ Ufam H W m ↔ ∃ S ∈ H, m ≤ 2 * (minFrag H W S).card ∧ minFrag H W S = U := by
  simp only [Ufam, bigG, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨S, ⟨hS, hbig⟩, hEq⟩; exact ⟨S, hS, hbig, hEq⟩
  · rintro ⟨S, hS, hbig, hEq⟩; exact ⟨S, ⟨hS, hbig⟩, hEq⟩

omit [Fintype α] in
lemma Ufam_disjoint {H : Finset (Finset α)} {W U : Finset α} {m : ℕ}
    (hU : U ∈ Ufam H W m) : Disjoint W U := by
  obtain ⟨S, hS, _, hEq⟩ := mem_Ufam_iff.1 hU
  rw [← hEq]
  exact minFrag_disjoint hS

omit [Fintype α] in
lemma Ufam_card {H : Finset (Finset α)} {W U : Finset α} {m : ℕ}
    (hU : U ∈ Ufam H W m) : m ≤ 2 * U.card := by
  obtain ⟨S, _, hbig, hEq⟩ := mem_Ufam_iff.1 hU
  rw [← hEq]; exact hbig

omit [Fintype α] in
lemma Ufam_subset_pick {H : Finset (Finset α)} {W U : Finset α} {m : ℕ}
    (hU : U ∈ Ufam H W m) : U ⊆ pick H (W ∪ U) := by
  obtain ⟨S, hS, _, hEq⟩ := mem_Ufam_iff.1 hU
  rw [← hEq]
  exact minFrag_subset_pick hS

/-- Reweighting: removing `U` from `W ∪ U` costs a factor at most `r ^ -|U|`. -/
lemma wt_union_bound {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) {W U : Finset α}
    (hd : Disjoint W U) {p : ℝ} (hp : 0 ≤ p) :
    wt r W * p ^ U.card ≤ wt r (W ∪ U) * (p / r) ^ U.card := by
  have hcard : (W ∪ U).card = W.card + U.card := Finset.card_union_of_disjoint hd
  have hn : W.card + U.card ≤ Fintype.card α := by
    rw [← hcard]; exact Finset.card_le_univ _
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card α - W.card = k + U.card :=
    ⟨Fintype.card α - W.card - U.card, by omega⟩
  have hk2 : Fintype.card α - (W.card + U.card) = k := by omega
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hX : 0 ≤ r ^ W.card * (1 - r) ^ k * p ^ U.card := by
    have : (0:ℝ) ≤ 1 - r := by linarith
    positivity
  have hLHS : wt r W * p ^ U.card
      = (r ^ W.card * (1 - r) ^ k * p ^ U.card) * (1 - r) ^ U.card := by
    simp only [wt, wtOn, Finset.card_univ, hk]
    rw [pow_add]; ring
  have hRHS : wt r (W ∪ U) * (p / r) ^ U.card
      = r ^ W.card * (1 - r) ^ k * p ^ U.card := by
    simp only [wt, wtOn, Finset.card_univ, hcard, hk2]
    rw [div_pow, pow_add]
    field_simp
  rw [hLHS, hRHS]
  have h1 : (1 - r) ^ U.card ≤ 1 :=
    pow_le_one₀ (by linarith) (by linarith)
  nlinarith

lemma sum_finset_as_ite (s : Finset (Finset α)) (f : Finset α → ℝ) :
    ∑ U ∈ s, f U = ∑ U : Finset α, if U ∈ s then f U else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext U; simp

/-- **Key Lemma.** If `H` is `m`-bounded with `m ≥ 1` and `r = c^2 * p`, then the expected
cost of the fragment cover `Ufam H W m` is at most `(2/c)^m`. -/
lemma expected_cost_le {H : Finset (Finset α)} {m : ℕ}
    (hH : ∀ S ∈ H, S.card ≤ m) {p r c : ℝ} (hp : 0 < p) (hc : 1 ≤ c)
    (hr : r = c ^ 2 * p) (hr1 : r ≤ 1) :
    ∑ W : Finset α, wt r W * cost p (Ufam H W m) ≤ (2 / c) ^ m := by
  have hc0 : (0:ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hr0 : 0 < r := by rw [hr]; positivity
  have hpr : p / r = (1 / c ^ 2) := by
    rw [hr]; field_simp
  classical
  set Pairs : Finset (Finset α × Finset α) :=
    Finset.univ.filter (fun q => q.2 ∈ Ufam H q.1 m) with hPairs
  set φ : Finset α × Finset α → Finset α × Finset α := fun q => (q.1 ∪ q.2, q.2) with hφ
  set Target : Finset (Finset α × Finset α) :=
    Finset.univ.filter (fun q => q.2 ⊆ pick H q.1 ∧ m ≤ 2 * q.2.card) with hTarget
  have hPairsSum : ∀ g : Finset α × Finset α → ℝ,
      ∑ q ∈ Pairs, g q
        = ∑ W : Finset α, ∑ U : Finset α, if U ∈ Ufam H W m then g (W, U) else 0 := by
    intro g
    rw [hPairs, Finset.sum_filter, Fintype.sum_prod_type]
  -- Step 1: rewrite the left-hand side as a sum over pairs
  have step1 : ∑ W : Finset α, wt r W * cost p (Ufam H W m)
      = ∑ q ∈ Pairs, wt r q.1 * p ^ q.2.card := by
    rw [hPairsSum (fun q => wt r q.1 * p ^ q.2.card)]
    refine Finset.sum_congr rfl ?_
    intro W _
    rw [cost, Finset.mul_sum, sum_finset_as_ite (Ufam H W m) (fun U => wt r W * p ^ U.card)]
  -- Step 2: pointwise reweighting
  have step2 : ∑ q ∈ Pairs, wt r q.1 * p ^ q.2.card
      ≤ ∑ q ∈ Pairs, wt r (q.1 ∪ q.2) * (p / r) ^ q.2.card := by
    refine Finset.sum_le_sum ?_
    intro q hq
    rw [hPairs, Finset.mem_filter] at hq
    exact wt_union_bound hr0 hr1 (Ufam_disjoint hq.2) (le_of_lt hp)
  -- Step 3: reindex by `Z = W ∪ U`
  have hinj : Set.InjOn φ ↑Pairs := by
    intro q1 hq1 q2 hq2 hEq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hPairs] at hq1 hq2
    simp only [hφ, Prod.mk.injEq] at hEq
    obtain ⟨h2, h1⟩ := hEq
    have d1 : Disjoint q1.1 q1.2 := Ufam_disjoint hq1.2
    have d2 : Disjoint q2.1 q2.2 := Ufam_disjoint hq2.2
    have hfst : q1.1 = q2.1 := by
      have e1 : (q1.1 ∪ q1.2) \ q1.2 = q1.1 := by
        rw [Finset.union_sdiff_right]
        exact Finset.sdiff_eq_self_of_disjoint d1
      have e2 : (q2.1 ∪ q2.2) \ q2.2 = q2.1 := by
        rw [Finset.union_sdiff_right]
        exact Finset.sdiff_eq_self_of_disjoint d2
      have e3 : q1.1 = (q2.1 ∪ q2.2) \ q2.2 := by
        rw [← h2, ← h1]; exact e1.symm
      rw [e3, e2]
    exact Prod.ext hfst h1
  have step3 : ∑ q ∈ Pairs, wt r (q.1 ∪ q.2) * (p / r) ^ q.2.card
      = ∑ q ∈ Pairs.image φ, wt r q.1 * (p / r) ^ q.2.card := by
    rw [Finset.sum_image hinj]
  -- Step 4: the image is contained in the target set
  have step4 : Pairs.image φ ⊆ Target := by
    intro q hq
    simp only [Finset.mem_image, hPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨q0, hq0, hEq⟩ := hq
    rw [hTarget, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [← hEq]
      exact Ufam_subset_pick hq0
    · rw [← hEq]
      exact Ufam_card hq0
  have hnonneg : ∀ q : Finset α × Finset α, 0 ≤ wt r q.1 * (p / r) ^ q.2.card := by
    intro q
    have h1 : 0 ≤ wt r q.1 := wt_nonneg (le_of_lt hr0) hr1 _
    have h2 : 0 ≤ (p / r) ^ q.2.card := by positivity
    exact mul_nonneg h1 h2
  have step5 : ∑ q ∈ Pairs.image φ, wt r q.1 * (p / r) ^ q.2.card
      ≤ ∑ q ∈ Target, wt r q.1 * (p / r) ^ q.2.card :=
    Finset.sum_le_sum_of_subset_of_nonneg step4 (fun q _ _ => hnonneg q)
  -- Step 6: bound the sum over the target set
  have step6 : ∑ q ∈ Target, wt r q.1 * (p / r) ^ q.2.card ≤ (2 / c) ^ m := by
    have hsplit : ∑ q ∈ Target, wt r q.1 * (p / r) ^ q.2.card
        = ∑ Z : Finset α, ∑ U : Finset α,
            if U ⊆ pick H Z ∧ m ≤ 2 * U.card then wt r Z * (p / r) ^ U.card else 0 := by
      rw [hTarget, Finset.sum_filter, Fintype.sum_prod_type]
    rw [hsplit]
    have hinner : ∀ Z : Finset α,
        (∑ U : Finset α, if U ⊆ pick H Z ∧ m ≤ 2 * U.card then wt r Z * (p / r) ^ U.card else 0)
          ≤ wt r Z * (2 / c) ^ m := by
      intro Z
      have hwZ : 0 ≤ wt r Z := wt_nonneg (le_of_lt hr0) hr1 _
      have hstep : (∑ U : Finset α,
            if U ⊆ pick H Z ∧ m ≤ 2 * U.card then wt r Z * (p / r) ^ U.card else 0)
          = wt r Z * ∑ U : Finset α,
            if U ⊆ pick H Z ∧ m ≤ 2 * U.card then (p / r) ^ U.card else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun U _ => ?_)
        by_cases h : U ⊆ pick H Z ∧ m ≤ 2 * U.card <;> simp [h]
      rw [hstep]
      refine mul_le_mul_of_nonneg_left ?_ hwZ
      -- bound the number of relevant `U` and each term
      have hterm : ∀ U : Finset α,
          (if U ⊆ pick H Z ∧ m ≤ 2 * U.card then (p / r) ^ U.card else 0)
            ≤ (if U ⊆ pick H Z then (1 / c) ^ m else 0) := by
        intro U
        by_cases h : U ⊆ pick H Z ∧ m ≤ 2 * U.card
        · rw [if_pos h, if_pos h.1, hpr]
          have : (1 / c ^ 2 : ℝ) ^ U.card = (1 / c) ^ (2 * U.card) := by
            rw [two_mul, pow_add, ← mul_pow]
            congr 1
            field_simp
          rw [this]
          exact pow_le_pow_of_le_one (by positivity) (by rw [div_le_one hc0]; linarith) h.2
        · rw [if_neg h]
          by_cases h2 : U ⊆ pick H Z
          · rw [if_pos h2]; positivity
          · rw [if_neg h2]
      calc (∑ U : Finset α,
            if U ⊆ pick H Z ∧ m ≤ 2 * U.card then (p / r) ^ U.card else 0)
          ≤ ∑ U : Finset α, if U ⊆ pick H Z then (1 / c) ^ m else 0 :=
            Finset.sum_le_sum (fun U _ => hterm U)
        _ = ((pick H Z).powerset.card : ℝ) * (1 / c) ^ m := by
            rw [← Finset.sum_filter]
            have : (Finset.univ.filter (fun U : Finset α => U ⊆ pick H Z))
                = (pick H Z).powerset := by
              ext U; simp
            rw [this, Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 ^ m : ℝ) * (1 / c) ^ m := by
            have hcard : ((pick H Z).powerset.card : ℝ) ≤ (2 ^ m : ℝ) := by
              rw [Finset.card_powerset]
              have := pick_card_le hH Z
              exact_mod_cast Nat.pow_le_pow_right (by norm_num) this
            have : (0:ℝ) ≤ (1 / c) ^ m := by positivity
            exact mul_le_mul_of_nonneg_right hcard this
        _ = (2 / c) ^ m := by
            rw [div_pow, div_pow]
            field_simp
            rw [one_pow]
    calc ∑ Z : Finset α, ∑ U : Finset α,
          (if U ⊆ pick H Z ∧ m ≤ 2 * U.card then wt r Z * (p / r) ^ U.card else 0)
        ≤ ∑ Z : Finset α, wt r Z * (2 / c) ^ m := Finset.sum_le_sum (fun Z _ => hinner Z)
      _ = (2 / c) ^ m := by rw [← Finset.sum_mul, sum_wt, one_mul]
  linarith [step1, step2, step3, step5, step6]

end KahnKalai

/-
Product ("Bernoulli") weights on the powerset of a finite set, and the two basic
identities we need:

* the total mass is `1`;
* the union of two independent random sets of densities `a` and `b` is a random
  set of density `a + b - a*b`.
-/
import Mathlib

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α]

/-- `wtOn s p A = p ^ |A| * (1-p) ^ (|s| - |A|)`: the probability that the `p`-random
subset of `s` equals `A` (for `A ⊆ s`). -/
noncomputable def wtOn (s : Finset α) (p : ℝ) (A : Finset α) : ℝ :=
  p ^ A.card * (1 - p) ^ (s.card - A.card)

omit [DecidableEq α] in
lemma wtOn_nonneg {s : Finset α} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset α) :
    0 ≤ wtOn s p A :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

lemma wtOn_insert_not_mem {x : α} {s : Finset α} (hx : x ∉ s) (p : ℝ) {A : Finset α}
    (hA : A ⊆ s) : wtOn (insert x s) p A = (1 - p) * wtOn s p A := by
  have h1 : (insert x s).card = s.card + 1 := Finset.card_insert_of_notMem hx
  have h2 : A.card ≤ s.card := Finset.card_le_card hA
  simp only [wtOn, h1]
  rw [show s.card + 1 - A.card = (s.card - A.card) + 1 by omega, pow_succ]
  ring

lemma wtOn_insert_mem {x : α} {s : Finset α} (hx : x ∉ s) (p : ℝ) {A : Finset α}
    (hA : A ⊆ s) : wtOn (insert x s) p (insert x A) = p * wtOn s p A := by
  have hxA : x ∉ A := fun h => hx (hA h)
  have h1 : (insert x s).card = s.card + 1 := Finset.card_insert_of_notMem hx
  have h3 : (insert x A).card = A.card + 1 := Finset.card_insert_of_notMem hxA
  have h2 : A.card ≤ s.card := Finset.card_le_card hA
  simp only [wtOn, h1, h3]
  rw [show s.card + 1 - (A.card + 1) = s.card - A.card by omega, pow_succ]
  ring

/-- Splitting a weighted sum over the powerset of `insert x s`. -/
lemma sum_powerset_insert_wt {x : α} {s : Finset α} (hx : x ∉ s) (p : ℝ)
    (F : Finset α → ℝ) :
    ∑ B ∈ (insert x s).powerset, wtOn (insert x s) p B * F B
      = (1 - p) * (∑ B ∈ s.powerset, wtOn s p B * F B)
        + p * (∑ B ∈ s.powerset, wtOn s p B * F (insert x B)) := by
  rw [Finset.sum_powerset_insert hx, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro B hB
    rw [wtOn_insert_not_mem hx p (mem_powerset.1 hB)]
    ring
  · refine Finset.sum_congr rfl ?_
    intro B hB
    rw [wtOn_insert_mem hx p (mem_powerset.1 hB)]
    ring

/-- The total mass of the `p`-weights on the powerset of `s` is `1`. -/
lemma sum_wtOn (s : Finset α) (p : ℝ) : ∑ A ∈ s.powerset, wtOn s p A = 1 := by
  have h := Finset.prod_add (fun _ : α => p) (fun _ : α => (1 - p)) s
  simp only [Finset.prod_const] at h
  rw [show p + (1 - p) = 1 by ring] at h
  simp only [one_pow] at h
  rw [h]
  refine Finset.sum_congr rfl ?_
  intro A hA
  rw [Finset.mem_powerset] at hA
  rw [wtOn, Finset.card_sdiff_of_subset hA]

/-- The union of independent `a`- and `b`-random subsets of `s` is an
`(a + b - a*b)`-random subset of `s`. -/
lemma union_wtOn (a b : ℝ) (s : Finset α) : ∀ f : Finset α → ℝ,
    ∑ A ∈ s.powerset, ∑ B ∈ s.powerset, wtOn s a A * wtOn s b B * f (A ∪ B)
      = ∑ C ∈ s.powerset, wtOn s (a + b - a * b) C * f C := by
  induction s using Finset.induction_on with
  | empty => intro f; simp [wtOn]
  | insert x s hx ih =>
      intro f
      have hc : 1 - (a + b - a * b) = (1 - a) * (1 - b) := by ring
      -- abbreviation for the double sum over `s`
      set S : (Finset α → ℝ) → ℝ := fun g =>
        ∑ A ∈ s.powerset, ∑ B ∈ s.powerset, wtOn s a A * wtOn s b B * g (A ∪ B) with hS
      have hpull : ∀ (g : Finset α → ℝ) (A : Finset α),
          wtOn s a A * (∑ B ∈ s.powerset, wtOn s b B * g (A ∪ B))
            = ∑ B ∈ s.powerset, wtOn s a A * wtOn s b B * g (A ∪ B) := by
        intro g A
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun B _ => by ring)
      -- inner sums
      have hG : ∀ A : Finset α, A ⊆ s →
          (∑ B ∈ (insert x s).powerset, wtOn (insert x s) b B * f (A ∪ B))
            = (1 - b) * (∑ B ∈ s.powerset, wtOn s b B * f (A ∪ B))
              + b * (∑ B ∈ s.powerset, wtOn s b B * f (insert x (A ∪ B))) := by
        intro A _
        rw [sum_powerset_insert_wt hx b (fun B => f (A ∪ B))]
        congr 2
        refine Finset.sum_congr rfl ?_
        intro B _
        rw [Finset.union_insert]
      have hG' : ∀ A : Finset α, A ⊆ s →
          (∑ B ∈ (insert x s).powerset, wtOn (insert x s) b B * f (insert x A ∪ B))
            = (1 - b) * (∑ B ∈ s.powerset, wtOn s b B * f (insert x (A ∪ B)))
              + b * (∑ B ∈ s.powerset, wtOn s b B * f (insert x (A ∪ B))) := by
        intro A _
        rw [sum_powerset_insert_wt hx b (fun B => f (insert x A ∪ B))]
        congr 2
        · refine Finset.sum_congr rfl ?_
          intro B _
          rw [Finset.insert_union]
        · refine Finset.sum_congr rfl ?_
          intro B _
          rw [Finset.insert_union, Finset.union_insert, Finset.insert_idem]
      -- rewrite the left-hand side
      have hL : ∑ A ∈ (insert x s).powerset, ∑ B ∈ (insert x s).powerset,
            wtOn (insert x s) a A * wtOn (insert x s) b B * f (A ∪ B)
          = (1 - a) * (1 - b) * S f + (a + b - a * b) * S (fun C => f (insert x C)) := by
        have e1 : ∀ A : Finset α, (∑ B ∈ (insert x s).powerset,
              wtOn (insert x s) a A * wtOn (insert x s) b B * f (A ∪ B))
            = wtOn (insert x s) a A *
                ∑ B ∈ (insert x s).powerset, wtOn (insert x s) b B * f (A ∪ B) := by
          intro A
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun B _ => by ring)
        simp only [e1]
        rw [sum_powerset_insert_wt hx a
          (fun A => ∑ B ∈ (insert x s).powerset, wtOn (insert x s) b B * f (A ∪ B))]
        have r1 : (∑ A ∈ s.powerset, wtOn s a A *
              ∑ B ∈ (insert x s).powerset, wtOn (insert x s) b B * f (A ∪ B))
            = (1 - b) * S f + b * S (fun C => f (insert x C)) := by
          rw [hS]
          beta_reduce
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro A hA
          rw [hG A (mem_powerset.1 hA), mul_add, ← mul_assoc, ← mul_assoc]
          rw [mul_comm (wtOn s a A) (1 - b), mul_comm (wtOn s a A) b]
          rw [mul_assoc, mul_assoc, hpull f A, hpull (fun C => f (insert x C)) A]
        have r2 : (∑ A ∈ s.powerset, wtOn s a A *
              ∑ B ∈ (insert x s).powerset, wtOn (insert x s) b B * f (insert x A ∪ B))
            = S (fun C => f (insert x C)) := by
          rw [hS]
          beta_reduce
          refine Finset.sum_congr rfl ?_
          intro A hA
          rw [hG' A (mem_powerset.1 hA)]
          have : (1 - b) * (∑ B ∈ s.powerset, wtOn s b B * f (insert x (A ∪ B)))
              + b * (∑ B ∈ s.powerset, wtOn s b B * f (insert x (A ∪ B)))
              = ∑ B ∈ s.powerset, wtOn s b B * f (insert x (A ∪ B)) := by ring
          rw [this, hpull (fun C => f (insert x C)) A]
        rw [r1, r2]
        ring
      rw [hL, sum_powerset_insert_wt hx (a + b - a * b) f, hc]
      simp only [hS]
      rw [ih f, ih (fun C => f (insert x C))]

end KahnKalai

