import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/
def Covers (H : Finset (Finset X)) (W : Finset X) : Prop := ∃ S ∈ H, S ⊆ W

instance (H : Finset (Finset X)) (W : Finset X) : Decidable (Covers H W) := by
  unfold Covers; infer_instance

/-- The cost `∑_{S ∈ G} p ^ |S|` of a family `G`. -/
def cost (p : ℝ) (G : Finset (Finset X)) : ℝ := ∑ S ∈ G, p ^ S.card

/-- `G` is a cover of `H`: every edge of `H` contains a member of `G`. -/
def IsCover (G H : Finset (Finset X)) : Prop := ∀ S ∈ H, ∃ T ∈ G, T ⊆ S

/-- `H` is `p`-small with threshold `c`: it admits a cover of cost at most `c`. -/
def IsSmall (p c : ℝ) (H : Finset (Finset X)) : Prop :=
  ∃ G : Finset (Finset X), IsCover G H ∧ cost p G ≤ c

lemma cost_nonneg {p : ℝ} (hp : 0 ≤ p) (G : Finset (Finset X)) : 0 ≤ cost p G :=
  Finset.sum_nonneg fun S _ => pow_nonneg hp _

lemma cost_union_le {p : ℝ} (hp : 0 ≤ p) (G G' : Finset (Finset X)) :
    cost p (G ∪ G') ≤ cost p G + cost p G' := by
  have hsplit : G ∪ G' = G ∪ (G' \ G) := by
    ext T; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  unfold cost
  rw [hsplit, Finset.sum_union (Finset.disjoint_sdiff)]
  gcongr
  · exact Finset.sdiff_subset

/-- The candidate fragments of `S` relative to `W`. -/
def cand (H : Finset (Finset X)) (W S : Finset X) : Finset (Finset X) :=
  (H.filter (fun S' => S' ⊆ W ∪ S)).image (fun S' => S' \ W)

lemma cand_nonempty {H : Finset (Finset X)} {W S : Finset X} (hS : S ∈ H) :
    (cand H W S).Nonempty := by
  refine ⟨S \ W, ?_⟩
  simp only [cand, Finset.mem_image, Finset.mem_filter]
  exact ⟨S, ⟨hS, Finset.subset_union_right⟩, rfl⟩

/-- A *minimum fragment* `T(S, W)`: a set of smallest size of the form `S' \ W`
with `S' ∈ H` and `S' ⊆ W ∪ S`. -/
noncomputable def frag (H : Finset (Finset X)) (W S : Finset X) : Finset X :=
  if h : (cand H W S).Nonempty then
    (Finset.exists_min_image (cand H W S) Finset.card h).choose
  else ∅

lemma frag_mem_cand {H : Finset (Finset X)} {W S : Finset X} (hS : S ∈ H) :
    frag H W S ∈ cand H W S := by
  have h := cand_nonempty (H := H) (W := W) hS
  rw [frag, dif_pos h]
  exact (Finset.exists_min_image (cand H W S) Finset.card h).choose_spec.1

lemma frag_min {H : Finset (Finset X)} {W S : Finset X} (hS : S ∈ H) :
    ∀ T ∈ cand H W S, (frag H W S).card ≤ T.card := by
  have h := cand_nonempty (H := H) (W := W) hS
  rw [frag, dif_pos h]
  exact (Finset.exists_min_image (cand H W S) Finset.card h).choose_spec.2

lemma frag_spec {H : Finset (Finset X)} {W S : Finset X} (hS : S ∈ H) :
    ∃ S' ∈ H, S' ⊆ W ∪ S ∧ frag H W S = S' \ W := by
  have h := frag_mem_cand (W := W) hS
  simp only [cand, Finset.mem_image, Finset.mem_filter] at h
  obtain ⟨S', ⟨hS'H, hS'sub⟩, hEq⟩ := h
  exact ⟨S', hS'H, hS'sub, hEq.symm⟩

lemma frag_subset {H : Finset (Finset X)} {W S : Finset X} (hS : S ∈ H) :
    frag H W S ⊆ S := by
  obtain ⟨S', _, hS'sub, hEq⟩ := frag_spec (W := W) hS
  rw [hEq]
  intro y hy
  simp only [Finset.mem_sdiff] at hy
  rcases Finset.mem_union.mp (hS'sub hy.1) with h | h
  · exact absurd h hy.2
  · exact h

lemma frag_disjoint {H : Finset (Finset X)} {W S : Finset X} (hS : S ∈ H) :
    Disjoint (frag H W S) W := by
  obtain ⟨S', _, _, hEq⟩ := frag_spec (W := W) hS
  rw [hEq]
  exact Finset.sdiff_disjoint

lemma frag_card_le {H : Finset (Finset X)} {W S : Finset X} (hS : S ∈ H) :
    (frag H W S).card ≤ S.card :=
  Finset.card_le_card (frag_subset hS)

/-- Capture property: `W ∪ T(S,W)` contains an edge of `H`. -/
lemma frag_capture {H : Finset (Finset X)} {W S : Finset X} (hS : S ∈ H) :
    ∃ S' ∈ H, S' ⊆ W ∪ frag H W S := by
  obtain ⟨S', hS'H, _, hEq⟩ := frag_spec (W := W) hS
  refine ⟨S', hS'H, ?_⟩
  rw [hEq]
  intro y hy
  by_cases hyW : y ∈ W
  · exact Finset.mem_union_left _ hyW
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hy, hyW⟩)

/-- Key minimality property: every edge of `H` inside `W ∪ T(S,W)` contains `T(S,W)`. -/
lemma frag_key {H : Finset (Finset X)} {W S : Finset X} (hS : S ∈ H)
    {Ŝ : Finset X} (hŜ : Ŝ ∈ H) (hsub : Ŝ ⊆ W ∪ frag H W S) :
    frag H W S ⊆ Ŝ := by
  set T := frag H W S with hT
  -- `Ŝ \ W ⊆ T`
  have h1 : Ŝ \ W ⊆ T := by
    intro y hy
    simp only [Finset.mem_sdiff] at hy
    rcases Finset.mem_union.mp (hsub hy.1) with h | h
    · exact absurd h hy.2
    · exact h
  -- `Ŝ` is a candidate, so `|T| ≤ |Ŝ \ W|`
  have h2 : Ŝ \ W ∈ cand H W S := by
    have hŜsub : Ŝ ⊆ W ∪ S := by
      intro y hy
      rcases Finset.mem_union.mp (hsub hy) with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (frag_subset hS h)
    simp only [cand, Finset.mem_image, Finset.mem_filter]
    exact ⟨Ŝ, ⟨hŜ, hŜsub⟩, rfl⟩
  have h3 : T.card ≤ (Ŝ \ W).card := frag_min hS _ h2
  have h4 : Ŝ \ W = T := Finset.eq_of_subset_of_card_le h1 h3
  calc T = Ŝ \ W := h4.symm
    _ ⊆ Ŝ := Finset.sdiff_subset

/-- Edges whose minimum fragment is large. -/
noncomputable def bigFam (H : Finset (Finset X)) (W : Finset X) (m₀ : ℕ) : Finset (Finset X) :=
  H.filter (fun S => m₀ < (frag H W S).card)

/-- The cover produced in one round. -/
noncomputable def coverFam (H : Finset (Finset X)) (W : Finset X) (m₀ : ℕ) :
    Finset (Finset X) :=
  (bigFam H W m₀).image (fun S => frag H W S)

/-- The hypergraph carried to the next round. -/
noncomputable def nextFam (H : Finset (Finset X)) (W : Finset X) (m₀ : ℕ) :
    Finset (Finset X) :=
  (H.filter (fun S => (frag H W S).card ≤ m₀)).image (fun S => frag H W S)

lemma nextFam_bounded {H : Finset (Finset X)} {W : Finset X} {m₀ : ℕ} :
    ∀ T ∈ nextFam H W m₀, T.card ≤ m₀ := by
  intro T hT
  simp only [nextFam, Finset.mem_image, Finset.mem_filter] at hT
  obtain ⟨S, ⟨_, hcard⟩, hEq⟩ := hT
  rw [← hEq]; exact hcard

lemma nextFam_subset_ground {H : Finset (Finset X)} {W V : Finset X} {m₀ : ℕ}
    (hV : ∀ S ∈ H, S ⊆ V) : ∀ T ∈ nextFam H W m₀, T ⊆ V := by
  intro T hT
  simp only [nextFam, Finset.mem_image, Finset.mem_filter] at hT
  obtain ⟨S, ⟨hSH, _⟩, hEq⟩ := hT
  rw [← hEq]
  exact (frag_subset hSH).trans (hV S hSH)

/-- Capture property for the next-round hypergraph. -/
lemma nextFam_capture {H : Finset (Finset X)} {W : Finset X} {m₀ : ℕ}
    {T : Finset X} (hT : T ∈ nextFam H W m₀) : ∃ S' ∈ H, S' ⊆ W ∪ T := by
  simp only [nextFam, Finset.mem_image, Finset.mem_filter] at hT
  obtain ⟨S, ⟨hSH, _⟩, hEq⟩ := hT
  rw [← hEq]
  exact frag_capture hSH

/-- If the next-round hypergraph is covered by `W₂` then `H` is covered by `W ∪ W₂`. -/
lemma covers_of_covers_nextFam {H : Finset (Finset X)} {W W₂ : Finset X} {m₀ : ℕ}
    (h : Covers (nextFam H W m₀) W₂) : Covers H (W ∪ W₂) := by
  obtain ⟨T, hT, hTW₂⟩ := h
  obtain ⟨S', hS'H, hS'sub⟩ := nextFam_capture hT
  exact ⟨S', hS'H, hS'sub.trans (Finset.union_subset_union_right hTW₂)⟩

/-- A cover of the next-round hypergraph, together with the round's cover, covers `H`. -/
lemma isCover_union {H : Finset (Finset X)} {W : Finset X} {m₀ : ℕ}
    {G : Finset (Finset X)} (hG : IsCover G (nextFam H W m₀)) :
    IsCover (G ∪ coverFam H W m₀) H := by
  intro S hS
  by_cases hbig : m₀ < (frag H W S).card
  · refine ⟨frag H W S, ?_, frag_subset hS⟩
    apply Finset.mem_union_right
    simp only [coverFam, Finset.mem_image]
    exact ⟨S, by simp [bigFam, hS, hbig], rfl⟩
  · have hmem : frag H W S ∈ nextFam H W m₀ := by
      simp only [nextFam, Finset.mem_image, Finset.mem_filter]
      exact ⟨S, ⟨hS, le_of_not_gt hbig⟩, rfl⟩
    obtain ⟨T, hTG, hTsub⟩ := hG _ hmem
    exact ⟨T, Finset.mem_union_left _ hTG, hTsub.trans (frag_subset hS)⟩

end Math2

import Mathlib

/-!
# Finite Bernoulli (product) measure on subsets of a finite ground set

`wt V p A` is the probability that the `p`-random subset of the ground set `V`
equals `A`, and `Exp V p f` is the corresponding expectation of `f`.
Everything is a finite sum; no measure theory is used.
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- Bernoulli weight: probability that the `p`-random subset of `V` is exactly `A`. -/
def wt (V : Finset X) (p : ℝ) (A : Finset X) : ℝ := p ^ A.card * (1 - p) ^ (V \ A).card

/-- Expectation of `f` with respect to the `p`-random subset of `V`. -/
def Exp (V : Finset X) (p : ℝ) (f : Finset X → ℝ) : ℝ := ∑ A ∈ V.powerset, wt V p A * f A

lemma wt_nonneg {V : Finset X} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset X) :
    0 ≤ wt V p A := by
  unfold wt
  have : (0:ℝ) ≤ 1 - p := by linarith
  positivity

lemma sum_wt (V : Finset X) (p : ℝ) : ∑ A ∈ V.powerset, wt V p A = 1 := by
  have h := Finset.prod_add (fun _ : X => p) (fun _ : X => (1 - p)) V
  simp only [Finset.prod_const] at h
  rw [show p + (1 - p) = (1:ℝ) by ring, one_pow] at h
  unfold wt
  rw [← h]

lemma Exp_const (V : Finset X) (p : ℝ) (c : ℝ) : Exp V p (fun _ => c) = c := by
  unfold Exp
  rw [← Finset.sum_mul, sum_wt, one_mul]

lemma Exp_mono {V : Finset X} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f g : Finset X → ℝ}
    (h : ∀ A ∈ V.powerset, f A ≤ g A) : Exp V p f ≤ Exp V p g := by
  unfold Exp
  refine Finset.sum_le_sum ?_
  intro A hA
  exact mul_le_mul_of_nonneg_left (h A hA) (wt_nonneg hp0 hp1 A)

lemma Exp_nonneg {V : Finset X} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f : Finset X → ℝ}
    (h : ∀ A ∈ V.powerset, 0 ≤ f A) : 0 ≤ Exp V p f := by
  have := Exp_mono (V := V) (p := p) hp0 hp1 (f := fun _ => (0:ℝ)) (g := f) (by simpa using h)
  simpa [Exp_const] using this

lemma Exp_le_of_le {V : Finset X} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f : Finset X → ℝ}
    {c : ℝ} (h : ∀ A ∈ V.powerset, f A ≤ c) : Exp V p f ≤ c := by
  have := Exp_mono (V := V) (p := p) hp0 hp1 (f := f) (g := fun _ => c) h
  simpa [Exp_const] using this

lemma Exp_add (V : Finset X) (p : ℝ) (f g : Finset X → ℝ) :
    Exp V p (fun A => f A + g A) = Exp V p f + Exp V p g := by
  unfold Exp
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun A _ => by ring)

lemma Exp_div (V : Finset X) (p : ℝ) (f : Finset X → ℝ) (c : ℝ) :
    Exp V p (fun A => f A / c) = Exp V p f / c := by
  unfold Exp
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun A _ => by ring)

lemma wt_insert_of_notMem {V : Finset X} {x : X} (hx : x ∉ V) {A : Finset X} (hA : A ⊆ V)
    (p : ℝ) : wt (insert x V) p A = (1 - p) * wt V p A := by
  have hxA : x ∉ A := fun h => hx (hA h)
  have : (insert x V) \ A = insert x (V \ A) := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨(rfl | hy), hy2⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hy, hy2⟩
    · rintro (rfl | ⟨hy, hy2⟩)
      · exact ⟨Or.inl rfl, hxA⟩
      · exact ⟨Or.inr hy, hy2⟩
  unfold wt
  rw [this, Finset.card_insert_of_notMem (by simp [hx]), pow_succ]
  ring

lemma wt_insert_of_mem {V : Finset X} {x : X} (hx : x ∉ V) {A : Finset X} (hA : A ⊆ V)
    (p : ℝ) : wt (insert x V) p (insert x A) = p * wt V p A := by
  have hxA : x ∉ A := fun h => hx (hA h)
  have h1 : (insert x V) \ (insert x A) = V \ A := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
    constructor
    · rintro ⟨(rfl | hy), hy2, hy3⟩
      · exact absurd rfl hy2
      · exact ⟨hy, hy3⟩
    · rintro ⟨hy, hy2⟩
      refine ⟨Or.inr hy, ?_, hy2⟩
      rintro rfl
      exact hx hy
  unfold wt
  rw [h1, Finset.card_insert_of_notMem hxA, pow_succ]
  ring

lemma Exp_insert {V : Finset X} {x : X} (hx : x ∉ V) (p : ℝ) (f : Finset X → ℝ) :
    Exp (insert x V) p f
      = (1 - p) * Exp V p f + p * Exp V p (fun A => f (insert x A)) := by
  unfold Exp
  rw [Finset.sum_powerset_insert hx]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun A hA => ?_)
    rw [wt_insert_of_notMem hx (Finset.mem_powerset.mp hA)]
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun A hA => ?_)
    rw [wt_insert_of_mem hx (Finset.mem_powerset.mp hA)]
    ring

lemma Exp_linear (V : Finset X) (c r s : ℝ) (F G : Finset X → ℝ) :
    Exp V c (fun W => r * F W + s * G W) = r * Exp V c F + s * Exp V c G := by
  unfold Exp
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun A _ => by ring

/-- Two independent rounds: the union of an `a`-random and a `b`-random subset is
`(a + b - a*b)`-random. -/
lemma Exp_union (a b : ℝ) :
    ∀ (V : Finset X) (f : Finset X → ℝ),
      Exp V a (fun W₁ => Exp V b (fun W₂ => f (W₁ ∪ W₂))) = Exp V (a + b - a * b) f := by
  intro V
  induction V using Finset.induction_on with
  | empty => intro f; simp [Exp, wt]
  | insert x V₀ hx ih =>
      intro f
      have inner1 : ∀ (h : Finset X → ℝ) (W₁ : Finset X),
          Exp (insert x V₀) b (fun W₂ => h (W₁ ∪ W₂))
            = (1 - b) * Exp V₀ b (fun W₂ => h (W₁ ∪ W₂))
              + b * Exp V₀ b (fun W₂ => h (insert x (W₁ ∪ W₂))) := by
        intro h W₁
        rw [Exp_insert hx]
        simp only [Finset.union_insert]
      have inner2 : ∀ A : Finset X,
          Exp (insert x V₀) b (fun W₂ => f (insert x (A ∪ W₂)))
            = Exp V₀ b (fun W₂ => f (insert x (A ∪ W₂))) := by
        intro A
        rw [Exp_insert hx]
        simp only [Finset.union_insert, Finset.insert_idem]
        ring
      rw [Exp_insert hx]
      simp only [inner1, Finset.insert_union, inner2]
      rw [Exp_linear V₀ a (1 - b) b, ih f, ih (fun U => f (insert x U)), Exp_insert hx]
      ring

import RequestProject.KeyLemma

/-!
# The Park–Pham iteration

Repeatedly applying the key lemma, halving the bound on the edge sizes each time.
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- Total density after all the rounds used for an `ℓ`-bounded hypergraph. -/
noncomputable def qq (L p : ℝ) : ℕ → ℝ
  | 0 => 0
  | (n + 1) => L * p + qq L p ((n + 1) / 2) - L * p * qq L p ((n + 1) / 2)

/-- The number of rounds used for an `ℓ`-bounded hypergraph. -/
def rounds : ℕ → ℕ
  | 0 => 0
  | (n + 1) => 1 + rounds ((n + 1) / 2)

/-- The bound on the expected cost of one round, for an `ℓ`-bounded hypergraph. -/
noncomputable def Aterm (L : ℝ) (ℓ : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc (ℓ / 2 + 1) ℓ, 2 ^ ℓ * (1 / L) ^ m

/-- The bound on the total expected cost of the cover produced by the whole iteration. -/
noncomputable def Bb (L : ℝ) : ℕ → ℝ
  | 0 => 0
  | (n + 1) => Aterm L (n + 1) + Bb L ((n + 1) / 2)

lemma qq_zero (L p : ℝ) : qq L p 0 = 0 := by rw [qq]

lemma qq_succ (L p : ℝ) (n : ℕ) :
    qq L p (n + 1) = L * p + qq L p ((n + 1) / 2) - L * p * qq L p ((n + 1) / 2) := by
  rw [qq]

lemma Bb_succ (L : ℝ) (n : ℕ) : Bb L (n + 1) = Aterm L (n + 1) + Bb L ((n + 1) / 2) := by
  rw [Bb]

lemma Aterm_nonneg {L : ℝ} (hL : 0 < L) (ℓ : ℕ) : 0 ≤ Aterm L ℓ := by
  unfold Aterm
  refine Finset.sum_nonneg fun m _ => ?_
  have : (0:ℝ) ≤ (1 / L) ^ m := by positivity
  positivity

lemma Bb_nonneg {L : ℝ} (hL : 0 < L) : ∀ ℓ : ℕ, 0 ≤ Bb L ℓ := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    match ℓ with
    | 0 => simp [Bb]
    | (n + 1) =>
      rw [Bb_succ]
      have h1 := Aterm_nonneg hL (n + 1)
      have h2 := ih ((n + 1) / 2) (by omega)
      linarith

lemma qq_mem {L p : ℝ} (hδ0 : 0 ≤ L * p) (hδ1 : L * p ≤ 1) :
    ∀ ℓ : ℕ, 0 ≤ qq L p ℓ ∧ qq L p ℓ ≤ 1 := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    match ℓ with
    | 0 => simp [qq_zero]
    | (n + 1) =>
      obtain ⟨h1, h2⟩ := ih ((n + 1) / 2) (by omega)
      rw [qq_succ]
      constructor <;> nlinarith

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

import RequestProject.Frag

/-!
# The Park–Pham key lemma

The cover built from the minimum fragments of one random round has small expected cost.
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

lemma Exp_sum {ι : Type*} (V : Finset X) (p : ℝ) (s : Finset ι) (f : ι → Finset X → ℝ) :
    Exp V p (fun A => ∑ i ∈ s, f i A) = ∑ i ∈ s, Exp V p (f i) := by
  simp only [Exp, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- A chosen edge of `H` inside `Z`, when there is one. -/
noncomputable def pick (H : Finset (Finset X)) (Z : Finset X) : Finset X :=
  if h : Covers H Z then h.choose else ∅

lemma pick_mem {H : Finset (Finset X)} {Z : Finset X} (h : Covers H Z) :
    pick H Z ∈ H ∧ pick H Z ⊆ Z := by
  rw [pick, dif_pos h]
  exact ⟨h.choose_spec.1, h.choose_spec.2⟩

lemma pick_card_le {H : Finset (Finset X)} {ℓ : ℕ} (hbd : ∀ S ∈ H, S.card ≤ ℓ)
    (Z : Finset X) : (pick H Z).card ≤ ℓ := by
  by_cases h : Covers H Z
  · exact hbd _ (pick_mem h).1
  · simp [pick, h]

/-- Facts about the members of the one-round cover. -/
lemma coverFam_spec {H : Finset (Finset X)} {W U : Finset X} {m₀ : ℕ}
    (hU : U ∈ coverFam H W m₀) : ∃ S ∈ H, m₀ < (frag H W S).card ∧ U = frag H W S := by
  simp only [coverFam, bigFam, Finset.mem_image, Finset.mem_filter] at hU
  obtain ⟨S, ⟨hSH, hbig⟩, hEq⟩ := hU
  exact ⟨S, hSH, hbig, hEq.symm⟩

lemma coverFam_disjoint {H : Finset (Finset X)} {W U : Finset X} {m₀ : ℕ}
    (hU : U ∈ coverFam H W m₀) : Disjoint U W := by
  obtain ⟨S, hSH, _, rfl⟩ := coverFam_spec hU
  exact frag_disjoint hSH

lemma coverFam_subset_ground {V : Finset X} {H : Finset (Finset X)} {W U : Finset X} {m₀ : ℕ}
    (hV : ∀ S ∈ H, S ⊆ V) (hU : U ∈ coverFam H W m₀) : U ⊆ V := by
  obtain ⟨S, hSH, _, rfl⟩ := coverFam_spec hU
  exact (frag_subset hSH).trans (hV S hSH)

lemma coverFam_card_lt {H : Finset (Finset X)} {W U : Finset X} {m₀ : ℕ}
    (hU : U ∈ coverFam H W m₀) : m₀ < U.card := by
  obtain ⟨S, _, hbig, rfl⟩ := coverFam_spec hU
  exact hbig

lemma coverFam_card_le {H : Finset (Finset X)} {ℓ : ℕ} (hbd : ∀ S ∈ H, S.card ≤ ℓ)
    {W U : Finset X} {m₀ : ℕ} (hU : U ∈ coverFam H W m₀) : U.card ≤ ℓ := by
  obtain ⟨S, hSH, _, rfl⟩ := coverFam_spec hU
  exact (frag_card_le hSH).trans (hbd S hSH)

/-- Members of the one-round cover are contained in the chosen edge of `W ∪ U`. -/
lemma coverFam_subset_pick {H : Finset (Finset X)} {W U : Finset X} {m₀ : ℕ}
    (hU : U ∈ coverFam H W m₀) : U ⊆ pick H (W ∪ U) := by
  obtain ⟨S, hSH, _, rfl⟩ := coverFam_spec hU
  have hcov : Covers H (W ∪ frag H W S) := frag_capture hSH
  obtain ⟨hmem, hsub⟩ := pick_mem hcov
  exact frag_key hSH hmem hsub

lemma wt_le_wt_union {V W U : Finset X} {δ p : ℝ} {m : ℕ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hp : 0 ≤ p)
    (hWV : W ⊆ V) (hUV : U ⊆ V) (hdisj : Disjoint U W) (hcard : U.card = m) :
    wt V δ W * p ^ m ≤ wt V δ (W ∪ U) * (p / δ) ^ m := by
  have hUW : U ⊆ V \ W := by
    intro y hy
    exact Finset.mem_sdiff.mpr ⟨hUV hy, fun h => (Finset.disjoint_left.mp hdisj hy) h⟩
  have hsplit : (V \ (W ∪ U)).card + m = (V \ W).card := by
    have h1 : V \ (W ∪ U) = (V \ W) \ U := by
      ext y; simp only [Finset.mem_sdiff, Finset.mem_union, not_or]; tauto
    rw [h1, ← hcard]
    exact Finset.card_sdiff_add_card_eq_card hUW
  have hcardU : (W ∪ U).card = W.card + m := by
    rw [Finset.card_union_of_disjoint hdisj.symm, hcard]
  have h1mδ : (0:ℝ) ≤ 1 - δ := by linarith
  set k := (V \ (W ∪ U)).card with hk
  have hleft : wt V δ W * p ^ m = δ ^ W.card * (1 - δ) ^ (k + m) * p ^ m := by
    unfold wt
    rw [← hsplit]
  have hright : wt V δ (W ∪ U) * (p / δ) ^ m = δ ^ W.card * (1 - δ) ^ k * p ^ m := by
    unfold wt
    rw [hcardU, div_pow, ← hk]
    field_simp
    ring
  rw [hleft, hright, pow_add]
  have : (1 - δ) ^ m ≤ 1 := pow_le_one₀ h1mδ (by linarith)
  have hnn : 0 ≤ δ ^ W.card * (1 - δ) ^ k * p ^ m := by positivity
  nlinarith [pow_nonneg h1mδ k, pow_nonneg hp m, pow_nonneg (le_of_lt hδ0) W.card,
    pow_nonneg h1mδ m]

/-- Rewriting a nested sum as a sum over a filtered product. -/
lemma sum_nested_eq (V : Finset X) (t : Finset X → Finset (Finset X))
    (ht : ∀ W ∈ V.powerset, t W ⊆ V.powerset) (F : Finset X → Finset X → ℝ) :
    ∑ W ∈ V.powerset, ∑ U ∈ t W, F W U
      = ∑ x ∈ (V.powerset ×ˢ V.powerset).filter (fun x => x.2 ∈ t x.1), F x.1 x.2 := by
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun W hW => ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun U _ => rfl)
  ext U
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨ht W hW h, h⟩, fun h => h.2⟩

/-- **Key Lemma** (Park–Pham).  With `δ` the density of one round, the expected cost of the
cover produced by that round is small. -/
theorem key_lemma {V : Finset X} {H : Finset (Finset X)} {ℓ m₀ : ℕ} {p δ : ℝ}
    (hV : ∀ S ∈ H, S ⊆ V) (hbd : ∀ S ∈ H, S.card ≤ ℓ)
    (hp : 0 ≤ p) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Exp V δ (fun W => cost p (coverFam H W m₀))
      ≤ ∑ m ∈ Finset.Icc (m₀ + 1) ℓ, 2 ^ ℓ * (p / δ) ^ m := by
  -- split the cover by the size of its members
  have hsplit : ∀ W : Finset X,
      cost p (coverFam H W m₀)
        = ∑ m ∈ Finset.Icc (m₀ + 1) ℓ,
            ∑ U ∈ (coverFam H W m₀).filter (fun U => U.card = m), p ^ U.card := by
    intro W
    show ∑ U ∈ coverFam H W m₀, p ^ U.card = _
    refine (Finset.sum_fiberwise_of_maps_to (g := fun U : Finset X => U.card) ?_ _).symm
    intro U hU
    exact Finset.mem_Icc.mpr ⟨coverFam_card_lt hU, coverFam_card_le hbd hU⟩
  simp only [hsplit]
  rw [Exp_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  -- fix `m` and bound one term
  set cm : Finset X → Finset (Finset X) :=
    fun W => (coverFam H W m₀).filter (fun U => U.card = m) with hcm
  have hcmsub : ∀ W ∈ V.powerset, cm W ⊆ V.powerset := by
    intro W _ U hU
    simp only [hcm, Finset.mem_filter] at hU
    exact Finset.mem_powerset.mpr (coverFam_subset_ground hV hU.1)
  have hstep1 : Exp V δ (fun W => ∑ U ∈ cm W, p ^ U.card)
      = ∑ W ∈ V.powerset, ∑ U ∈ cm W, wt V δ W * p ^ m := by
    unfold Exp
    refine Finset.sum_congr rfl fun W _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun U hU => ?_
    simp only [hcm, Finset.mem_filter] at hU
    rw [hU.2]
  rw [hstep1, sum_nested_eq V cm hcmsub (fun W U => wt V δ W * p ^ m)]
  -- pass to the sets `Z = W ∪ U`
  set P₁ := (V.powerset ×ˢ V.powerset).filter (fun x : Finset X × Finset X => x.2 ∈ cm x.1)
    with hP₁
  set P₂ := (V.powerset ×ˢ V.powerset).filter
    (fun y : Finset X × Finset X => y.2 ⊆ y.1 ∧ y.2 ∈ cm (y.1 \ y.2)) with hP₂
  have hmem₁ : ∀ x ∈ P₁, x.1 ⊆ V ∧ x.2 ∈ cm x.1 := by
    intro x hx
    simp only [hP₁, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hx
    exact ⟨hx.1.1, hx.2⟩
  have hstep2 : ∑ x ∈ P₁, wt V δ x.1 * p ^ m ≤ ∑ x ∈ P₁, wt V δ (x.1 ∪ x.2) * (p / δ) ^ m := by
    refine Finset.sum_le_sum fun x hx => ?_
    obtain ⟨hxV, hxcm⟩ := hmem₁ x hx
    simp only [hcm, Finset.mem_filter] at hxcm
    exact wt_le_wt_union hδ0 hδ1 hp hxV (coverFam_subset_ground hV hxcm.1)
      (coverFam_disjoint hxcm.1) hxcm.2
  have hstep3 : ∑ x ∈ P₁, wt V δ (x.1 ∪ x.2) * (p / δ) ^ m
      = ∑ y ∈ P₂, wt V δ y.1 * (p / δ) ^ m := by
    refine Finset.sum_nbij' (i := fun x : Finset X × Finset X => (x.1 ∪ x.2, x.2))
      (j := fun y : Finset X × Finset X => (y.1 \ y.2, y.2)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨hxV, hxcm⟩ := hmem₁ x hx
      have hcm' := hxcm
      simp only [hcm, Finset.mem_filter] at hcm'
      have hdisj : Disjoint x.2 x.1 := coverFam_disjoint hcm'.1
      have hUV : x.2 ⊆ V := coverFam_subset_ground hV hcm'.1
      have hEq : (x.1 ∪ x.2) \ x.2 = x.1 := by
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact h1
          · exact absurd h1 h2
        · intro h
          exact ⟨Or.inl h, fun hy => (Finset.disjoint_left.mp hdisj hy) h⟩
      simp only [hP₂, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
      refine ⟨⟨Finset.union_subset hxV hUV, hUV⟩, Finset.subset_union_right, ?_⟩
      rw [hEq]; exact hxcm
    · intro y hy
      simp only [hP₂, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hy
      simp only [hP₁, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
      exact ⟨⟨(Finset.sdiff_subset).trans hy.1.1, hy.1.2⟩, hy.2.2⟩
    · intro x hx
      obtain ⟨_, hxcm⟩ := hmem₁ x hx
      simp only [hcm, Finset.mem_filter] at hxcm
      have hdisj : Disjoint x.2 x.1 := coverFam_disjoint hxcm.1
      have hEq : (x.1 ∪ x.2) \ x.2 = x.1 := by
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact h1
          · exact absurd h1 h2
        · intro h
          exact ⟨Or.inl h, fun hy => (Finset.disjoint_left.mp hdisj hy) h⟩
      simp [hEq]
    · intro y hy
      simp only [hP₂, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hy
      have : (y.1 \ y.2) ∪ y.2 = y.1 := Finset.sdiff_union_of_subset hy.2.1
      simp [this]
    · intro x _
      rfl
  -- now bound the sum over `P₂`
  have hstep4 : ∑ y ∈ P₂, wt V δ y.1 * (p / δ) ^ m
      ≤ ∑ Z ∈ V.powerset, ∑ U ∈ (pick H Z).powerset, wt V δ Z * (p / δ) ^ m := by
    have hP₂eq : ∑ y ∈ P₂, wt V δ y.1 * (p / δ) ^ m
        = ∑ Z ∈ V.powerset, ∑ U ∈ V.powerset.filter
            (fun U => U ⊆ Z ∧ U ∈ cm (Z \ U)), wt V δ Z * (p / δ) ^ m := by
      rw [hP₂, Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun Z _ => ?_
      rw [Finset.sum_filter]
    rw [hP₂eq]
    refine Finset.sum_le_sum fun Z hZ => ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro U hU
      simp only [Finset.mem_filter, Finset.mem_powerset] at hU ⊢
      obtain ⟨_, hUZ, hUcm⟩ := hU
      simp only [hcm, Finset.mem_filter] at hUcm
      have hsub : U ⊆ pick H ((Z \ U) ∪ U) := coverFam_subset_pick hUcm.1
      rwa [Finset.sdiff_union_of_subset hUZ] at hsub
    · intro U _ _
      have : (0:ℝ) ≤ wt V δ Z := wt_nonneg (le_of_lt hδ0) hδ1 Z
      have h2 : (0:ℝ) ≤ (p / δ) ^ m := by positivity
      positivity
  refine le_trans hstep2 (le_trans (le_of_eq hstep3) (le_trans hstep4 ?_))
  -- finally: each fiber has at most `2 ^ ℓ` elements
  have hfin : ∀ Z ∈ V.powerset,
      ∑ U ∈ (pick H Z).powerset, wt V δ Z * (p / δ) ^ m
        ≤ 2 ^ ℓ * ((p / δ) ^ m * wt V δ Z) := by
    intro Z _
    rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
    push_cast
    have hcard : ((2:ℝ) ^ (pick H Z).card) ≤ 2 ^ ℓ := by
      apply pow_le_pow_right₀ (by norm_num)
      exact pick_card_le hbd Z
    have hnn : (0:ℝ) ≤ wt V δ Z * (p / δ) ^ m := by
      have := wt_nonneg (le_of_lt hδ0) hδ1 (V := V) (p := δ) Z
      have h2 : (0:ℝ) ≤ (p / δ) ^ m := by positivity
      positivity
    calc ((2:ℝ) ^ (pick H Z).card) * (wt V δ Z * (p / δ) ^ m)
        ≤ 2 ^ ℓ * (wt V δ Z * (p / δ) ^ m) := by
          exact mul_le_mul_of_nonneg_right hcard hnn
      _ = 2 ^ ℓ * ((p / δ) ^ m * wt V δ Z) := by ring
  calc ∑ Z ∈ V.powerset, ∑ U ∈ (pick H Z).powerset, wt V δ Z * (p / δ) ^ m
      ≤ ∑ Z ∈ V.powerset, 2 ^ ℓ * ((p / δ) ^ m * wt V δ Z) := Finset.sum_le_sum hfin
    _ = 2 ^ ℓ * (p / δ) ^ m := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, sum_wt, mul_one]

end Math2

