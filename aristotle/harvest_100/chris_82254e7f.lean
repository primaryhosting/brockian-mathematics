import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
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

namespace CS

/-! ## Walks

A walk starting at a vertex `src` is described by the list `l` of vertices it visits
after `src`, in order.  Since we work with a complete weighted graph (a non-edge can be
modelled by a suitably large weight), every list of vertices describes a walk. -/

section Walks

variable {V : Type*}

/-- The final vertex of the walk that starts at `src` and then visits `l` in order. -/
def walkEnd (src : V) : List V → V
  | [] => src
  | v :: t => walkEnd v t

/-- The total weight of the walk that starts at `src` and then visits `l` in order. -/
def walkWt (w : V → V → ℝ) (src : V) : List V → ℝ
  | [] => 0
  | v :: t => w src v + walkWt w v t

@[simp] lemma walkEnd_nil (src : V) : walkEnd src ([] : List V) = src := rfl

@[simp] lemma walkEnd_cons (src v : V) (t : List V) : walkEnd src (v :: t) = walkEnd v t := rfl

@[simp] lemma walkWt_nil (w : V → V → ℝ) (src : V) : walkWt w src [] = 0 := rfl

@[simp] lemma walkWt_cons (w : V → V → ℝ) (src v : V) (t : List V) :
    walkWt w src (v :: t) = w src v + walkWt w v t := rfl

lemma walkEnd_append (src : V) (l₁ l₂ : List V) :
    walkEnd src (l₁ ++ l₂) = walkEnd (walkEnd src l₁) l₂ := by
  induction l₁ generalizing src with
  | nil => simp
  | cons a t ih => simp [ih]

lemma walkWt_append (w : V → V → ℝ) (src : V) (l₁ l₂ : List V) :
    walkWt w src (l₁ ++ l₂) = walkWt w src l₁ + walkWt w (walkEnd src l₁) l₂ := by
  induction l₁ generalizing src with
  | nil => simp
  | cons a t ih => simp [ih]; ring

lemma walkWt_nonneg (w : V → V → ℝ) (hw : ∀ u v, 0 ≤ w u v) (src : V) (l : List V) :
    0 ≤ walkWt w src l := by
  induction l generalizing src with
  | nil => simp
  | cons a t ih => exact add_nonneg (hw _ _) (ih a)

lemma walkEnd_mem_cons (v : V) (t : List V) : walkEnd v t ∈ v :: t := by
  induction t generalizing v with
  | nil => simp
  | cons a s ih =>
      have := ih a
      simp only [walkEnd_cons, List.mem_cons] at this ⊢
      tauto

/-- A walk that only ever visits its starting vertex ends where it started. -/
lemma walkEnd_const (src : V) (l : List V) (h : ∀ y ∈ l, y = src) : walkEnd src l = src := by
  induction l generalizing src with
  | nil => simp
  | cons a t ih =>
      have ha : a = src := h a (by simp)
      subst ha
      exact ih a fun y hy => h y (by simp [hy])

/-- Splitting a list at the last occurrence of an element. -/
lemma exists_last_split [DecidableEq V] (u : V) (l : List V) (h : u ∈ l) :
    ∃ l₁ l₂ : List V, l = l₁ ++ u :: l₂ ∧ u ∉ l₂ := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
      by_cases ht : u ∈ t
      · obtain ⟨l₁, l₂, h1, h2⟩ := ih ht
        exact ⟨a :: l₁, l₂, by simp [h1], h2⟩
      · have : a = u := by
          rcases List.mem_cons.1 h with h' | h'
          · exact h'.symm
          · exact absurd h' ht
        exact ⟨[], t, by simp [this], ht⟩

/-- Splitting a list at the first element outside a finite set. -/
lemma exists_first_split [DecidableEq V] (S : Finset V) (l : List V) (h : ∃ x ∈ l, x ∉ S) :
    ∃ (l₁ : List V) (b : V) (l₂ : List V),
      l = l₁ ++ b :: l₂ ∧ (∀ y ∈ l₁, y ∈ S) ∧ b ∉ S := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
      by_cases ha : a ∈ S
      · have ht : ∃ x ∈ t, x ∉ S := by
          obtain ⟨x, hx, hxS⟩ := h
          rcases List.mem_cons.1 hx with rfl | hx'
          · exact absurd ha hxS
          · exact ⟨x, hx', hxS⟩
        obtain ⟨l₁, b, l₂, h1, h2, h3⟩ := ih ht
        refine ⟨a :: l₁, b, l₂, by simp [h1], ?_, h3⟩
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy'
        · exact ha
        · exact h2 y hy'
      · exact ⟨[], a, t, by simp, by simp, ha⟩

end Walks

/-! ## The algorithm -/

section Algorithm

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex of `s` minimising `d`. -/
noncomputable def pickMin (s : Finset V) (d : V → ℝ) (h : s.Nonempty) : V :=
  (Finset.exists_min_image s d h).choose

omit [Fintype V] [DecidableEq V] in
lemma pickMin_mem (s : Finset V) (d : V → ℝ) (h : s.Nonempty) : pickMin s d h ∈ s :=
  (Finset.exists_min_image s d h).choose_spec.1

omit [Fintype V] [DecidableEq V] in
lemma pickMin_le (s : Finset V) (d : V → ℝ) (h : s.Nonempty) :
    ∀ b ∈ s, d (pickMin s d h) ≤ d b :=
  (Finset.exists_min_image s d h).choose_spec.2

/-- One step of Dijkstra's algorithm: settle an unsettled vertex of minimal tentative
distance and relax all edges out of it. -/
noncomputable def dijkstraStep (w : V → V → ℝ) (p : Finset V × (V → ℝ)) :
    Finset V × (V → ℝ) :=
  if h : (p.1ᶜ).Nonempty then
    (insert (pickMin p.1ᶜ p.2 h) p.1,
      fun v => min (p.2 v) (p.2 (pickMin p.1ᶜ p.2 h) + w (pickMin p.1ᶜ p.2 h) v))
  else p

/-- The initial state: only the source is settled, tentative distances are the direct
edge weights out of the source. -/
noncomputable def dijkstraInit (w : V → V → ℝ) (src : V) : Finset V × (V → ℝ) :=
  ({src}, fun v => if v = src then 0 else w src v)

/-- Dijkstra's algorithm: iterate the settle-and-relax step `|V|` times. -/
noncomputable def dijkstra (w : V → V → ℝ) (src : V) : V → ℝ :=
  ((dijkstraStep w)^[Fintype.card V] (dijkstraInit w src)).2

/-- The loop invariant of Dijkstra's algorithm. -/
structure Inv (w : V → V → ℝ) (src : V) (p : Finset V × (V → ℝ)) : Prop where
  /-- the source is settled -/
  src_mem : src ∈ p.1
  /-- every tentative distance is realised by a walk whose intermediate vertices are settled -/
  realize : ∀ v : V, ∃ l : List V,
    (∀ y ∈ l, y ∈ insert v p.1) ∧ walkEnd src l = v ∧ walkWt w src l = p.2 v
  /-- settled vertices carry the true shortest-path distance -/
  settled : ∀ x ∈ p.1, ∀ l : List V, walkEnd src l = x → p.2 x ≤ walkWt w src l
  /-- tentative distances beat every walk through settled vertices followed by one edge -/
  frontier : ∀ l : List V, (∀ y ∈ src :: l, y ∈ p.1) →
    ∀ v : V, p.2 v ≤ walkWt w src l + w (walkEnd src l) v

omit [Fintype V] in
lemma inv_init (w : V → V → ℝ) (hw : ∀ u v, 0 ≤ w u v) (src : V) :
    Inv w src (dijkstraInit w src) := by
  constructor
  · simp [dijkstraInit]
  · intro v
    by_cases hv : v = src
    · subst hv
      exact ⟨[], by simp, by simp, by simp [dijkstraInit]⟩
    · exact ⟨[v], by simp, by simp, by simp [dijkstraInit, hv]⟩
  · intro x hx l hl
    have hx' : x = src := by simpa [dijkstraInit] using hx
    simpa [dijkstraInit, hx'] using walkWt_nonneg w hw src l
  · intro l hl v
    have hall : ∀ y ∈ l, y = src := by
      intro y hy
      simpa [dijkstraInit] using hl y (by simp [hy])
    have hend : walkEnd src l = src := walkEnd_const src l hall
    have hnn : 0 ≤ walkWt w src l := walkWt_nonneg w hw src l
    rw [hend]
    have hww : 0 ≤ w src v := hw src v
    by_cases hv : v = src
    · simp only [dijkstraInit, if_pos hv]
      linarith
    · simp only [dijkstraInit, if_neg hv]
      linarith

lemma inv_step (w : V → V → ℝ) (hw : ∀ u v, 0 ≤ w u v) (src : V)
    (p : Finset V × (V → ℝ)) (hp : Inv w src p) : Inv w src (dijkstraStep w p) := by
  by_cases h : (p.1ᶜ).Nonempty
  swap
  · rw [dijkstraStep, dif_neg h]
    exact hp
  rw [dijkstraStep, dif_pos h]
  set S := p.1 with hS
  set d := p.2 with hd
  set u := pickMin (Sᶜ) d h with hu
  have hu_not : u ∉ S := by simpa using pickMin_mem (Sᶜ) d h
  have hu_min : ∀ v : V, v ∉ S → d u ≤ d v := by
    intro v hv
    exact pickMin_le (Sᶜ) d h v (by simpa using hv)
  -- the newly settled vertex already carries its true distance
  have K1 : ∀ l : List V, walkEnd src l = u → d u ≤ walkWt w src l := by
    intro l hl
    have hex : ∃ x ∈ l, x ∉ S := by
      cases l with
      | nil =>
          simp only [walkEnd_nil] at hl
          exact absurd (hl ▸ hp.src_mem) hu_not
      | cons a t =>
          refine ⟨walkEnd a t, walkEnd_mem_cons a t, ?_⟩
          simp only [walkEnd_cons] at hl
          rw [hl]
          exact hu_not
    obtain ⟨l₁, b, l₂, rfl, hl₁, hb⟩ := exists_first_split S l hex
    have h1 : d b ≤ walkWt w src l₁ + w (walkEnd src l₁) b := by
      refine hp.frontier l₁ ?_ b
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact hp.src_mem
      · exact hl₁ y hy'
    have h2 : 0 ≤ walkWt w b l₂ := walkWt_nonneg w hw b l₂
    have h3 : walkWt w src (l₁ ++ b :: l₂)
        = walkWt w src l₁ + (w (walkEnd src l₁) b + walkWt w b l₂) := by
      rw [walkWt_append]
      simp
    have h4 := hu_min b hb
    rw [h3]
    linarith
  -- relaxing from `u` cannot improve an already settled vertex
  have K2 : ∀ x ∈ S, d x ≤ d u + w u x := by
    intro x hx
    obtain ⟨lu, -, hlu_end, hlu_wt⟩ := hp.realize u
    have hend : walkEnd src (lu ++ [x]) = x := by
      rw [walkEnd_append, hlu_end]
      simp
    have hwt : walkWt w src (lu ++ [x]) = d u + w u x := by
      rw [walkWt_append, hlu_end, hlu_wt]
      simp [hd]
    have := hp.settled x hx (lu ++ [x]) hend
    rw [hwt] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Finset.mem_insert_of_mem hp.src_mem
  · -- realisability
    intro v
    dsimp only
    rcases le_total (d v) (d u + w u v) with hle | hle
    · obtain ⟨l, hsub, hend, hwt⟩ := hp.realize v
      refine ⟨l, ?_, hend, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.1 (hsub y hy) with h' | h'
        · exact Finset.mem_insert.2 (Or.inl h')
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h')
      · rw [hwt, min_eq_left hle]
    · obtain ⟨lu, hsub, hlu_end, hlu_wt⟩ := hp.realize u
      refine ⟨lu ++ [v], ?_, ?_, ?_⟩
      · intro y hy
        rcases List.mem_append.1 hy with hy' | hy'
        · rcases Finset.mem_insert.1 (hsub y hy') with h' | h'
          · exact Finset.mem_insert_of_mem (Finset.mem_insert.2 (Or.inl h'))
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h')
        · simp only [List.mem_singleton] at hy'
          exact Finset.mem_insert.2 (Or.inl hy')
      · rw [walkEnd_append, hlu_end]
        simp
      · rw [walkWt_append, hlu_end, hlu_wt, min_eq_right hle]
        simp [hd]
  · -- settled vertices are optimal
    intro x hx l hl
    dsimp only at hx ⊢
    rcases Finset.mem_insert.1 hx with rfl | hx'
    · exact le_trans (min_le_left _ _) (K1 l hl)
    · exact le_trans (min_le_left _ _) (hp.settled x hx' l hl)
  · -- the frontier estimate
    intro l hl v
    dsimp only at hl ⊢
    by_cases hul : u ∈ l
    swap
    · refine le_trans (min_le_left _ _) (hp.frontier l ?_ v)
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact hp.src_mem
      · rcases Finset.mem_insert.1 (hl y (List.mem_cons_of_mem _ hy')) with h' | h'
        · exact absurd (h' ▸ hy') hul
        · exact h'
    obtain ⟨l₁, l₂, rfl, hl₂⟩ := exists_last_split u l hul
    have hl₂S : ∀ y ∈ l₂, y ∈ S := by
      intro y hy
      have hy' : y ∈ insert u S :=
        hl y (List.mem_cons_of_mem _ (by simp [hy]))
      rcases Finset.mem_insert.1 hy' with h' | h'
      · exact absurd (h' ▸ hy) hl₂
      · exact h'
    have hPend : walkEnd src (l₁ ++ [u]) = u := by
      rw [walkEnd_append]
      simp
    have hPwt : walkWt w src (l₁ ++ [u])
        = walkWt w src l₁ + w (walkEnd src l₁) u := by
      rw [walkWt_append]
      simp
    have hPle : d u ≤ walkWt w src l₁ + w (walkEnd src l₁) u := by
      have := K1 (l₁ ++ [u]) hPend
      rwa [hPwt] at this
    cases l₂ with
    | nil =>
        have hend : walkEnd src (l₁ ++ [u]) = u := hPend
        have hwt : walkWt w src (l₁ ++ [u])
            = walkWt w src l₁ + w (walkEnd src l₁) u := hPwt
        refine le_trans (min_le_right _ _) ?_
        rw [hend, hwt]
        linarith
    | cons y rest =>
        have hyS : y ∈ S := hl₂S y (by simp)
        have hrest : ∀ z ∈ rest, z ∈ S := fun z hz => hl₂S z (by simp [hz])
        obtain ⟨ly, hly_sub, hly_end, hly_wt⟩ := hp.realize y
        have hly_S : ∀ z ∈ ly, z ∈ S := by
          intro z hz
          rcases Finset.mem_insert.1 (hly_sub z hz) with h' | h'
          · exact h' ▸ hyS
          · exact h'
        have hL := hp.frontier (ly ++ rest) (by
          intro z hz
          rcases List.mem_cons.1 hz with rfl | hz'
          · exact hp.src_mem
          · rcases List.mem_append.1 hz' with hz'' | hz''
            · exact hly_S z hz''
            · exact hrest z hz'') v
        rw [walkEnd_append, hly_end, walkWt_append, hly_end, hly_wt] at hL
        have hyle : d y ≤ d u + w u y := K2 y hyS
        have hbigend : walkEnd src (l₁ ++ u :: y :: rest) = walkEnd y rest := by
          rw [walkEnd_append]
          simp
        have hbigwt : walkWt w src (l₁ ++ u :: y :: rest)
            = walkWt w src l₁ + (w (walkEnd src l₁) u + (w u y + walkWt w y rest)) := by
          rw [walkWt_append]
          simp
        refine le_trans (min_le_left _ _) ?_
        rw [hbigend, hbigwt]
        linarith

lemma inv_iterate (w : V → V → ℝ) (hw : ∀ u v, 0 ≤ w u v) (src : V) (k : ℕ) :
    Inv w src ((dijkstraStep w)^[k] (dijkstraInit w src)) := by
  induction k with
  | zero => simpa using inv_init w hw src
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact inv_step w hw src _ ih

lemma step_fst_univ (w : V → V → ℝ) (p : Finset V × (V → ℝ)) (h : p.1 = Finset.univ) :
    (dijkstraStep w p).1 = Finset.univ := by
  have : ¬ (p.1ᶜ).Nonempty := by
    rw [h]
    simp
  simp [dijkstraStep, h]

lemma step_fst_card (w : V → V → ℝ) (p : Finset V × (V → ℝ)) (h : p.1 ≠ Finset.univ) :
    (dijkstraStep w p).1.card = p.1.card + 1 := by
  have hne : (p.1ᶜ).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc
    exact h ((Finset.compl_eq_empty_iff p.1).1 hc)
  have hmem : pickMin p.1ᶜ p.2 hne ∈ p.1ᶜ := pickMin_mem _ _ _
  have hnot : pickMin p.1ᶜ p.2 hne ∉ p.1 := by simpa using hmem
  simp only [dijkstraStep, dif_pos hne]
  exact Finset.card_insert_of_notMem hnot

lemma card_iterate (w : V → V → ℝ) (src : V) (k : ℕ) :
    ((dijkstraStep w)^[k] (dijkstraInit w src)).1 = Finset.univ ∨
      1 + k ≤ (((dijkstraStep w)^[k] (dijkstraInit w src)).1).card := by
  induction k with
  | zero =>
      right
      simp [dijkstraInit]
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · exact Or.inl (step_fst_univ w _ h)
      · by_cases hu : ((dijkstraStep w)^[n] (dijkstraInit w src)).1 = Finset.univ
        · exact Or.inl (step_fst_univ w _ hu)
        · right
          rw [step_fst_card w _ hu]
          omega

lemma settled_univ (w : V → V → ℝ) (src : V) :
    ((dijkstraStep w)^[Fintype.card V] (dijkstraInit w src)).1 = Finset.univ := by
  rcases card_iterate w src (Fintype.card V) with h | h
  · exact h
  · exfalso
    have := Finset.card_le_univ ((dijkstraStep w)^[Fintype.card V] (dijkstraInit w src)).1
    omega

/-- **Correctness of Dijkstra's algorithm.**  On a finite graph with nonnegative weights,
the value computed by Dijkstra's algorithm at a vertex `v` is the least weight of a walk
from the source `src` to `v` (and this least weight is attained). -/
theorem dijkstra_correct (w : V → V → ℝ) (hw : ∀ u v, 0 ≤ w u v) (src v : V) :
    IsLeast {c : ℝ | ∃ l : List V, walkEnd src l = v ∧ walkWt w src l = c}
      (dijkstra w src v) := by
  have hinv := inv_iterate w hw src (Fintype.card V)
  have huniv := settled_univ w src
  constructor
  · obtain ⟨l, _, hend, hwt⟩ := hinv.realize v
    exact ⟨l, hend, hwt⟩
  · rintro c ⟨l, hend, rfl⟩
    exact hinv.settled v (by rw [huniv]; exact Finset.mem_univ v) l hend

end Algorithm

end CS

#print axioms CS.dijkstra_correct

