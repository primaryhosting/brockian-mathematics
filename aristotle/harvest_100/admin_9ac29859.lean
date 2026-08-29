import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Frontier

/-! ## Games on a set of moves

A play of the game is an infinite sequence `x : ℕ → A` of moves.  Player I plays the
moves `x 0, x 2, x 4, …` and player II plays the moves `x 1, x 3, x 5, …`.  Player I
wins the play `x` iff `x` belongs to the payoff set `S`.
-/

universe u

variable {A : Type u}

/-- The position (list of moves played) after the first `n` moves of the play `x`. -/
def pref (x : ℕ → A) : ℕ → List A
  | 0 => []
  | n + 1 => pref x n ++ [x n]

/-- A play `x` follows the strategy `σ` of player I. -/
def FollowsI (σ : List A → A) (x : ℕ → A) : Prop := ∀ n, Even n → x n = σ (pref x n)

/-- A play `x` follows the strategy `τ` of player II. -/
def FollowsII (τ : List A → A) (x : ℕ → A) : Prop := ∀ n, Odd n → x n = τ (pref x n)

/-- `σ` is a winning strategy for player I in the game with payoff set `S`. -/
def WinI (S : Set (ℕ → A)) (σ : List A → A) : Prop := ∀ x, FollowsI σ x → x ∈ S

/-- `τ` is a winning strategy for player II in the game with payoff set `S`. -/
def WinII (S : Set (ℕ → A)) (τ : List A → A) : Prop := ∀ x, FollowsII τ x → x ∉ S

/-- The game with payoff set `S` is determined. -/
def Det (S : Set (ℕ → A)) : Prop := (∃ σ, WinI S σ) ∨ (∃ τ, WinII S τ)

/-! ## Prefix-closedness and prefix-openness

For the product topology on `ℕ → A` with `A` discrete these are exactly closedness and
openness; this is proved below (`seqClosed_iff_isClosed`, `seqOpen_iff_isOpen`). -/

/-- `S` is closed: any sequence all of whose finite positions can be extended into `S`
lies in `S`. -/
def SeqClosed (S : Set (ℕ → A)) : Prop :=
  ∀ x, (∀ n, ∃ y ∈ S, pref y n = pref x n) → x ∈ S

/-- `S` is open: membership of `S` is witnessed by a finite position. -/
def SeqOpen (S : Set (ℕ → A)) : Prop :=
  ∀ x ∈ S, ∃ n, ∀ y, pref y n = pref x n → y ∈ S

/-! ## Basic facts about `pref` -/

@[simp] theorem pref_length (x : ℕ → A) (n : ℕ) : (pref x n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pref, ih]

theorem pref_getD (x : ℕ → A) {i n : ℕ} (h : i < n) (d : A) :
    (pref x n).getD i d = x i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 h) with h' | h'
    · rw [pref, List.getD_append _ _ _ _ (by simpa using h')]
      exact ih h'
    · subst h'
      rw [pref, List.getD_append_right _ _ _ _ (by simp)]
      simp

theorem pref_succ (x : ℕ → A) (n : ℕ) : pref x (n + 1) = pref x n ++ [x n] := rfl

/-! ## Relativised games (games starting from a position) -/

/-- `τ` is a winning strategy for player II in the game with payoff `S` played from the
position `p` onwards. -/
def WinIIfrom (S : Set (ℕ → A)) (p : List A) (τ : List A → A) : Prop :=
  ∀ x, pref x p.length = p → (∀ n, p.length ≤ n → Odd n → x n = τ (pref x n)) → x ∉ S

/-- Player II wins the game with payoff `S` from the position `p`. -/
def IIwins (S : Set (ℕ → A)) (p : List A) : Prop := ∃ τ, WinIIfrom S p τ

/-- Positions from which player II has no winning strategy. -/
def Good (S : Set (ℕ → A)) (p : List A) : Prop := ¬ IIwins S p

theorem good_nil_iff (S : Set (ℕ → A)) : Good S [] ↔ ¬ ∃ τ, WinII S τ := by
  unfold Good IIwins WinIIfrom WinII FollowsII
  simp [pref]

/-- If player II wins from every one-move extension of `p`, then player II wins from `p`
(this needs no assumption on whose turn it is).  Contrapositively: from a good position
there is always a move to a good position. -/
theorem exists_good_move [Nonempty A] {S : Set (ℕ → A)} {p : List A}
    (hp : Good S p) : ∃ a, Good S (p ++ [a]) := by
  by_contra hcon
  push_neg at hcon
  simp only [Good, not_not] at hcon
  choose τ' hτ' using hcon
  refine hp ⟨fun p' => τ' (p'.getD p.length (Classical.arbitrary A)) p', ?_⟩
  intro x hx hf
  set a : A := x p.length with ha
  have hext : pref x (p ++ [a]).length = p ++ [a] := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [pref_succ, hx]
  refine hτ' a x hext ?_
  intro n hn hodd
  have hn' : p.length < n := by simpa [List.length_append] using hn
  have := hf n (le_of_lt hn') hodd
  rw [this]
  simp only [pref_getD x hn', ha]

/-- From a good position where player II is to move, every move leads to a good
position. -/
theorem good_of_move {S : Set (ℕ → A)} {p : List A}
    (hp : Good S p) (hodd : Odd p.length) (a : A) : Good S (p ++ [a]) := by
  intro ⟨τ', hτ'⟩
  refine hp ⟨fun p' => if p'.length = p.length then a else τ' p', ?_⟩
  intro x hx hf
  have hmove : x p.length = a := by
    have := hf p.length le_rfl hodd
    simpa [hx] using this
  have hext : pref x (p ++ [a]).length = p ++ [a] := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [pref_succ, hx, hmove]
  refine hτ' x hext ?_
  intro n hn hodd'
  have hn' : p.length < n := by simpa [List.length_append] using hn
  have := hf n (le_of_lt hn') hodd'
  rw [this]
  simp only [pref_length]
  rw [if_neg (by omega)]

/-- A position from which no extension lies in `S` is won by player II. -/
theorem iiwins_of_no_extension [Nonempty A] {S : Set (ℕ → A)} {p : List A}
    (h : ∀ y, pref y p.length = p → y ∉ S) : IIwins S p :=
  ⟨fun _ => Classical.arbitrary A, fun x hx _ => h x hx⟩

/-! ## The Gale–Stewart theorem: closed games are determined -/

theorem seqClosed_determinacy [Nonempty A] (S : Set (ℕ → A)) (hS : SeqClosed S) : Det S := by
  by_cases h : ∃ τ, WinII S τ
  · exact Or.inr h
  refine Or.inl ?_
  have hnil : Good S [] := (good_nil_iff S).2 h
  have key : ∀ p : List A, Good S p → ∃ a, Good S (p ++ [a]) := fun _ hp => exists_good_move hp
  choose! σ hσ using key
  refine ⟨σ, ?_⟩
  intro x hfol
  have hgood : ∀ n, Good S (pref x n) := by
    intro n
    induction n with
    | zero => exact hnil
    | succ n ih =>
      rw [pref_succ]
      rcases Nat.even_or_odd n with he | ho
      · rw [hfol n he]
        exact hσ _ ih
      · exact good_of_move ih (by simpa using ho) (x n)
  refine hS x ?_
  intro n
  by_contra hcon
  push_neg at hcon
  refine hgood n (iiwins_of_no_extension ?_)
  intro y hy
  exact fun hyS => hcon y hyS (by simpa using hy)

/-! ### The dual argument: open games are determined -/

/-- `σ` is a winning strategy for player I in the game with payoff `S` played from the
position `p` onwards. -/
def WinIfrom (S : Set (ℕ → A)) (p : List A) (σ : List A → A) : Prop :=
  ∀ x, pref x p.length = p → (∀ n, p.length ≤ n → Even n → x n = σ (pref x n)) → x ∈ S

/-- Player I wins the game with payoff `S` from the position `p`. -/
def Iwins (S : Set (ℕ → A)) (p : List A) : Prop := ∃ σ, WinIfrom S p σ

/-- Positions from which player I has no winning strategy. -/
def Coop (S : Set (ℕ → A)) (p : List A) : Prop := ¬ Iwins S p

theorem coop_nil_iff (S : Set (ℕ → A)) : Coop S [] ↔ ¬ ∃ σ, WinI S σ := by
  unfold Coop Iwins WinIfrom WinI FollowsI
  simp [pref]

/-- If player I wins from every one-move extension of `p`, then player I wins from `p`. -/
theorem exists_coop_move [Nonempty A] {S : Set (ℕ → A)} {p : List A}
    (hp : Coop S p) : ∃ a, Coop S (p ++ [a]) := by
  by_contra hcon
  push_neg at hcon
  simp only [Coop, not_not] at hcon
  choose σ' hσ' using hcon
  refine hp ⟨fun p' => σ' (p'.getD p.length (Classical.arbitrary A)) p', ?_⟩
  intro x hx hf
  set a : A := x p.length with ha
  have hext : pref x (p ++ [a]).length = p ++ [a] := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [pref_succ, hx]
  refine hσ' a x hext ?_
  intro n hn hev
  have hn' : p.length < n := by simpa [List.length_append] using hn
  have := hf n (le_of_lt hn') hev
  rw [this]
  simp only [pref_getD x hn', ha]

/-- From a position where player I has no winning strategy and player I is to move,
every move again leads to such a position. -/
theorem coop_of_move {S : Set (ℕ → A)} {p : List A}
    (hp : Coop S p) (hev : Even p.length) (a : A) : Coop S (p ++ [a]) := by
  intro ⟨σ', hσ'⟩
  refine hp ⟨fun p' => if p'.length = p.length then a else σ' p', ?_⟩
  intro x hx hf
  have hmove : x p.length = a := by
    have := hf p.length le_rfl hev
    simpa [hx] using this
  have hext : pref x (p ++ [a]).length = p ++ [a] := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [pref_succ, hx, hmove]
  refine hσ' x hext ?_
  intro n hn hev'
  have hn' : p.length < n := by simpa [List.length_append] using hn
  have := hf n (le_of_lt hn') hev'
  rw [this]
  simp only [pref_length]
  rw [if_neg (by omega)]

/-- A position all of whose extensions lie in `S` is won by player I. -/
theorem iwins_of_all_extension [Nonempty A] {S : Set (ℕ → A)} {p : List A}
    (h : ∀ y, pref y p.length = p → y ∈ S) : Iwins S p :=
  ⟨fun _ => Classical.arbitrary A, fun x hx _ => h x hx⟩

/-- Open games are determined. -/
theorem seqOpen_determinacy [Nonempty A] (S : Set (ℕ → A)) (hS : SeqOpen S) : Det S := by
  by_cases h : ∃ σ, WinI S σ
  · exact Or.inl h
  refine Or.inr ?_
  have hnil : Coop S [] := (coop_nil_iff S).2 h
  have key : ∀ p : List A, Coop S p → ∃ a, Coop S (p ++ [a]) := fun _ hp => exists_coop_move hp
  choose! τ hτ using key
  refine ⟨τ, ?_⟩
  intro x hfol
  have hcoop : ∀ n, Coop S (pref x n) := by
    intro n
    induction n with
    | zero => exact hnil
    | succ n ih =>
      rw [pref_succ]
      rcases Nat.even_or_odd n with he | ho
      · exact coop_of_move ih (by simpa using he) (x n)
      · rw [hfol n ho]
        exact hτ _ ih
  intro hxS
  obtain ⟨n, hn⟩ := hS x hxS
  refine hcoop n (iwins_of_all_extension ?_)
  intro y hy
  exact hn y (by simpa using hy)

/-! ## Comparison with the topological notions -/

theorem pref_eq_iff (x y : ℕ → A) (n : ℕ) : pref y n = pref x n ↔ ∀ i < n, y i = x i := by
  constructor
  · intro h i hi
    rcases isEmpty_or_nonempty A with hA | hA
    · exact (IsEmpty.false (x i)).elim
    · have h2 := congrArg (fun l => l.getD i (Classical.arbitrary A)) h
      dsimp only at h2
      rwa [pref_getD _ hi, pref_getD _ hi] at h2
  · intro h
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pref_succ, pref_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- The basic open sets of the product topology: plays with a prescribed initial
position. -/
theorem isOpen_prefixSet [TopologicalSpace A] [DiscreteTopology A] (x : ℕ → A) (n : ℕ) :
    IsOpen {y : ℕ → A | pref y n = pref x n} := by
  have : {y : ℕ → A | pref y n = pref x n}
      = ⋂ i ∈ Finset.range n, (fun y : ℕ → A => y i) ⁻¹' {x i} := by
    ext y
    simp [pref_eq_iff]
  rw [this]
  refine isOpen_biInter_finset ?_
  intro i _
  exact (continuous_apply i).isOpen_preimage _ (isOpen_discrete _)

/-- Membership in an open set is determined by a finite initial position. -/
theorem exists_prefix_subset [TopologicalSpace A] [DiscreteTopology A] {U : Set (ℕ → A)}
    (hU : IsOpen U) {x : ℕ → A} (hx : x ∈ U) : ∃ n, ∀ y, pref y n = pref x n → y ∈ U := by
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hU x hx
  refine ⟨I.sup id + 1, fun y hy => hsub ?_⟩
  intro i hi
  have hlt : i < I.sup id + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  have : y i = x i := (pref_eq_iff x y _).1 hy i hlt
  rw [this]
  exact (hu i hi).2

theorem seqClosed_iff_isClosed [TopologicalSpace A] [DiscreteTopology A] (S : Set (ℕ → A)) :
    SeqClosed S ↔ IsClosed S := by
  constructor
  · intro h
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    have hne : ¬ ∀ n, ∃ y ∈ S, pref y n = pref x n := fun hall => hx (h x hall)
    push_neg at hne
    obtain ⟨n, hn⟩ := hne
    exact ⟨{y | pref y n = pref x n}, fun y hy hyS => hn y hyS hy, isOpen_prefixSet x n, rfl⟩
  · intro hS x hx
    by_contra hxS
    obtain ⟨n, hn⟩ := exists_prefix_subset hS.isOpen_compl hxS
    obtain ⟨y, hyS, hy⟩ := hx n
    exact hn y hy hyS

theorem seqOpen_iff_isOpen [TopologicalSpace A] [DiscreteTopology A] (S : Set (ℕ → A)) :
    SeqOpen S ↔ IsOpen S := by
  constructor
  · intro h
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨n, hn⟩ := h x hx
    exact ⟨{y | pref y n = pref x n}, hn, isOpen_prefixSet x n, rfl⟩
  · intro hS x hx
    exact exists_prefix_subset hS hx

/-- **Gale–Stewart theorem**: every closed game is determined.  (Here `ℕ → A` carries the
product of the discrete topology on the set `A` of moves.) -/
theorem isClosed_determinacy [TopologicalSpace A] [DiscreteTopology A] [Nonempty A]
    (S : Set (ℕ → A)) (hS : IsClosed S) : Det S :=
  seqClosed_determinacy S ((seqClosed_iff_isClosed S).2 hS)

/-- **Gale–Stewart theorem**, open version: every open game is determined. -/
theorem isOpen_determinacy [TopologicalSpace A] [DiscreteTopology A] [Nonempty A]
    (S : Set (ℕ → A)) (hS : IsOpen S) : Det S :=
  seqOpen_determinacy S ((seqOpen_iff_isOpen S).2 hS)

/-! ## Coverings and unravelings (Martin) -/

/-- A *covering* of the game with moves in `A` by a game with moves in `B`: an
alphabet `B`, a length-preserving monotone map on positions inducing a map `π` on
plays, together with maps lifting strategies in the `B`-game to strategies in the
`A`-game so that every play following the lifted strategy is the image of a play
following the original one. -/
structure Covering (A : Type*) (B : Type*) where
  /-- the map on positions -/
  pmap : List B → List A
  pmap_length : ∀ q, (pmap q).length = q.length
  pmap_mono : ∀ q b, pmap q <+: pmap (q ++ [b])
  /-- the induced map on plays -/
  π : (ℕ → B) → (ℕ → A)
  π_spec : ∀ y n, pref (π y) n = pmap (pref y n)
  /-- lifting of strategies of player I -/
  liftI : (List B → B) → (List A → A)
  /-- lifting of strategies of player II -/
  liftII : (List B → B) → (List A → A)
  liftI_spec : ∀ σ x, FollowsI (liftI σ) x → ∃ y, FollowsI σ y ∧ π y = x
  liftII_spec : ∀ τ x, FollowsII (liftII τ) x → ∃ y, FollowsII τ y ∧ π y = x

/-- `S` is *unravelled* by a covering: there is a covering of the game by a game in
which the payoff set becomes clopen. -/
def Unravels (S : Set (ℕ → A)) : Prop :=
  ∃ (B : Type u) (_ : Nonempty B) (c : Covering A B),
    SeqClosed (c.π ⁻¹' S) ∧ SeqOpen (c.π ⁻¹' S)

/-- The trivial (identity) covering: in particular the notion of covering used above is
not vacuous, and every clopen set is (trivially) unravelled. -/
def idCovering (A : Type u) : Covering A A where
  pmap := id
  pmap_length := fun _ => rfl
  pmap_mono := fun _ b => ⟨[b], rfl⟩
  π := id
  π_spec := fun _ _ => rfl
  liftI := id
  liftII := id
  liftI_spec := fun _ x hx => ⟨x, hx, rfl⟩
  liftII_spec := fun _ x hx => ⟨x, hx, rfl⟩

theorem unravels_of_clopen [Nonempty A] {S : Set (ℕ → A)} (hc : SeqClosed S) (ho : SeqOpen S) :
    Unravels S :=
  ⟨A, inferInstance, idCovering A, hc, ho⟩

/-- A game whose payoff set is unravelled to a clopen set is determined. -/
theorem det_of_unravels [Nonempty A] {S : Set (ℕ → A)} (h : Unravels S) : Det S := by
  obtain ⟨B, hB, c, hclosed, -⟩ := h
  rcases seqClosed_determinacy (c.π ⁻¹' S) hclosed with ⟨σ, hσ⟩ | ⟨τ, hτ⟩
  · refine Or.inl ⟨c.liftI σ, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := c.liftI_spec σ x hx
    exact hσ y hy
  · refine Or.inr ⟨c.liftII τ, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := c.liftII_spec τ x hx
    exact hτ y hy

/-- A subset of the space of plays is Borel, i.e. lies in the σ-algebra generated by the
open sets of the product topology. -/
def IsBorel [TopologicalSpace A] (S : Set (ℕ → A)) : Prop :=
  @MeasurableSet (ℕ → A) (borel (ℕ → A)) S

/-- **Borel determinacy** (Martin's theorem), reduced to Martin's unraveling lemma:
if every Borel payoff set can be unravelled to a clopen set by a covering of the game,
then every Borel game is determined.  The reduction goes through the Gale–Stewart
theorem `isClosed_determinacy`, which is proved outright above. -/
theorem Borel_determinacy [TopologicalSpace A] [DiscreteTopology A] [Nonempty A]
    (hUnravel : ∀ S : Set (ℕ → A), IsBorel S → Unravels S)
    (S : Set (ℕ → A)) (hS : IsBorel S) : Det S :=
  det_of_unravels (hUnravel S hS)

end Frontier

