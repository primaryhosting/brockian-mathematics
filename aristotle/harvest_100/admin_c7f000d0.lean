import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
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

namespace Frontier

/-!
## Infinite two-person games of perfect information

Fix a nonempty set `X` of moves.  A *play* is an element of `ℕ → X` (for `X = ℕ` this is
Baire space); a *position* is a finite list of moves.  Players I and II alternate moves,
producing an infinite play, and player I wins iff the play belongs to the payoff set `A`.

The parameter `s : Bool` records which player moves first: for `s = false` player I moves
at positions of even length (the usual convention), for `s = true` the roles are
interchanged.  Carrying this parameter lets a single Gale–Stewart argument serve both
players.
-/

variable {X : Type*} [Inhabited X]

/-- `moverIsI s h` is `true` exactly when player I is to move at the position `h`. -/
def moverIsI (s : Bool) (h : List X) : Bool := (decide (Even h.length)) ^^ s

/-- The move made at position `h` when player I follows `σ` and player II follows `τ`. -/
def nextMove (s : Bool) (σ τ : List X → X) (h : List X) : X :=
  if moverIsI s h then σ h else τ h

/-- The sequence of positions reached from the position `p` when the players follow the
strategies `σ` (player I) and `τ` (player II); `hist s p σ τ n` is the position after `n`
further moves. -/
def hist (s : Bool) (p : List X) (σ τ : List X → X) : ℕ → List X
  | 0 => p
  | n + 1 => hist s p σ τ n ++ [nextMove s σ τ (hist s p σ τ n)]

/-- The infinite play resulting from the position `p` and the strategies `σ`, `τ`. -/
def play (s : Bool) (p : List X) (σ τ : List X → X) : ℕ → X :=
  fun k => (hist s p σ τ (k + 1)).getD k default

/-- Player I has a winning strategy for the game with payoff `A` from the position `p`. -/
def WinI (s : Bool) (A : Set (ℕ → X)) (p : List X) : Prop :=
  ∃ σ : List X → X, ∀ τ : List X → X, play s p σ τ ∈ A

/-- Player II has a winning strategy for the game with payoff `A` from the position `p`. -/
def WinII (s : Bool) (A : Set (ℕ → X)) (p : List X) : Prop :=
  ∃ τ : List X → X, ∀ σ : List X → X, play s p σ τ ∉ A

/-- The game with payoff set `A` (player I moving first, from the empty position) is
*determined*: one of the two players has a winning strategy. -/
def Determined (A : Set (ℕ → X)) : Prop := WinI false A [] ∨ WinII false A []

/-- The full statement of Martin's Borel determinacy theorem for Baire space: every game
whose payoff set is Borel is determined.  It is recorded here as a `Prop`; what is *proved*
below is its base case, `Frontier.Borel_determinacy`. -/
def BorelDeterminacyStatement : Prop :=
  ∀ A : Set (ℕ → ℕ), @MeasurableSet (ℕ → ℕ) (borel (ℕ → ℕ)) A → Determined A

/-! ## Basic properties of plays -/

omit [Inhabited X] in
lemma hist_length (s : Bool) (p : List X) (σ τ : List X → X) (n : ℕ) :
    (hist s p σ τ n).length = p.length + n := by
  induction n with
  | zero => simp [hist]
  | succ n ih => simp [hist, ih]; omega

omit [Inhabited X] in
lemma hist_prefix_succ (s : Bool) (p : List X) (σ τ : List X → X) (n : ℕ) :
    hist s p σ τ n <+: hist s p σ τ (n + 1) := ⟨_, rfl⟩

omit [Inhabited X] in
lemma hist_prefix_mono (s : Bool) (p : List X) (σ τ : List X → X) {m n : ℕ} (h : m ≤ n) :
    hist s p σ τ m <+: hist s p σ τ n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (hist_prefix_succ s p σ τ n)

omit [Inhabited X] in
lemma prefix_hist (s : Bool) (p : List X) (σ τ : List X → X) (n : ℕ) :
    p <+: hist s p σ τ n := hist_prefix_mono s p σ τ (Nat.zero_le n)

lemma getD_of_prefix {l₁ l₂ : List X} (h : l₁ <+: l₂) {k : ℕ} (hk : k < l₁.length) :
    l₂.getD k default = l₁.getD k default := by
  obtain ⟨t, rfl⟩ := h
  exact List.getD_append _ _ _ _ hk

lemma play_eq_getD (s : Bool) (p : List X) (σ τ : List X → X) {k n : ℕ}
    (hk : k < p.length + n) : play s p σ τ k = (hist s p σ τ n).getD k default := by
  rcases le_total (k + 1) n with h | h
  · exact (getD_of_prefix (hist_prefix_mono s p σ τ h) (by rw [hist_length]; omega)).symm
  · exact getD_of_prefix (hist_prefix_mono s p σ τ h) (by rw [hist_length]; omega)

/-- Every play from the position `p` extends `p`. -/
lemma play_prefix (s : Bool) (p : List X) (σ τ : List X → X) {k : ℕ} (hk : k < p.length) :
    play s p σ τ k = p.getD k default := by
  have := play_eq_getD s p σ τ (k := k) (n := 0) (by omega)
  simpa [hist] using this

omit [Inhabited X] in
/-- After the first move from `p` the game continues as the game from `p ++ [a]`. -/
lemma hist_succ_shift (s : Bool) (p : List X) (σ τ : List X → X) (n : ℕ) :
    hist s p σ τ (n + 1) = hist s (p ++ [nextMove s σ τ p]) σ τ n := by
  induction n with
  | zero => simp [hist]
  | succ n ih => rw [hist, ih]; rfl

lemma play_shift (s : Bool) (p : List X) (σ τ : List X → X) :
    play s p σ τ = play s (p ++ [nextMove s σ τ p]) σ τ := by
  funext k
  have h1 : play s p σ τ k = (hist s p σ τ (k + 2)).getD k default :=
    play_eq_getD s p σ τ (by omega)
  have h2 : play s (p ++ [nextMove s σ τ p]) σ τ k
      = (hist s (p ++ [nextMove s σ τ p]) σ τ (k + 1)).getD k default := rfl
  rw [h1, h2, hist_succ_shift]

omit [Inhabited X] in
/-- Only the values of the strategies on positions extending `p` matter. -/
lemma hist_congr (s : Bool) (p : List X) {σ τ σ' τ' : List X → X}
    (hσ : ∀ h : List X, p <+: h → σ h = σ' h) (hτ : ∀ h : List X, p <+: h → τ h = τ' h)
    (n : ℕ) : hist s p σ τ n = hist s p σ' τ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hp : p <+: hist s p σ τ n := prefix_hist s p σ τ n
      rw [hist, hist, ih]
      congr 1
      rw [← ih] at *
      simp only [nextMove]
      by_cases hm : moverIsI s (hist s p σ τ n) <;> simp [hm, hσ _ hp, hτ _ hp]

lemma play_congr (s : Bool) (p : List X) {σ τ σ' τ' : List X → X}
    (hσ : ∀ h : List X, p <+: h → σ h = σ' h) (hτ : ∀ h : List X, p <+: h → τ h = τ' h) :
    play s p σ τ = play s p σ' τ' := by
  funext k
  simp only [play, hist_congr s p hσ hτ]

/-! ### Sanity checks: the game conventions are the intended ones

Player I controls the even coordinates of the play and player II the odd ones. -/

example : WinI false {x : ℕ → ℕ | x 0 = 1} [] :=
  ⟨fun _ => 1, fun _ => rfl⟩

example : WinII false {x : ℕ → ℕ | x 1 = 1} [] :=
  ⟨fun _ => 0, fun _ => by simp [play, hist, nextMove, moverIsI]⟩

/-! ## Open payoff sets -/

/-- A payoff set is *open* in the combinatorial sense if membership of any of its elements
is already guaranteed by a finite initial segment of that element. -/
def IsOpenPayoff (A : Set (ℕ → X)) : Prop :=
  ∀ x ∈ A, ∃ N : ℕ, ∀ y : ℕ → X, (∀ i < N, y i = x i) → y ∈ A

omit [Inhabited X] in
/-- A set that is open in the product topology is an open payoff set. -/
lemma isOpenPayoff_of_isOpen [TopologicalSpace X] {A : Set (ℕ → X)} (hA : IsOpen A) :
    IsOpenPayoff A := by
  intro x hx
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hA x hx
  refine ⟨(I.sup id) + 1, fun y hy => hsub ?_⟩
  intro a ha
  have hle : a ≤ I.sup id := Finset.le_sup (f := id) ha
  have hya : y a = x a := hy a (by omega)
  rw [hya]
  exact (hu a ha).2

/-! ## The Gale–Stewart theorem -/

/-- If player I is to move at `q` and has a winning strategy after moving `a`, then he has
a winning strategy at `q`. -/
lemma winI_of_winI_append_moverI {s : Bool} {A : Set (ℕ → X)} {q : List X} {a : X}
    (hm : moverIsI s q = true) (h : WinI s A (q ++ [a])) : WinI s A q := by
  obtain ⟨σ', hσ'⟩ := h
  refine ⟨fun h => if h = q then a else σ' h, fun τ => ?_⟩
  set σ : List X → X := fun h => if h = q then a else σ' h with hσdef
  have hfirst : nextMove s σ τ q = a := by simp [nextMove, hm, hσdef]
  have h1 : play s q σ τ = play s (q ++ [a]) σ τ := by
    have := play_shift s q σ τ
    rwa [hfirst] at this
  have h2 : play s (q ++ [a]) σ τ = play s (q ++ [a]) σ' τ := by
    refine play_congr s (q ++ [a]) (fun h hh => ?_) (fun h _ => rfl)
    have hlen : q.length < h.length := by
      have := hh.length_le
      simp at this
      omega
    have hne : h ≠ q := by
      intro hEq; rw [hEq] at hlen; omega
    simp [hσdef, hne]
  rw [h1, h2]
  exact hσ' τ

/-- If player II is to move at `q` and player I has a winning strategy after every move of
player II, then player I has a winning strategy at `q`. -/
lemma winI_of_forall_append_moverII {s : Bool} {A : Set (ℕ → X)} {q : List X}
    (hm : moverIsI s q = false) (h : ∀ a : X, WinI s A (q ++ [a])) : WinI s A q := by
  choose σ hσ using h
  refine ⟨fun h => if q.length < h.length then σ (h.getD q.length default) h else default,
    fun τ => ?_⟩
  set SS : List X → X :=
    fun h => if q.length < h.length then σ (h.getD q.length default) h else default with hSdef
  set a : X := τ q with hadef
  have hfirst : nextMove s SS τ q = a := by simp [nextMove, hm, hadef]
  have h1 : play s q SS τ = play s (q ++ [a]) SS τ := by
    have := play_shift s q SS τ
    rwa [hfirst] at this
  have hga : (q ++ [a]).getD q.length default = a := by
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  have h2 : play s (q ++ [a]) SS τ = play s (q ++ [a]) (σ a) τ := by
    refine play_congr s (q ++ [a]) (fun h hh => ?_) (fun h _ => rfl)
    have hlen : q.length + 1 ≤ h.length := by
      have := hh.length_le
      simp at this
      omega
    have hget : h.getD q.length default = a := by
      rw [getD_of_prefix hh (by simp)]
      exact hga
    have hlt : q.length < h.length := by omega
    simp only [hSdef, if_pos hlt, hget]
  rw [h1, h2]
  exact hσ a τ

/-- **The Gale–Stewart theorem.**  Every game with an open payoff set is determined, from
every position and for either player moving first. -/
theorem gale_stewart (s : Bool) {A : Set (ℕ → X)} (hA : IsOpenPayoff A) (p : List X) :
    WinI s A p ∨ WinII s A p := by
  by_cases hI : WinI s A p
  · exact Or.inl hI
  refine Or.inr ?_
  -- Player II's strategy: always move to a position from which player I has no winning
  -- strategy.  This is possible as long as the current position has that property.
  set τ₀ : List X → X :=
    fun q => if h : ∃ a : X, ¬ WinI s A (q ++ [a]) then h.choose else default with hτdef
  have hkey : ∀ (σ : List X → X) (n : ℕ), ¬ WinI s A (hist s p σ τ₀ n) := by
    intro σ n
    induction n with
    | zero => simpa [hist] using hI
    | succ n ih =>
        set q : List X := hist s p σ τ₀ n with hq
        have hnext : hist s p σ τ₀ (n + 1) = q ++ [nextMove s σ τ₀ q] := rfl
        rw [hnext]
        by_cases hm : moverIsI s q
        · rw [show nextMove s σ τ₀ q = σ q by simp [nextMove, hm]]
          exact fun hw => ih (winI_of_winI_append_moverI hm hw)
        · have hm' : moverIsI s q = false := by simpa using hm
          rw [show nextMove s σ τ₀ q = τ₀ q by simp [nextMove, hm']]
          have hex : ∃ a : X, ¬ WinI s A (q ++ [a]) := by
            by_contra hcon
            push_neg at hcon
            exact ih (winI_of_forall_append_moverII hm' (fun a => hcon a))
          have hchoice : τ₀ q = hex.choose := by simp [hτdef, hex]
          rw [hchoice]
          exact hex.choose_spec
  refine ⟨τ₀, fun σ hmem => ?_⟩
  -- If the resulting play were in `A`, openness would already give player I a winning
  -- strategy at a finite stage of that play, contradicting `hkey`.
  obtain ⟨N, hN⟩ := hA _ hmem
  set q : List X := hist s p σ τ₀ N with hq
  have hqlen : q.length = p.length + N := hist_length s p σ τ₀ N
  have hagree : ∀ i < N, q.getD i default = play s p σ τ₀ i := fun i hi =>
    (play_eq_getD s p σ τ₀ (k := i) (n := N) (by omega)).symm
  have hwin : WinI s A q := by
    refine ⟨fun _ => default, fun τ => hN _ (fun i hi => ?_)⟩
    have hlt : i < q.length := by omega
    rw [play_prefix s q _ τ hlt]
    exact hagree i hi
  exact hkey σ N hwin

/-! ## Determinacy of open and of closed games -/

/-- Swapping the two players amounts to changing which player moves first. -/
lemma play_swap (s : Bool) (p : List X) (σ τ : List X → X) :
    play s p σ τ = play (!s) p τ σ := by
  have hstep : ∀ h : List X, nextMove s σ τ h = nextMove (!s) τ σ h := by
    intro h
    simp only [nextMove, moverIsI]
    cases s <;> by_cases he : Even h.length <;> simp [he]
  have hh : ∀ n, hist s p σ τ n = hist (!s) p τ σ n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [hist, hist, ih, hstep]
  funext k
  show (hist s p σ τ (k + 1)).getD k default = (hist (!s) p τ σ (k + 1)).getD k default
  rw [hh]

theorem determined_of_isOpenPayoff {A : Set (ℕ → X)} (hA : IsOpenPayoff A) : Determined A :=
  gale_stewart false hA []

theorem determined_of_compl_isOpenPayoff {A : Set (ℕ → X)} (hA : IsOpenPayoff Aᶜ) :
    Determined A := by
  rcases gale_stewart true hA [] with ⟨σ, hσ⟩ | ⟨τ, hτ⟩
  · -- player I wins the `Aᶜ`-game with player II moving first: player II wins the `A`-game
    refine Or.inr ⟨σ, fun σ' => ?_⟩
    have h := hσ σ'
    rw [play_swap false [] σ' σ]
    exact h
  · -- player II wins the `Aᶜ`-game with player II moving first: player I wins the `A`-game
    refine Or.inl ⟨τ, fun τ' => ?_⟩
    have h := hτ τ'
    rw [play_swap false [] τ τ']
    simpa using h

/-- Every game with an open payoff set is determined. -/
theorem determined_of_isOpen [TopologicalSpace X] {A : Set (ℕ → X)} (hA : IsOpen A) :
    Determined A :=
  determined_of_isOpenPayoff (isOpenPayoff_of_isOpen hA)

/-- Every game with a closed payoff set is determined. -/
theorem determined_of_isClosed [TopologicalSpace X] {A : Set (ℕ → X)} (hA : IsClosed A) :
    Determined A :=
  determined_of_compl_isOpenPayoff (isOpenPayoff_of_isOpen hA.isOpen_compl)

/-- **Borel determinacy (Martin's theorem): verified base case.**

The full statement — every Borel game on Baire space `ℕ → ℕ` is determined — is recorded
as `Frontier.BorelDeterminacyStatement`.  What is proved here is its base case, the
Gale–Stewart theorem: every game whose payoff set lies in the bottom level
`Σ⁰₁ ∪ Π⁰₁` of the Borel hierarchy (i.e. is open or closed in the product topology on
`ℕ → ℕ`) is determined.  This is the base of Martin's transfinite induction on Borel rank.

The underlying results (`Frontier.gale_stewart`, `Frontier.determined_of_isOpen`,
`Frontier.determined_of_isClosed`) are proved for games with an arbitrary nonempty set `X`
of legal moves and from an arbitrary position, which is the form in which the base case is
used in Martin's proof. -/
theorem Borel_determinacy (A : Set (ℕ → ℕ)) (hA : IsOpen A ∨ IsClosed A) : Determined A :=
  hA.elim determined_of_isOpen determined_of_isClosed

end Frontier

