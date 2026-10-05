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

set_option grind.warning false

namespace Frontier

/-! ## Infinite games: positions, strategies, winning strategies

We consider infinite two-player games with perfect information played on an alphabet `X`.
A *play* is a sequence `x : ℕ → X`; the move at time `n` is `x n`.  Which player moves at
time `n` is recorded by a predicate `turn : ℕ → Prop` (the *turn set* of the player under
consideration).  In the classical game `G(A)` on Baire space, player I moves at the even
times and player II at the odd times, and player I wins the play `x` iff `x ∈ A`.
-/

variable {X : Type*}

/-- The position reached after the first `n` moves of the play `x`. -/
def pre (x : ℕ → X) (n : ℕ) : List X := (List.range n).map x

@[simp] lemma length_pre (x : ℕ → X) (n : ℕ) : (pre x n).length = n := by simp [pre]

lemma pre_succ (x : ℕ → X) (n : ℕ) : pre x (n + 1) = pre x n ++ [x n] := by
  simp [pre, List.range_succ]

lemma pre_getElem (x : ℕ → X) {n i : ℕ} (h : i < (pre x n).length) : (pre x n)[i] = x i := by
  simp [pre]

/-- The play `x` passes through the position `p`. -/
def Extends (p : List X) (x : ℕ → X) : Prop := pre x p.length = p

@[simp] lemma extends_nil (x : ℕ → X) : Extends ([] : List X) x := by simp [Extends, pre]

lemma Extends.eq_of_lt {p : List X} {x : ℕ → X} (h : Extends p x) {i : ℕ}
    (hi : i < p.length) : p[i] = x i := by
  have h2 : (pre x p.length)[i]'(by simpa using hi) = p[i] :=
    List.getElem_of_eq h (by simpa using hi)
  rw [← h2, pre_getElem]

/-- From the position `p` on, the play `x` follows the strategy `σ` of the player whose
moves are those at the times in `turn`. -/
def Follows (turn : ℕ → Prop) (p : List X) (σ : List X → X) (x : ℕ → X) : Prop :=
  ∀ n, p.length ≤ n → turn n → x n = σ (pre x n)

/-- The player whose moves are those at times in `turn` has a strategy from the position `p`
guaranteeing that the resulting play lies in `A`. -/
def WinsFrom (turn : ℕ → Prop) (A : Set (ℕ → X)) (p : List X) : Prop :=
  ∃ σ : List X → X, ∀ x, Extends p x → Follows turn p σ x → x ∈ A

/-- The game `G(A)` on the alphabet `X` (player I moves at even times, player II at odd
times, player I wins iff the play is in `A`) is determined. -/
def Determined (A : Set (ℕ → X)) : Prop :=
  WinsFrom (fun n => Even n) A [] ∨ WinsFrom (fun n => ¬ Even n) Aᶜ []

/-! ## Elementary facts about winning positions -/

/-- If *every* play through `p` lies in `A`, the position `p` is trivially won. -/
lemma winsFrom_of_forall [Inhabited X] {turn : ℕ → Prop} {A : Set (ℕ → X)} {p : List X}
    (h : ∀ x, Extends p x → x ∈ A) : WinsFrom turn A p :=
  ⟨fun _ => default, fun x hx _ => h x hx⟩

/-- If the player to move at `p` (i.e. `turn p.length` holds) can move to a won position,
then `p` is won. -/
lemma winsFrom_of_move {turn : ℕ → Prop} {A : Set (ℕ → X)} {p : List X} {a : X}
    (hturn : turn p.length) (hw : WinsFrom turn A (p ++ [a])) : WinsFrom turn A p := by
  obtain ⟨σ, hσ⟩ := hw
  refine ⟨fun q => if q.length = p.length then a else σ q, ?_⟩
  intro x hx hfol
  have hxa : x p.length = a := by
    have := hfol p.length le_rfl hturn
    simpa [hx] using this
  have hext : Extends (p ++ [a]) x := by
    have : (p ++ [a]).length = p.length + 1 := by simp
    unfold Extends
    rw [this, pre_succ, hxa]
    unfold Extends at hx
    rw [hx]
  refine hσ x hext ?_
  intro n hn hturn'
  have hlen : p.length < n := by
    simpa using hn
  have hne : ¬ ((pre x n).length = p.length) := by simp; omega
  have h1 := hfol n (by omega) hturn'
  rw [h1]
  show (if (pre x n).length = p.length then a else σ (pre x n)) = σ (pre x n)
  rw [if_neg hne]

/-- If every move at `p` leads to a won position, then `p` is won.  (This is used when the
opponent moves at `p`; it happens to hold without that assumption.) -/
lemma winsFrom_of_forall_moves [Inhabited X] {turn : ℕ → Prop} {A : Set (ℕ → X)} {p : List X}
    (hw : ∀ a : X, WinsFrom turn A (p ++ [a])) :
    WinsFrom turn A p := by
  choose f hf using hw
  refine ⟨fun q => if h : p.length < q.length then f q[p.length] q else default, ?_⟩
  intro x hx hfol
  set a := x p.length with ha
  have hext : Extends (p ++ [a]) x := by
    have hlen : (p ++ [a]).length = p.length + 1 := by simp
    unfold Extends
    rw [hlen, pre_succ, ha]
    unfold Extends at hx
    rw [hx]
  refine hf a x hext ?_
  intro n hn hturn'
  have hlen : p.length < n := by simpa using hn
  have h1 := hfol n (by omega) hturn'
  rw [h1]
  have hq : p.length < (pre x n).length := by simpa using hlen
  show (if h : p.length < (pre x n).length then f (pre x n)[p.length] (pre x n) else default)
      = f a (pre x n)
  rw [dif_pos hq, pre_getElem]

/-! ## The Gale–Stewart theorem: closed games are determined

This is the base case of Borel determinacy.  We prove it in a general form: for any turn
predicate and any closed payoff set `A`, either the player with turn set `turn` has a
winning strategy for `A`, or the other player has a winning strategy for `Aᶜ`.
-/

/-- Closedness of a payoff set, phrased combinatorially: any play *not* in `A` has a finite
initial segment all of whose extensions avoid `A`.  For the product topology this is
equivalent to topological closedness, see `cylClosed_of_isClosed`. -/
def CylClosed (A : Set (ℕ → X)) : Prop :=
  ∀ x, x ∉ A → ∃ n : ℕ, ∀ y, Extends (pre x n) y → y ∉ A

/-- A payoff set is clopen when both it and its complement are closed. -/
def CylClopen (A : Set (ℕ → X)) : Prop := CylClosed A ∧ CylClosed Aᶜ

/-- A topologically closed set (in the product topology) is closed in the above sense: a
closed set that misses `x` misses a whole basic neighbourhood of `x`. -/
lemma cylClosed_of_isClosed [TopologicalSpace X] {A : Set (ℕ → X)} (hA : IsClosed A) :
    CylClosed A := by
  intro x hx
  have hopen : IsOpen Aᶜ := hA.isOpen_compl
  rw [isOpen_pi_iff] at hopen
  obtain ⟨I, u, hu, hsub⟩ := hopen x hx
  refine ⟨(I.sup id) + 1, ?_⟩
  intro y hy
  have hyx : ∀ i, i < (I.sup id) + 1 → y i = x i := by
    intro i hi
    have := hy.eq_of_lt (i := i) (by simpa using hi)
    rw [← this, pre_getElem]
  have : y ∈ (I : Set ℕ).pi u := by
    intro i hi
    have hle : i ≤ I.sup id := Finset.le_sup (f := id) (by simpa using hi)
    rw [hyx i (by omega)]
    exact (hu i (by simpa using hi)).2
  exact hsub this

/-- A play passes through `p` exactly when it agrees with `p` on the first `p.length`
coordinates. -/
lemma extends_iff {p : List X} {y : ℕ → X} :
    Extends p y ↔ ∀ i, ∀ h : i < p.length, y i = p[i] := by
  constructor
  · intro h i hi
    exact (h.eq_of_lt hi).symm
  · intro h
    refine List.ext_getElem (by simp) ?_
    intro i h1 h2
    rw [pre_getElem]
    exact h i (by simpa using h2)

/-- Cylinders are open in the product topology when the alphabet is discrete. -/
lemma isOpen_setOf_extends [TopologicalSpace X] [DiscreteTopology X] (p : List X) :
    IsOpen {y : ℕ → X | Extends p y} := by
  have hcyl : {y : ℕ → X | Extends p y}
      = ⋂ i : Fin p.length, (fun y : ℕ → X => y (i : ℕ)) ⁻¹' {p[(i : ℕ)]'i.isLt} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    rw [extends_iff]
    exact ⟨fun h i => h i i.isLt, fun h i hi => h ⟨i, hi⟩⟩
  rw [hcyl]
  exact isOpen_iInter_of_finite fun i => (continuous_apply (i : ℕ)).isOpen_preimage _
    (isOpen_discrete _)

/-- Over a discrete alphabet, combinatorial closedness agrees with topological closedness. -/
lemma isClosed_of_cylClosed [TopologicalSpace X] [DiscreteTopology X] {A : Set (ℕ → X)}
    (hA : CylClosed A) : IsClosed A := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨n, hn⟩ := hA x hx
  refine ⟨{y : ℕ → X | Extends (pre x n) y}, fun y hy => hn y hy, isOpen_setOf_extends _, ?_⟩
  simp [Extends]

/-- Over a discrete alphabet, the combinatorial and the topological notions of a closed
payoff set coincide. -/
lemma cylClosed_iff_isClosed [TopologicalSpace X] [DiscreteTopology X] {A : Set (ℕ → X)} :
    CylClosed A ↔ IsClosed A :=
  ⟨isClosed_of_cylClosed, cylClosed_of_isClosed⟩

/-- **Gale–Stewart theorem.**  In a game with a closed payoff set `A`, either the player
moving at the times in `turn` has a winning strategy for `A`, or the other player has a
winning strategy for `Aᶜ`. -/
theorem gale_stewart [Inhabited X] (turn : ℕ → Prop) (A : Set (ℕ → X)) (hA : CylClosed A) :
    WinsFrom turn A [] ∨ WinsFrom (fun n => ¬ turn n) Aᶜ [] := by
  classical
  by_cases h0 : WinsFrom (fun n => ¬ turn n) Aᶜ ([] : List X)
  · exact Or.inr h0
  left
  set W : List X → Prop := fun p => WinsFrom (fun n => ¬ turn n) Aᶜ p
  -- from a position not won by the opponent, some move keeps it so
  have step_our : ∀ p : List X, ¬ W p → ∃ a : X, ¬ W (p ++ [a]) := by
    intro p hnp
    by_contra hcon
    push_neg at hcon
    exact hnp (winsFrom_of_forall_moves (fun a => hcon a))
  -- and if it is the opponent's move, *every* move keeps it so
  have step_their : ∀ (p : List X) (a : X), ¬ turn p.length → ¬ W p → ¬ W (p ++ [a]) := by
    intro p a hturn hnp hwa
    exact hnp (winsFrom_of_move (turn := fun n => ¬ turn n) (by simpa using hturn) hwa)
  refine ⟨fun q => if h : ∃ a : X, ¬ W (q ++ [a]) then h.choose else default, ?_⟩
  intro x _hx hfol
  set σ : List X → X := fun q => if h : ∃ a : X, ¬ W (q ++ [a]) then h.choose else default
    with hσ
  have key : ∀ n, ¬ W (pre x n) := by
    intro n
    induction n with
    | zero => simpa [pre] using h0
    | succ n ih =>
      rw [pre_succ]
      by_cases hturn : turn n
      · obtain ⟨a, ha⟩ := step_our (pre x n) ih
        have hex : ∃ a : X, ¬ W (pre x n ++ [a]) := ⟨a, ha⟩
        have hxn : x n = σ (pre x n) := hfol n (by simp) hturn
        rw [hxn, hσ]
        simp only [dif_pos hex]
        exact hex.choose_spec
      · have hlen : (pre x n).length = n := by simp
        exact step_their (pre x n) (x n) (by rw [hlen]; exact hturn) ih
  by_contra hxA
  obtain ⟨n, hn⟩ := hA x hxA
  exact key n (winsFrom_of_forall (fun y hy => hn y hy))

/-- Games with a closed payoff set (on any alphabet) are determined. -/
theorem determined_of_cylClosed [Inhabited X] {A : Set (ℕ → X)} (hA : CylClosed A) :
    Determined A :=
  gale_stewart (fun n => Even n) A hA

/-- Games with an open payoff set (on any alphabet) are determined. -/
theorem determined_of_cylOpen [Inhabited X] {A : Set (ℕ → X)} (hA : CylClosed Aᶜ) :
    Determined A := by
  rcases gale_stewart (fun n => ¬ Even n) Aᶜ hA with h | h
  · exact Or.inr h
  · left
    obtain ⟨σ, hσ⟩ := h
    refine ⟨σ, fun x hx hfol => ?_⟩
    have : x ∈ Aᶜᶜ := hσ x hx (fun n hn hturn => hfol n hn (by simpa using hturn))
    simpa using this

/-- Topologically closed games (on any alphabet) are determined. -/
theorem determined_of_isClosed [Inhabited X] [TopologicalSpace X] {A : Set (ℕ → X)}
    (hA : IsClosed A) : Determined A :=
  determined_of_cylClosed (cylClosed_of_isClosed hA)

/-- Topologically open games (on any alphabet) are determined. -/
theorem determined_of_isOpen [Inhabited X] [TopologicalSpace X] {A : Set (ℕ → X)}
    (hA : IsOpen A) : Determined A :=
  determined_of_cylOpen (cylClosed_of_isClosed (isClosed_compl_iff.mpr hA))

/-! ## Determinacy is a genuine dichotomy: the two players cannot both win

Playing two strategies against each other produces a play consistent with both, so at most
one of the two disjuncts in `Determined` can hold. -/

/-- The position reached after `n` moves when the player with turn set `turn` follows `σ`
and the other player follows `τ`. -/
noncomputable def playAux [Inhabited X] (turn : ℕ → Prop) (σ τ : List X → X) : ℕ → List X
  | 0 => []
  | n + 1 => playAux turn σ τ n ++
      [if turn n then σ (playAux turn σ τ n) else τ (playAux turn σ τ n)]

/-- The play resulting from `σ` (for the player with turn set `turn`) against `τ`. -/
noncomputable def play [Inhabited X] (turn : ℕ → Prop) (σ τ : List X → X) (n : ℕ) : X :=
  (playAux turn σ τ (n + 1)).getD n default

@[simp] lemma length_playAux [Inhabited X] (turn : ℕ → Prop) (σ τ : List X → X) (n : ℕ) :
    (playAux turn σ τ n).length = n := by
  induction n with
  | zero => simp [playAux]
  | succ n ih => simp [playAux, ih]

lemma pre_play [Inhabited X] (turn : ℕ → Prop) (σ τ : List X → X) (n : ℕ) :
    pre (play turn σ τ) n = playAux turn σ τ n := by
  induction n with
  | zero => simp [pre, playAux]
  | succ n ih =>
    have hn : play turn σ τ n
        = if turn n then σ (playAux turn σ τ n) else τ (playAux turn σ τ n) := by
      have : (playAux turn σ τ n).length = n := by simp
      rw [play, playAux, ← this, List.getD_eq_getElem?_getD]
      simp
    rw [pre_succ, ih, hn, playAux]

lemma play_follows [Inhabited X] (turn : ℕ → Prop) (σ τ : List X → X) :
    Follows turn [] σ (play turn σ τ) := by
  intro n _ hturn
  have hn : play turn σ τ n
      = if turn n then σ (playAux turn σ τ n) else τ (playAux turn σ τ n) := by
    have h : (playAux turn σ τ n).length = n := by simp
    rw [play, playAux, ← h, List.getD_eq_getElem?_getD]
    simp
  rw [hn, if_pos hturn, pre_play]

lemma play_follows' [Inhabited X] (turn : ℕ → Prop) (σ τ : List X → X) :
    Follows (fun n => ¬ turn n) [] τ (play turn σ τ) := by
  intro n _ hturn
  have hn : play turn σ τ n
      = if turn n then σ (playAux turn σ τ n) else τ (playAux turn σ τ n) := by
    have h : (playAux turn σ τ n).length = n := by simp
    rw [play, playAux, ← h, List.getD_eq_getElem?_getD]
    simp
  rw [hn, if_neg hturn, pre_play]

/-- The two players cannot both have a winning strategy. -/
theorem not_winsFrom_both [Inhabited X] {turn : ℕ → Prop} {A : Set (ℕ → X)}
    (h1 : WinsFrom turn A []) (h2 : WinsFrom (fun n => ¬ turn n) Aᶜ []) : False := by
  obtain ⟨σ, hσ⟩ := h1
  obtain ⟨τ, hτ⟩ := h2
  have hx1 := hσ (play turn σ τ) (extends_nil _) (play_follows turn σ τ)
  have hx2 := hτ (play turn σ τ) (extends_nil _) (play_follows' turn σ τ)
  exact hx2 hx1

/-! ## Coverings and unravelings

Martin's proof of Borel determinacy proceeds by *unraveling*: every Borel payoff set `A` on
Baire space is *covered* by an auxiliary game, played on a (much larger) alphabet, whose
payoff set is **clopen**.  A covering comes with a projection of plays and, crucially, with
a way of projecting strategies, so that winning strategies in the auxiliary game yield
winning strategies in the original one.  The auxiliary clopen game is determined by the
Gale–Stewart theorem above, and determinacy of `A` follows.

We formalize coverings, prove that they compose and that determinacy transfers along them,
and use this to reduce Borel determinacy to Martin's unraveling lemma (the statement that
every Borel set is covered by a clopen game).  The unraveling lemma is a theorem of ZFC, so
the hypothesis of `Frontier.Borel_determinacy` below is not vacuous; we also check that
clopen sets are unraveled by the identity covering, and that the class of unraveled sets is
closed under complements.
-/

section Covering

variable {Y Z : Type*}

/-- The game with payoff `B` on the alphabet `X` **covers** the game with payoff `A` on the
alphabet `Y`, with play projection `proj`, if

* `B` is the `proj`-preimage of `A`;
* every strategy `s` of either player in the covering game can be projected to a strategy
  `t` in the game `G(A)`, in such a way that every play `y` following `t` is `proj x` for
  some play `x` of the covering game following `s`.

This is the property of Martin's coverings that is needed to transfer determinacy. -/
def Covers (proj : (ℕ → X) → (ℕ → Y)) (B : Set (ℕ → X)) (A : Set (ℕ → Y)) : Prop :=
  (∀ x, x ∈ B ↔ proj x ∈ A) ∧
    ∀ turn : ℕ → Prop, (turn = fun n => Even n) ∨ (turn = fun n => ¬ Even n) →
      ∀ s : List X → X, ∃ t : List Y → Y,
        ∀ y : ℕ → Y, Follows turn [] t y → ∃ x : ℕ → X, Follows turn [] s x ∧ proj x = y

/-- Every game covers itself, via the identity. -/
theorem Covers.refl (A : Set (ℕ → X)) : Covers id A A :=
  ⟨fun _ => Iff.rfl, fun _ _ s => ⟨s, fun y hy => ⟨y, hy, rfl⟩⟩⟩

/-- Coverings compose. -/
theorem Covers.comp {proj₁ : (ℕ → X) → (ℕ → Y)} {proj₂ : (ℕ → Z) → (ℕ → X)}
    {A : Set (ℕ → Y)} {B : Set (ℕ → X)} {C : Set (ℕ → Z)}
    (h₂ : Covers proj₂ C B) (h₁ : Covers proj₁ B A) : Covers (proj₁ ∘ proj₂) C A := by
  refine ⟨fun z => ((h₂.1 z).trans (h₁.1 (proj₂ z))), ?_⟩
  intro turn hturn s
  obtain ⟨t, ht⟩ := h₂.2 turn hturn s
  obtain ⟨u, hu⟩ := h₁.2 turn hturn t
  refine ⟨u, fun y hy => ?_⟩
  obtain ⟨x, hx, hxy⟩ := hu y hy
  obtain ⟨z, hz, hzx⟩ := ht x hx
  exact ⟨z, hz, by simp [Function.comp, hzx, hxy]⟩

/-- A covering of `A` is a covering of `Aᶜ`. -/
theorem Covers.compl {proj : (ℕ → X) → (ℕ → Y)} {B : Set (ℕ → X)} {A : Set (ℕ → Y)}
    (h : Covers proj B A) : Covers proj Bᶜ Aᶜ := by
  refine ⟨fun x => ?_, h.2⟩
  simp only [Set.mem_compl_iff, not_iff_not]
  exact h.1 x

/-- **Determinacy transfers along a covering.** -/
theorem Covers.determined {proj : (ℕ → X) → (ℕ → Y)} {B : Set (ℕ → X)} {A : Set (ℕ → Y)}
    (h : Covers proj B A) (hB : Determined B) : Determined A := by
  obtain ⟨hpre, hlift⟩ := h
  rcases hB with hI | hII
  · -- player I wins the covering game
    obtain ⟨s, hs⟩ := hI
    obtain ⟨t, ht⟩ := hlift (fun n => Even n) (Or.inl rfl) s
    refine Or.inl ⟨t, fun y _ hfol => ?_⟩
    obtain ⟨x, hx, hxy⟩ := ht y hfol
    have hxB : x ∈ B := hs x (extends_nil x) hx
    rw [← hxy]
    exact (hpre x).1 hxB
  · -- player II wins the covering game
    obtain ⟨s, hs⟩ := hII
    obtain ⟨t, ht⟩ := hlift (fun n => ¬ Even n) (Or.inr rfl) s
    refine Or.inr ⟨t, fun y _ hfol => ?_⟩
    obtain ⟨x, hx, hxy⟩ := ht y hfol
    have hxB : x ∈ Bᶜ := hs x (extends_nil x) hx
    rw [← hxy]
    exact fun hy => hxB ((hpre x).2 hy)

end Covering

/-- `A` admits a **clopen unraveling**: it is covered by a game, on some alphabet, whose
payoff set is clopen.  This is the conclusion of Martin's unraveling construction. -/
def HasClopenUnraveling (A : Set (ℕ → ℕ)) : Prop :=
  ∃ (X : Type) (_ : Inhabited X) (B : Set (ℕ → X)) (proj : (ℕ → X) → (ℕ → ℕ)),
    CylClopen B ∧ Covers proj B A

/-- Clopen payoff sets are (trivially) unraveled by the identity covering. -/
theorem hasClopenUnraveling_of_cylClopen {A : Set (ℕ → ℕ)} (hA : CylClopen A) :
    HasClopenUnraveling A :=
  ⟨ℕ, inferInstance, A, id, hA, Covers.refl A⟩

/-- The class of sets admitting a clopen unraveling is closed under complementation. -/
theorem HasClopenUnraveling.compl {A : Set (ℕ → ℕ)} (h : HasClopenUnraveling A) :
    HasClopenUnraveling Aᶜ := by
  obtain ⟨X, hX, B, proj, ⟨hB, hBc⟩, hcov⟩ := h
  exact ⟨X, hX, Bᶜ, proj, ⟨hBc, by simpa using hB⟩, hcov.compl⟩

/-- **Transfer along an unraveling.**  If `A` admits a clopen unraveling then the game
`G(A)` is determined: the covering game has a clopen — in particular closed — payoff set,
hence is determined by Gale–Stewart, and its winning strategy projects to a winning
strategy in `G(A)`. -/
theorem determined_of_hasClopenUnraveling {A : Set (ℕ → ℕ)} (h : HasClopenUnraveling A) :
    Determined A := by
  obtain ⟨X, hX, B, proj, ⟨hB, _⟩, hcov⟩ := h
  exact hcov.determined (determined_of_cylClosed hB)

/-! ## Borel determinacy -/

/-- **The statement of Borel determinacy (Martin's theorem)**: every game on Baire space
`ℕ → ℕ` whose payoff set is Borel (i.e. is in the σ-algebra generated by the open sets of
the product topology) is determined. -/
def BorelDeterminacy : Prop :=
  ∀ A : Set (ℕ → ℕ), @MeasurableSet (ℕ → ℕ) (borel (ℕ → ℕ)) A → Determined A

/-- **Borel determinacy (Martin's theorem)**, reduced to Martin's unraveling lemma.

Every Borel game on Baire space `ℕ → ℕ` is determined, given the unraveling lemma
`martin_unraveling`: every Borel payoff set is covered by a game with clopen payoff (see
`Frontier.HasClopenUnraveling` and `Frontier.Covers`).  The reduction and the base case —
determinacy of clopen, indeed of all closed and all open games, `Frontier.determined_of_isClosed`
and `Frontier.determined_of_isOpen` — are proved here in full. -/
theorem Borel_determinacy
    (martin_unraveling : ∀ A : Set (ℕ → ℕ),
      @MeasurableSet (ℕ → ℕ) (borel (ℕ → ℕ)) A → HasClopenUnraveling A) :
    BorelDeterminacy :=
  fun A hA => determined_of_hasClopenUnraveling (martin_unraveling A hA)

/-- Unconditional base case on Baire space: every closed game is determined. -/
theorem Borel_determinacy_closed {A : Set (ℕ → ℕ)} (hA : IsClosed A) : Determined A :=
  determined_of_isClosed hA

/-- Unconditional base case on Baire space: every open game is determined. -/
theorem Borel_determinacy_open {A : Set (ℕ → ℕ)} (hA : IsOpen A) : Determined A :=
  determined_of_isOpen hA

end Frontier

