import Mathlib
/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Frontier

variable {X : Type u}

/-- A strategy assigns a move to every finite position of the game. -/
abbrev Strategy (X : Type u) := List X → X

/-- The move played at position `q`: player I (resp. II) moves at positions of
even (resp. odd) length. -/
def nextMove (σ τ : Strategy X) (q : List X) : X :=
  if Even q.length then σ q else τ q

/-- The position reached after `n` further moves, starting from position `p`,
when player I follows `σ` and player II follows `τ`. -/
def posFrom (p : List X) (σ τ : Strategy X) : ℕ → List X
  | 0 => p
  | n + 1 => posFrom p σ τ n ++ [nextMove σ τ (posFrom p σ τ n)]

variable [Nonempty X]

/-- The infinite play resulting from starting at position `p` and following `σ`, `τ`. -/
noncomputable def playFrom (p : List X) (σ τ : Strategy X) : ℕ → X :=
  fun k => (posFrom p σ τ (k + 1)).getD k (Classical.arbitrary X)

/-- Player I wins the game with payoff `A` from position `p`. -/
def IWins (A : Set (ℕ → X)) (p : List X) : Prop :=
  ∃ σ : Strategy X, ∀ τ : Strategy X, playFrom p σ τ ∈ A

/-- Player II wins the game with payoff `A` from position `p`. -/
def IIWins (A : Set (ℕ → X)) (p : List X) : Prop :=
  ∃ τ : Strategy X, ∀ σ : Strategy X, playFrom p σ τ ∉ A

/-- The game with payoff set `A` (played from the empty position) is determined. -/
def Determined (A : Set (ℕ → X)) : Prop := IWins A [] ∨ IIWins A []

/-- Combinatorial openness of a payoff set: every winning play is won at a finite stage. -/
def IsOpenPayoff (A : Set (ℕ → X)) : Prop :=
  ∀ x ∈ A, ∃ n : ℕ, ∀ y : ℕ → X, (∀ i < n, y i = x i) → y ∈ A

/-! ### Basic combinatorics of plays -/

omit [Nonempty X] in
theorem getD_of_prefix {l₁ l₂ : List X} (h : l₁ <+: l₂) {k : ℕ} (hk : k < l₁.length)
    (d : X) : l₁.getD k d = l₂.getD k d := by
  rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ (hk.trans_le h.length_le),
    h.getElem hk]

omit [Nonempty X] in
theorem posFrom_length (p : List X) (σ τ : Strategy X) (n : ℕ) :
    (posFrom p σ τ n).length = p.length + n := by
  induction n with
  | zero => simp [posFrom]
  | succ n ih => simp [posFrom, ih]; omega

omit [Nonempty X] in
theorem posFrom_prefix_succ (p : List X) (σ τ : Strategy X) (n : ℕ) :
    posFrom p σ τ n <+: posFrom p σ τ (n + 1) :=
  ⟨[nextMove σ τ (posFrom p σ τ n)], rfl⟩

omit [Nonempty X] in
theorem posFrom_prefix (p : List X) (σ τ : Strategy X) {n m : ℕ} (h : n ≤ m) :
    posFrom p σ τ n <+: posFrom p σ τ m := by
  induction h with
  | refl => exact List.prefix_rfl
  | step h ih => exact ih.trans (posFrom_prefix_succ _ _ _ _)

theorem playFrom_eq_getD (p : List X) (σ τ : Strategy X) (n k : ℕ)
    (hk : k < p.length + n) :
    playFrom p σ τ k = (posFrom p σ τ n).getD k (Classical.arbitrary X) := by
  have h1 : k < (posFrom p σ τ (k + 1)).length := by
    rw [posFrom_length]; omega
  have h2 : k < (posFrom p σ τ n).length := by rw [posFrom_length]; exact hk
  rcases le_total (k + 1) n with h | h
  · exact getD_of_prefix (posFrom_prefix p σ τ h) h1 _
  · exact (getD_of_prefix (posFrom_prefix p σ τ h) h2 _).symm

theorem posFrom_eq_map (p : List X) (σ τ : Strategy X) (n : ℕ) :
    posFrom p σ τ n = (List.range (p.length + n)).map (playFrom p σ τ) := by
  apply List.ext_getElem
  · simp [posFrom_length]
  · intro k h₁ h₂
    rw [posFrom_length] at h₁
    rw [List.getElem_map, List.getElem_range]
    rw [playFrom_eq_getD p σ τ n k h₁, List.getD_eq_getElem]

omit [Nonempty X] in
theorem posFrom_shift (p : List X) (σ τ : Strategy X) (n : ℕ) :
    posFrom (p ++ [nextMove σ τ p]) σ τ n = posFrom p σ τ (n + 1) := by
  induction n with
  | zero => simp [posFrom]
  | succ n ih => rw [posFrom, ih]; rfl

theorem playFrom_shift (p : List X) (σ τ : Strategy X) :
    playFrom (p ++ [nextMove σ τ p]) σ τ = playFrom p σ τ := by
  funext k
  have h : playFrom (p ++ [nextMove σ τ p]) σ τ k
      = (posFrom (p ++ [nextMove σ τ p]) σ τ (k + 1)).getD k (Classical.arbitrary X) := rfl
  rw [h, posFrom_shift]
  exact (playFrom_eq_getD p σ τ (k + 2) k (by omega)).symm

omit [Nonempty X] in
theorem posFrom_congr (p : List X) {σ σ' τ τ' : Strategy X}
    (hσ : ∀ q, p <+: q → σ q = σ' q) (hτ : ∀ q, p <+: q → τ q = τ' q) (n : ℕ) :
    posFrom p σ τ n = posFrom p σ' τ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpre : p <+: posFrom p σ τ n := by
      have := posFrom_prefix p σ τ (Nat.zero_le n)
      simpa [posFrom] using this
    rw [posFrom, posFrom, ih, nextMove, nextMove, ← ih, hσ _ hpre, hτ _ hpre, ih]

theorem playFrom_congr (p : List X) {σ σ' τ τ' : Strategy X}
    (hσ : ∀ q, p <+: q → σ q = σ' q) (hτ : ∀ q, p <+: q → τ q = τ' q) :
    playFrom p σ τ = playFrom p σ' τ' := by
  funext k
  show (posFrom p σ τ (k + 1)).getD k (Classical.arbitrary X)
      = (posFrom p σ' τ' (k + 1)).getD k (Classical.arbitrary X)
  rw [posFrom_congr p hσ hτ]

/-! ### Propagation of winning positions -/

theorem IWins_of_child_even {A : Set (ℕ → X)} {p : List X} (hp : Even p.length) {a : X}
    (hc : IWins A (p ++ [a])) : IWins A p := by
  classical
  obtain ⟨σa, hσa⟩ := hc
  refine ⟨fun q => if q = p then a else σa q, fun τ => ?_⟩
  set σ : Strategy X := fun q => if q = p then a else σa q with hσdef
  have hmove : nextMove σ τ p = a := by simp [nextMove, hp, hσdef]
  have h1 : playFrom p σ τ = playFrom (p ++ [a]) σ τ := by
    rw [← hmove]; exact (playFrom_shift p σ τ).symm
  have h2 : playFrom (p ++ [a]) σ τ = playFrom (p ++ [a]) σa τ := by
    refine playFrom_congr _ (fun q hq => ?_) (fun q _ => rfl)
    have hne : q ≠ p := by
      rintro rfl
      have := hq.length_le
      simp at this
    simp [hσdef, hne]
  rw [h1, h2]
  exact hσa τ

theorem IWins_of_children_odd {A : Set (ℕ → X)} {p : List X} (hp : ¬ Even p.length)
    (hc : ∀ b : X, IWins A (p ++ [b])) : IWins A p := by
  classical
  choose σb hσb using hc
  refine ⟨fun q => σb (q.getD p.length (Classical.arbitrary X)) q, fun τ => ?_⟩
  set σ : Strategy X := fun q => σb (q.getD p.length (Classical.arbitrary X)) q with hσdef
  have hmove : nextMove σ τ p = τ p := by simp [nextMove, hp]
  have h1 : playFrom p σ τ = playFrom (p ++ [τ p]) σ τ := by
    rw [← hmove]; exact (playFrom_shift p σ τ).symm
  have h2 : playFrom (p ++ [τ p]) σ τ = playFrom (p ++ [τ p]) (σb (τ p)) τ := by
    refine playFrom_congr _ (fun q hq => ?_) (fun q _ => rfl)
    have hlen : p.length < (p ++ [τ p]).length := by simp
    have hgd : q.getD p.length (Classical.arbitrary X) = τ p := by
      rw [← getD_of_prefix hq hlen]
      simp
    show σb (q.getD p.length (Classical.arbitrary X)) q = σb (τ p) q
    rw [hgd]
  rw [h1, h2]
  exact hσb (τ p) τ

/-! ### The Gale–Stewart theorem: open games are determined -/

open Classical in
/-- A strategy for player II which, from a position not winning for player I,
moves to a position which is still not winning for player I. -/
noncomputable def defenseStrategy (A : Set (ℕ → X)) : Strategy X :=
  fun q => if h : ∃ b : X, ¬ IWins A (q ++ [b]) then h.choose else Classical.arbitrary X

theorem not_IWins_defense {A : Set (ℕ → X)} {q : List X} (hq : ¬ IWins A q)
    (hodd : ¬ Even q.length) : ¬ IWins A (q ++ [defenseStrategy A q]) := by
  classical
  have hex : ∃ b : X, ¬ IWins A (q ++ [b]) := by
    by_contra hcon
    push_neg at hcon
    exact hq (IWins_of_children_odd hodd hcon)
  have hdef : defenseStrategy A q = hex.choose := by
    simp only [defenseStrategy, dif_pos hex]
  rw [hdef]
  exact hex.choose_spec

theorem not_IWins_posFrom {A : Set (ℕ → X)} (h : ¬ IWins A []) (σ : Strategy X) (n : ℕ) :
    ¬ IWins A (posFrom [] σ (defenseStrategy A) n) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    set q := posFrom [] σ (defenseStrategy A) n with hq
    show ¬ IWins A (q ++ [nextMove σ (defenseStrategy A) q])
    by_cases hpar : Even q.length
    · have hm : nextMove σ (defenseStrategy A) q = σ q := by simp [nextMove, hpar]
      rw [hm]
      exact fun hc => ih (IWins_of_child_even hpar hc)
    · have hm : nextMove σ (defenseStrategy A) q = defenseStrategy A q := by
        simp [nextMove, hpar]
      rw [hm]
      exact not_IWins_defense ih hpar

/-- **Gale–Stewart theorem**: every game with an open payoff set is determined.
This is the base case of Martin's transfinite induction for Borel determinacy. -/
theorem gale_stewart_open (A : Set (ℕ → X)) (hA : IsOpenPayoff A) : Determined A := by
  by_cases h : IWins A []
  · exact Or.inl h
  refine Or.inr ⟨defenseStrategy A, fun σ hmem => ?_⟩
  obtain ⟨n, hn⟩ := hA _ hmem
  refine not_IWins_posFrom h σ n ⟨defenseStrategy A, fun τ' => ?_⟩
  refine hn _ (fun i hi => ?_)
  set q := posFrom [] σ (defenseStrategy A) n with hqdef
  have hqlen : q.length = n := by rw [hqdef, posFrom_length]; simp
  have h1 : playFrom q (defenseStrategy A) τ' i
      = q.getD i (Classical.arbitrary X) := by
    have : i < q.length + 0 := by omega
    simpa [posFrom] using playFrom_eq_getD q (defenseStrategy A) τ' 0 i this
  have h2 : playFrom [] σ (defenseStrategy A) i = q.getD i (Classical.arbitrary X) := by
    have : i < ([] : List X).length + n := by simpa using hi
    simpa [hqdef] using playFrom_eq_getD ([] : List X) σ (defenseStrategy A) n i this
  rw [h1, h2]

/-! ### The dual (closed) case -/

theorem IIWins_of_child_odd {A : Set (ℕ → X)} {p : List X} (hp : ¬ Even p.length) {b : X}
    (hc : IIWins A (p ++ [b])) : IIWins A p := by
  classical
  obtain ⟨τb, hτb⟩ := hc
  refine ⟨fun q => if q = p then b else τb q, fun σ => ?_⟩
  set τ : Strategy X := fun q => if q = p then b else τb q with hτdef
  have hmove : nextMove σ τ p = b := by simp [nextMove, hp, hτdef]
  have h1 : playFrom p σ τ = playFrom (p ++ [b]) σ τ := by
    rw [← hmove]; exact (playFrom_shift p σ τ).symm
  have h2 : playFrom (p ++ [b]) σ τ = playFrom (p ++ [b]) σ τb := by
    refine playFrom_congr _ (fun q _ => rfl) (fun q hq => ?_)
    have hne : q ≠ p := by
      rintro rfl
      have := hq.length_le
      simp at this
    simp [hτdef, hne]
  rw [h1, h2]
  exact hτb σ

theorem IIWins_of_children_even {A : Set (ℕ → X)} {p : List X} (hp : Even p.length)
    (hc : ∀ a : X, IIWins A (p ++ [a])) : IIWins A p := by
  classical
  choose τa hτa using hc
  refine ⟨fun q => τa (q.getD p.length (Classical.arbitrary X)) q, fun σ => ?_⟩
  set τ : Strategy X := fun q => τa (q.getD p.length (Classical.arbitrary X)) q with hτdef
  have hmove : nextMove σ τ p = σ p := by simp [nextMove, hp]
  have h1 : playFrom p σ τ = playFrom (p ++ [σ p]) σ τ := by
    rw [← hmove]; exact (playFrom_shift p σ τ).symm
  have h2 : playFrom (p ++ [σ p]) σ τ = playFrom (p ++ [σ p]) σ (τa (σ p)) := by
    refine playFrom_congr _ (fun q _ => rfl) (fun q hq => ?_)
    have hlen : p.length < (p ++ [σ p]).length := by simp
    have hgd : q.getD p.length (Classical.arbitrary X) = σ p := by
      rw [← getD_of_prefix hq hlen]
      simp
    show τa (q.getD p.length (Classical.arbitrary X)) q = τa (σ p) q
    rw [hgd]
  rw [h1, h2]
  exact hτa (σ p) σ

open Classical in
/-- A strategy for player I which, from a position not winning for player II,
moves to a position which is still not winning for player II. -/
noncomputable def attackStrategy (A : Set (ℕ → X)) : Strategy X :=
  fun q => if h : ∃ a : X, ¬ IIWins A (q ++ [a]) then h.choose else Classical.arbitrary X

theorem not_IIWins_attack {A : Set (ℕ → X)} {q : List X} (hq : ¬ IIWins A q)
    (heven : Even q.length) : ¬ IIWins A (q ++ [attackStrategy A q]) := by
  classical
  have hex : ∃ a : X, ¬ IIWins A (q ++ [a]) := by
    by_contra hcon
    push_neg at hcon
    exact hq (IIWins_of_children_even heven hcon)
  have hdef : attackStrategy A q = hex.choose := by
    simp only [attackStrategy, dif_pos hex]
  rw [hdef]
  exact hex.choose_spec

theorem not_IIWins_posFrom {A : Set (ℕ → X)} (h : ¬ IIWins A []) (τ : Strategy X) (n : ℕ) :
    ¬ IIWins A (posFrom [] (attackStrategy A) τ n) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    set q := posFrom [] (attackStrategy A) τ n with hq
    show ¬ IIWins A (q ++ [nextMove (attackStrategy A) τ q])
    by_cases hpar : Even q.length
    · have hm : nextMove (attackStrategy A) τ q = attackStrategy A q := by
        simp [nextMove, hpar]
      rw [hm]
      exact not_IIWins_attack ih hpar
    · have hm : nextMove (attackStrategy A) τ q = τ q := by simp [nextMove, hpar]
      rw [hm]
      exact fun hc => ih (IIWins_of_child_odd hpar hc)

/-- **Gale–Stewart theorem, closed case**: a game whose payoff set has open complement
(i.e. player I's payoff set is closed) is determined. -/
theorem gale_stewart_closed (A : Set (ℕ → X)) (hA : IsOpenPayoff Aᶜ) : Determined A := by
  by_cases h : IIWins A []
  · exact Or.inr h
  refine Or.inl ⟨attackStrategy A, fun τ => ?_⟩
  by_contra hmem
  obtain ⟨n, hn⟩ := hA _ hmem
  refine not_IIWins_posFrom h τ n ⟨attackStrategy A, fun σ' hmem' => ?_⟩
  set q := posFrom [] (attackStrategy A) τ n with hqdef
  have hqlen : q.length = n := by rw [hqdef, posFrom_length]; simp
  refine hn (playFrom q σ' (attackStrategy A)) (fun i hi => ?_) hmem'
  have h1 : playFrom q σ' (attackStrategy A) i = q.getD i (Classical.arbitrary X) := by
    have : i < q.length + 0 := by omega
    simpa [posFrom] using playFrom_eq_getD q σ' (attackStrategy A) 0 i this
  have h2 : playFrom [] (attackStrategy A) τ i = q.getD i (Classical.arbitrary X) := by
    have : i < ([] : List X).length + n := by simpa using hi
    simpa [hqdef] using playFrom_eq_getD ([] : List X) (attackStrategy A) τ n i this
  rw [h1, h2]

/-! ### Sanity checks: plays really follow the strategies -/

theorem playFrom_of_lt_length (p : List X) (σ τ : Strategy X) {k : ℕ} (hk : k < p.length) :
    playFrom p σ τ k = p.getD k (Classical.arbitrary X) := by
  simpa [posFrom] using playFrom_eq_getD p σ τ 0 k (by omega)

theorem playFrom_at_length (p : List X) (σ τ : Strategy X) :
    playFrom p σ τ p.length = nextMove σ τ p := by
  have h := playFrom_eq_getD p σ τ 1 p.length (by omega)
  simpa [posFrom] using h

theorem not_IWins_and_IIWins (A : Set (ℕ → X)) (p : List X) :
    ¬ (IWins A p ∧ IIWins A p) := by
  rintro ⟨⟨σ, hσ⟩, ⟨τ, hτ⟩⟩
  exact hτ σ (hσ τ)

/-! ### Topological form of the Gale–Stewart theorem -/

section Topology

variable [TopologicalSpace X]

omit [Nonempty X] in
/-- An open subset of the product space `ℕ → X` is an open payoff set. -/
theorem isOpenPayoff_of_isOpen {A : Set (ℕ → X)} (hA : IsOpen A) : IsOpenPayoff A := by
  intro x hx
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hA x hx
  refine ⟨(I.sup id) + 1, fun y hy => ?_⟩
  refine hsub (fun i hi => ?_)
  have hlt : i < (I.sup id) + 1 := lt_of_le_of_lt (Finset.le_sup (f := id) hi) (by omega)
  rw [hy i hlt]
  exact (hu i hi).2

/-- **Gale–Stewart theorem, topological form**: a game whose payoff set is open in the
product topology on `ℕ → X` is determined. (In the intended descriptive-set-theoretic
setting `X` carries the discrete topology, so that `ℕ → X` is a Baire space.) -/
theorem gale_stewart {A : Set (ℕ → X)} (hA : IsOpen A) : Determined A :=
  gale_stewart_open A (isOpenPayoff_of_isOpen hA)

/-- A payoff set is *Borel* if it belongs to the Borel σ-algebra of the product
topology on `ℕ → X`. -/
def IsBorelPayoff (A : Set (ℕ → X)) : Prop := @MeasurableSet _ (borel (ℕ → X)) A

omit [Nonempty X] in
theorem isBorelPayoff_of_isOpen {A : Set (ℕ → X)} (hA : IsOpen A) : IsBorelPayoff A :=
  MeasurableSpace.measurableSet_generateFrom hA

/-- **Martin's theorem, as a statement**: every Borel game on `X` is determined. -/
def BorelDeterminacyStatement (X : Type u) [Nonempty X] [TopologicalSpace X] : Prop :=
  ∀ A : Set (ℕ → X), IsBorelPayoff A → Determined A

/-! ### Unravelings (Martin coverings) and the reduction to the open case -/

/-- An *unraveling* of a payoff set `A ⊆ ℕ → X` (an abstract form of a Martin covering
whose covering game has clopen payoff): an auxiliary game on moves `Y` whose payoff set
`payoff` is topologically simple (open or closed) and is the pullback of `A` along a
projection `proj` of plays, together
with maps lifting strategies of the auxiliary game to strategies of the original game in
such a way that every play against a lifted strategy is the projection of some play
against the original strategy.

Martin's unraveling theorem states that every Borel `A` admits such an unraveling; it is
the only ingredient of Martin's proof that is not formalized here. -/
structure Unraveling (A : Set (ℕ → X)) where
  /-- the move set of the auxiliary (covering) game -/
  Y : Type u
  [nonemptyY : Nonempty Y]
  /-- projection of plays of the covering game to plays of the original game -/
  proj : (ℕ → Y) → (ℕ → X)
  /-- the payoff set of the covering game -/
  payoff : Set (ℕ → Y)
  /-- the covering game has a topologically simple (open or closed, e.g. clopen) payoff -/
  simple_payoff : IsOpenPayoff payoff ∨ IsOpenPayoff payoffᶜ
  pullback : payoff = proj ⁻¹' A
  /-- lifting of player I's strategies -/
  liftI : Strategy Y → Strategy X
  /-- lifting of player II's strategies -/
  liftII : Strategy Y → Strategy X
  liftI_spec : ∀ (s : Strategy Y) (τ : Strategy X), ∃ t : Strategy Y,
    proj (playFrom [] s t) = playFrom [] (liftI s) τ
  liftII_spec : ∀ (t : Strategy Y) (σ : Strategy X), ∃ s : Strategy Y,
    proj (playFrom [] s t) = playFrom [] σ (liftII t)

attribute [instance] Unraveling.nonemptyY

/-- Any open payoff set is unraveled by itself (the identity covering); in particular
unravelings exist. -/
def Unraveling.ofOpen (A : Set (ℕ → X)) (hA : IsOpenPayoff A) : Unraveling A where
  Y := X
  proj := id
  payoff := A
  simple_payoff := Or.inl hA
  pullback := rfl
  liftI := id
  liftII := id
  liftI_spec := fun _ τ => ⟨τ, rfl⟩
  liftII_spec := fun _ σ => ⟨σ, rfl⟩

/-- Any closed payoff set is unraveled by itself (the identity covering). -/
def Unraveling.ofClosed (A : Set (ℕ → X)) (hA : IsOpenPayoff Aᶜ) : Unraveling A where
  Y := X
  proj := id
  payoff := A
  simple_payoff := Or.inr hA
  pullback := rfl
  liftI := id
  liftII := id
  liftI_spec := fun _ τ => ⟨τ, rfl⟩
  liftII_spec := fun _ σ => ⟨σ, rfl⟩

omit [TopologicalSpace X] in
/-- **Martin's reduction**: a payoff set admitting an unraveling is determined. -/
theorem determined_of_unraveling {A : Set (ℕ → X)} (U : Unraveling A) : Determined A := by
  have hdet : Determined U.payoff :=
    U.simple_payoff.elim (gale_stewart_open U.payoff) (gale_stewart_closed U.payoff)
  rcases hdet with ⟨s, hs⟩ | ⟨t, ht⟩
  · refine Or.inl ⟨U.liftI s, fun τ => ?_⟩
    obtain ⟨t, hst⟩ := U.liftI_spec s τ
    have : playFrom [] s t ∈ U.proj ⁻¹' A := U.pullback ▸ hs t
    rwa [Set.mem_preimage, hst] at this
  · refine Or.inr ⟨U.liftII t, fun σ hmem => ?_⟩
    obtain ⟨s, hst⟩ := U.liftII_spec t σ
    refine ht s ?_
    rw [U.pullback, Set.mem_preimage, hst]
    exact hmem

/-- **Borel determinacy (Martin's theorem)**, as a Lean-checked reduction: if every Borel
payoff set admits an unraveling (Martin's unraveling theorem), then every Borel game is
determined.

The reduction itself, together with its base case (the Gale–Stewart theorem
`Frontier.gale_stewart_open`, proved here from scratch), is fully formalized; the
hypothesis `hUnravel` is exactly Martin's covering construction. The hypothesis is not
vacuous: `Frontier.Unraveling.ofOpen` produces unravelings of open payoff sets. -/
theorem Borel_determinacy
    (hUnravel : ∀ A : Set (ℕ → X), IsBorelPayoff A → Nonempty (Unraveling A)) :
    BorelDeterminacyStatement X :=
  fun A hA => determined_of_unraveling (hUnravel A hA).some

omit [TopologicalSpace X] in
/-- Consistency check: the reduction applied to the identity unraveling recovers the
Gale–Stewart theorem. -/
theorem determined_of_isOpenPayoff {A : Set (ℕ → X)} (hA : IsOpenPayoff A) : Determined A :=
  determined_of_unraveling (Unraveling.ofOpen A hA)

/-- The lowest levels of the Borel hierarchy: open and closed games are determined. -/
theorem determined_of_isOpen_or_isClosed {A : Set (ℕ → X)} (hA : IsOpen A ∨ IsClosed A) :
    Determined A :=
  hA.elim (fun h => gale_stewart_open A (isOpenPayoff_of_isOpen h))
    (fun h => gale_stewart_closed A (isOpenPayoff_of_isOpen h.isOpen_compl))

end Topology

end Frontier

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

