/-
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above repeats verbatim as a module docstring below; Lean 4 does not allow a
-- module docstring to precede the `import` commands.)

import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

/-! ## Infinite two-player games on sequences -/

/-- A strategy is a map from the finite history of moves played so far to the next move. -/

def Strategy (A : Type u) : Type u := List A → A

variable {A : Type u}

/-- The list of the first `n` moves of the play `x`. -/

def hist (x : ℕ → A) (n : ℕ) : List A := (List.range n).map x

lemma hist_succ (x : ℕ → A) (n : ℕ) : hist x (n + 1) = hist x n ++ [x n] := by
  simp [hist, List.range_succ]

lemma hist_getD [Inhabited A] (x : ℕ → A) {i n : ℕ} (h : i < n) :
    (hist x n).getD i default = x i := by
  simp [hist, List.getD_eq_getElem?_getD, h]

def ConsI (p : List A) (σ : Strategy A) (x : ℕ → A) : Prop :=
  hist x p.length = p ∧ ∀ n, p.length ≤ n → Even n → x n = σ (hist x n)

/-- `ConsII p τ x` : the play `x` extends the position `p` and player II (who moves at the odd
positions) follows the strategy `τ` from `p` onwards. -/

def ConsII (p : List A) (τ : Strategy A) (x : ℕ → A) : Prop :=
  hist x p.length = p ∧ ∀ n, p.length ≤ n → Odd n → x n = τ (hist x n)

/-- Player I follows `σ` throughout the whole play `x`. -/

def ConsistentI (σ : Strategy A) (x : ℕ → A) : Prop := ConsI [] σ x

/-- Player II follows `τ` throughout the whole play `x`. -/

def ConsistentII (τ : Strategy A) (x : ℕ → A) : Prop := ConsII [] τ x

/-- `σ` is a winning strategy for player I in the game with payoff set `S` started at `p`. -/

def WinIFrom (S : Set (ℕ → A)) (p : List A) (σ : Strategy A) : Prop :=
  ∀ x, ConsI p σ x → x ∈ S

/-- Player I has a winning strategy in the game with payoff set `S` started at `p`. -/

def IWins (S : Set (ℕ → A)) (p : List A) : Prop := ∃ σ, WinIFrom S p σ

/-- The game with payoff set `S` (player I wins a play `x` iff `x ∈ S`) is determined. -/

def Determined (S : Set (ℕ → A)) : Prop :=
  (∃ σ : Strategy A, ∀ x, ConsistentI σ x → x ∈ S) ∨
  (∃ τ : Strategy A, ∀ x, ConsistentII τ x → x ∉ S)

/-! ## A combinatorial description of the (cl)open sets of the sequence space -/

/-- `S` is open in the product topology on `ℕ → A` with `A` discrete: every member of `S` has a
finite prefix all of whose extensions lie in `S`. -/

def IsOpenSeq (S : Set (ℕ → A)) : Prop :=
  ∀ x ∈ S, ∃ n, ∀ y, hist y n = hist x n → y ∈ S

/-- `S` is clopen in the product topology on `ℕ → A` with `A` discrete. -/

def IsClopenSeq (S : Set (ℕ → A)) : Prop := IsOpenSeq S ∧ IsOpenSeq Sᶜ

section Topology

variable [TopologicalSpace A] [DiscreteTopology A]

omit [DiscreteTopology A] in
/-- Openness in the product topology implies the combinatorial notion `IsOpenSeq`. -/

lemma iWins_of_all_extensions {S : Set (ℕ → A)} {p : List A}
    (h : ∀ y, hist y p.length = p → y ∈ S) : IWins S p :=
  ⟨fun _ => default, fun x hx => h x hx.1⟩

omit [Inhabited A] in

lemma not_iWins_snoc_of_even {S : Set (ℕ → A)} {p : List A} (hp : Even p.length)
    (h : ¬ IWins S p) (a : A) : ¬ IWins S (p ++ [a]) := by
  classical
  rintro ⟨σ, hσ⟩
  refine h ⟨fun l => if l = p then a else σ l, fun x hx => ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  have hfirst : x p.length = a := by
    have := hx2 p.length le_rfl hp
    simpa [hx1] using this
  have hext : hist x (p ++ [a]).length = p ++ [a] := by
    have : (p ++ [a]).length = p.length + 1 := by simp
    rw [this, hist_succ, hx1, hfirst]
  refine hσ x ⟨hext, fun n hn hne => ?_⟩
  have hn' : p.length < n := by simpa using hn
  have hne' : hist x n ≠ p := by
    intro hcon
    have := congrArg List.length hcon
    simp at this
    omega
  have := hx2 n (le_of_lt hn') hne
  simpa [hne'] using this

lemma exists_not_iWins_snoc {S : Set (ℕ → A)} {p : List A}
    (h : ¬ IWins S p) : ∃ b : A, ¬ IWins S (p ++ [b]) := by
  by_contra hcon
  push_neg at hcon
  choose f hf using fun b => (hcon b)
  refine h ⟨fun l => f (l.getD p.length default) l, fun x hx => ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  set b := x p.length with hb
  refine hf b x ⟨?_, fun n hn hno => ?_⟩
  · have hlen : (p ++ [b]).length = p.length + 1 := by simp
    rw [hlen, hist_succ, hx1]
  · have hn' : p.length < n := by simpa using hn
    have hxn := hx2 n (le_of_lt hn') hno
    simp only [hist_getD x hn'] at hxn
    exact hxn

/-- **Gale–Stewart theorem** (base case of Borel determinacy): a game whose payoff set is open
is determined. -/

theorem determined_of_isOpenSeq {S : Set (ℕ → A)} (hS : IsOpenSeq S) : Determined S := by
  classical
  by_cases hI : IWins S []
  · obtain ⟨σ, hσ⟩ := hI
    exact Or.inl ⟨σ, hσ⟩
  · right
    refine ⟨fun p => if h : ∃ b, ¬ IWins S (p ++ [b]) then h.choose else default,
      fun x hx hxS => ?_⟩
    obtain ⟨-, hx2⟩ := hx
    have hgood : ∀ n, ¬ IWins S (hist x n) := by
      intro n
      induction n with
      | zero => simpa using hI
      | succ n ih =>
        rw [hist_succ]
        rcases Nat.even_or_odd n with he | ho
        · exact not_iWins_snoc_of_even (by simpa using he) ih (x n)
        · have hex : ∃ b, ¬ IWins S (hist x n ++ [b]) := exists_not_iWins_snoc ih
          have hxn := hx2 n (by simp) ho
          simp only [dif_pos hex] at hxn
          rw [hxn]
          exact hex.choose_spec
    obtain ⟨n, hn⟩ := hS x hxS
    refine hgood n (iWins_of_all_extensions (p := hist x n) fun y hy => hn y ?_)
    simpa using hy

/-- Clopen games are determined. -/

theorem determined_of_isClopenSeq {S : Set (ℕ → A)} (hS : IsClopenSeq S) : Determined S :=
  determined_of_isOpenSeq hS.1

/-- **Gale–Stewart theorem**, topological form: a game on a discrete alphabet whose payoff set is
open in the product topology is determined. -/

def Covering.refl (A : Type u) : Covering A A where
  push := id
  liftI := id
  liftII := id
  liftI_spec := fun _ x hx => ⟨x, hx, rfl⟩
  liftII_spec := fun _ x hx => ⟨x, hx, rfl⟩

/-- Determinacy transfers downwards along a covering. -/

theorem Covering.determined {B : Type u} (cov : Covering A B) {S : Set (ℕ → A)}
    (h : Determined (cov.push ⁻¹' S)) : Determined S := by
  rcases h with ⟨σ, hσ⟩ | ⟨τ, hτ⟩
  · refine Or.inl ⟨cov.liftI σ, fun x hx => ?_⟩
    obtain ⟨y, hy, hpush⟩ := cov.liftI_spec σ x hx
    have := hσ y hy
    rwa [Set.mem_preimage, hpush] at this
  · refine Or.inr ⟨cov.liftII τ, fun x hx => ?_⟩
    obtain ⟨y, hy, hpush⟩ := cov.liftII_spec τ x hx
    have := hτ y hy
    rwa [Set.mem_preimage, hpush] at this

/-! ## Borel determinacy -/

/-- Martin's *unravelling* hypothesis: every Borel payoff set admits a covering in which it
becomes clopen.  This is the deep combinatorial content of Martin's theorem. -/

def UnravelsBorel (A : Type u) [TopologicalSpace A] : Prop :=
  ∀ S : Set (ℕ → A), @MeasurableSet (ℕ → A) (borel (ℕ → A)) S →
    ∃ (B : Type u) (cov : Covering A B), Nonempty (Inhabited B) ∧ IsClopenSeq (cov.push ⁻¹' S)

/-- A payoff set that is already clopen is unravelled by the identity covering; in particular the
unravelling condition is satisfiable. -/

theorem Borel_determinacy [TopologicalSpace A] [DiscreteTopology A] [Inhabited A]
    (hUnravel : UnravelsBorel A) (S : Set (ℕ → A)) (hS : @MeasurableSet (ℕ → A) (borel (ℕ → A)) S) :
    Determined S := by
  obtain ⟨B, cov, ⟨hB⟩, hclopen⟩ := hUnravel S hS
  haveI : Inhabited B := hB
  exact cov.determined (determined_of_isClopenSeq hclopen)

end Frontier
