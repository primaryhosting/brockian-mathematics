import Mathlib

/-!
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON THE HEADER: Lean 4 requires `import` to be the first command of a file, so the
module docstring above is placed directly after `import Mathlib` (a `/-! ... -/` block
before the import is a parse error).
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Math2

universe u v w

open SimpleGraph

/-! ## The minor relation -/

/-- `IsMinor H G` says that `H` is a minor of `G`: there is a family of pairwise disjoint,
nonempty, connected *branch sets* `B w ⊆ V(G)`, indexed by the vertices `w` of `H`, such
that adjacent vertices of `H` have an edge of `G` between their branch sets. -/
def IsMinor {V : Type u} {W : Type v} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ B : W → Set V,
    (∀ w, (B w).Nonempty) ∧
    (∀ w, (G.induce (B w)).Connected) ∧
    (∀ w w', w ≠ w' → Disjoint (B w) (B w')) ∧
    (∀ w w', H.Adj w w' → ∃ a ∈ B w, ∃ b ∈ B w', G.Adj a b)

/-- `Embeds H G` says that `H` is isomorphic to a subgraph of `G`, i.e. there is an
injective adjacency-preserving map from the vertices of `H` to the vertices of `G`. -/
def Embeds {V : Type u} {W : Type v} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ a b, H.Adj a b → G.Adj (f a) (f b)

/-- A subgraph embedding gives a minor (with singleton branch sets). -/
theorem Embeds.isMinor {V : Type u} {W : Type v} {H : SimpleGraph W} {G : SimpleGraph V}
    (h : Embeds H G) : IsMinor H G := by
  obtain ⟨f, hinj, hadj⟩ := h
  refine ⟨fun w => {f w}, fun w => ⟨f w, rfl⟩, ?_, ?_, ?_⟩
  · intro w
    haveI : Nonempty ↥({f w} : Set V) := ⟨⟨f w, rfl⟩⟩
    refine SimpleGraph.Connected.mk ?_
    intro a b
    have hab : a = b := Subtype.ext (by
      have ha : a.1 = f w := a.2
      have hb : b.1 = f w := b.2
      rw [ha, hb])
    exact hab ▸ SimpleGraph.Reachable.refl a
  · intro w w' hne
    simp only [Set.disjoint_singleton]
    exact fun h => hne (hinj h)
  · intro w w' hww'
    exact ⟨f w, rfl, f w', rfl, hadj _ _ hww'⟩

/-- The minor relation is reflexive. -/
theorem isMinor_refl {V : Type u} (G : SimpleGraph V) : IsMinor G G :=
  Embeds.isMinor ⟨id, Function.injective_id, fun _ _ h => h⟩

/-- Embeddings compose with isomorphisms on both sides. -/
theorem Embeds.congr {V : Type u} {W : Type v} {V' : Type w} {W' : Type*}
    {H : SimpleGraph W} {G : SimpleGraph V} {H' : SimpleGraph W'} {G' : SimpleGraph V'}
    (eH : H ≃g H') (eG : G' ≃g G) (h : Embeds H' G') : Embeds H G := by
  obtain ⟨f, hinj, hadj⟩ := h
  refine ⟨fun x => eG (f (eH x)), ?_, ?_⟩
  · intro a b hab
    exact eH.injective (hinj (eG.injective hab))
  · intro a b hab
    exact eG.map_adj_iff.2 (hadj _ _ (eH.map_adj_iff.2 hab))

/-! ## The minor relation is transitive -/

/-- Reachability transfers along an inclusion of induced subgraphs. -/
theorem reachable_induce_mono {V : Type u} {G : SimpleGraph V} {S T : Set V} (hST : S ⊆ T)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S)
    (h : (G.induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    (G.induce T).Reachable ⟨x, hST hx⟩ ⟨y, hST hy⟩ := by
  let f : G.induce S →g G.induce T := ⟨fun z => ⟨z.1, hST z.2⟩, fun {_ _} hab => hab⟩
  exact h.map f

section Glue

variable {V : Type u} {U : Type v} {G : SimpleGraph V} {K : SimpleGraph U} {C : V → Set U}

/-- The union of the branch sets attached to a set `B` of vertices. -/
def glue (C : V → Set U) (B : Set V) : Set U := ⋃ v ∈ B, C v

theorem mem_glue {B : Set V} {v : V} (hv : v ∈ B) {u : U} (hu : u ∈ C v) : u ∈ glue C B :=
  Set.mem_biUnion hv hu

/-- Two vertices lying in branch sets joined by a walk of `G` inside `B` are reachable
inside the glued set. -/
theorem reachable_glue_of_walk (hC : ∀ v, (K.induce (C v)).Connected)
    (hedge : ∀ v v', G.Adj v v' → ∃ u ∈ C v, ∃ u' ∈ C v', K.Adj u u')
    {B : Set V} : ∀ {a b : ↥B} (_ : (G.induce B).Walk a b) {x y : U}
      (hx : x ∈ C a.1) (hy : y ∈ C b.1),
      (K.induce (glue C B)).Reachable ⟨x, mem_glue a.2 hx⟩ ⟨y, mem_glue b.2 hy⟩ := by
  intro a b w
  induction w with
  | @nil a =>
    intro x y hx hy
    exact reachable_induce_mono (Set.subset_biUnion_of_mem a.2) hx hy
      ((hC a.1).preconnected ⟨x, hx⟩ ⟨y, hy⟩)
  | @cons a c b hac _ ih =>
    intro x y hx hy
    obtain ⟨u, hu, u', hu', huu'⟩ := hedge a.1 c.1 hac
    have h1 : (K.induce (glue C B)).Reachable ⟨x, mem_glue a.2 hx⟩ ⟨u, mem_glue a.2 hu⟩ :=
      reachable_induce_mono (Set.subset_biUnion_of_mem a.2) hx hu
        ((hC a.1).preconnected ⟨x, hx⟩ ⟨u, hu⟩)
    have h2 : (K.induce (glue C B)).Adj ⟨u, mem_glue a.2 hu⟩ ⟨u', mem_glue c.2 hu'⟩ := huu'
    exact (h1.trans h2.reachable).trans (ih hu' hy)

/-- Gluing connected branch sets along a connected set of vertices yields a connected set. -/
theorem connected_glue (hC : ∀ v, (K.induce (C v)).Connected)
    (hedge : ∀ v v', G.Adj v v' → ∃ u ∈ C v, ∃ u' ∈ C v', K.Adj u u')
    {B : Set V} (hB : (G.induce B).Connected) : (K.induce (glue C B)).Connected := by
  obtain ⟨a⟩ := hB.nonempty
  obtain ⟨u₀⟩ := (hC a.1).nonempty
  haveI : Nonempty ↥(glue C B) := ⟨⟨u₀.1, mem_glue a.2 u₀.2⟩⟩
  refine SimpleGraph.Connected.mk ?_
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  simp only [glue, Set.mem_iUnion, exists_prop] at hx hy
  obtain ⟨v, hv, hxv⟩ := hx
  obtain ⟨v', hv', hyv'⟩ := hy
  exact reachable_glue_of_walk hC hedge ((hB.preconnected ⟨v, hv⟩ ⟨v', hv'⟩).some) hxv hyv'

end Glue

/-- The minor relation is transitive. -/
theorem IsMinor.trans {V : Type u} {U : Type v} {W : Type w} {H : SimpleGraph W}
    {G : SimpleGraph V} {K : SimpleGraph U}
    (h₁ : IsMinor H G) (h₂ : IsMinor G K) : IsMinor H K := by
  obtain ⟨B, hBne, hBconn, hBdisj, hBadj⟩ := h₁
  obtain ⟨C, hCne, hCconn, hCdisj, hCadj⟩ := h₂
  refine ⟨fun w => glue C (B w), ?_, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨v, hv⟩ := hBne w
    obtain ⟨u, hu⟩ := hCne v
    exact ⟨u, mem_glue hv hu⟩
  · intro w
    exact connected_glue hCconn hCadj (hBconn w)
  · intro w w' hne
    rw [Set.disjoint_left]
    rintro u hu hu'
    simp only [glue, Set.mem_iUnion, exists_prop] at hu hu'
    obtain ⟨v, hv, huv⟩ := hu
    obtain ⟨v', hv', huv'⟩ := hu'
    have hvv' : v = v' := by
      by_contra hcon
      exact (Set.disjoint_left.1 (hCdisj v v' hcon)) huv huv'
    subst hvv'
    exact (Set.disjoint_left.1 (hBdisj w w' hne)) hv hv'
  · intro w w' hww'
    obtain ⟨a, ha, b, hb, hab⟩ := hBadj w w' hww'
    obtain ⟨u, hu, u', hu', huu'⟩ := hCadj a b hab
    exact ⟨u, mem_glue ha hu, u', mem_glue hb hu', huu'⟩

/-! ## Extracting an index map from Higman domination -/

/-- From `SublistForall₂ R l₁ l₂` we extract a strictly monotone index map matching each
entry of `l₁` with an `R`-larger entry of `l₂`. -/
theorem exists_strictMono_of_sublistForall₂ {α : Type*} {R : α → α → Prop} {d : α}
    {l₁ l₂ : List α} (h : List.SublistForall₂ R l₁ l₂) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ i, i < l₁.length → σ i < l₂.length ∧ R (l₁.getD i d) (l₂.getD (σ i) d) := by
  induction h with
  | nil => exact ⟨id, strictMono_id, by simp⟩
  | @cons a b l₁ l₂ hab _ ih =>
    obtain ⟨σ, hmono, hσ⟩ := ih
    refine ⟨fun i => Nat.casesOn i 0 (fun j => σ j + 1), ?_, ?_⟩
    · apply strictMono_nat_of_lt_succ
      intro n
      cases n with
      | zero => simp
      | succ m => simpa using hmono (Nat.lt_succ_self m)
    · intro i hi
      cases i with
      | zero => simpa using hab
      | succ m =>
        simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
        obtain ⟨h1, h2⟩ := hσ m hi
        simpa [List.getD_cons_succ] using ⟨h1, h2⟩
  | @cons_right b l₁ l₂ _ ih =>
    obtain ⟨σ, hmono, hσ⟩ := ih
    refine ⟨fun i => σ i + 1, fun a b hab => by simpa using hmono hab, ?_⟩
    intro i hi
    obtain ⟨h1, h2⟩ := hσ i hi
    simpa [List.getD_cons_succ] using ⟨h1, h2⟩

/-! ## Isomorphism invariance of the minor relation -/

/-- An isomorphism is in particular a subgraph embedding. -/
theorem Iso.embeds {V : Type u} {W : Type v} {H : SimpleGraph W} {G : SimpleGraph V}
    (e : H ≃g G) : Embeds H G :=
  ⟨e, e.injective, fun _ _ h => e.map_adj_iff.2 h⟩

/-- The minor relation only depends on the isomorphism types of the two graphs. -/
theorem IsMinor.congr {V : Type u} {W : Type v} {V' : Type w} {W' : Type*}
    {H : SimpleGraph W} {G : SimpleGraph V} {H' : SimpleGraph W'} {G' : SimpleGraph V'}
    (eH : H ≃g H') (eG : G' ≃g G) (h : IsMinor H' G') : IsMinor H G :=
  (Iso.embeds eH).isMinor.trans (h.trans (Iso.embeds eG).isMinor)

/-! ## Components: paths and cycles -/

/-- A connected graph of maximum degree at most two: either a path with `n` vertices or a
cycle with `n + 3` vertices. -/
inductive Comp where
  | path (n : ℕ) : Comp
  | cycle (n : ℕ) : Comp
  deriving DecidableEq

/-- The number of vertices of a component. -/
def Comp.size : Comp → ℕ
  | .path n => n
  | .cycle n => n + 3

/-- Adjacency between two positions inside a component: consecutive positions on a path,
respectively consecutive positions modulo the length on a cycle. -/
def Comp.Adj : Comp → ℕ → ℕ → Prop
  | .path _, x, y => x + 1 = y ∨ y + 1 = x
  | .cycle n, x, y => (x + 1) % (n + 3) = y ∨ (y + 1) % (n + 3) = x

theorem Comp.adj_symm : ∀ (c : Comp) {x y : ℕ}, c.Adj x y → c.Adj y x := by
  rintro (n | n) x y h <;> exact h.symm

theorem Comp.adj_irrefl : ∀ (c : Comp) {x : ℕ}, x < c.size → ¬ c.Adj x x := by
  rintro (n | n) x hx h
  · rcases h with h | h <;> omega
  · simp only [Comp.size] at hx
    have : (x + 1) % (n + 3) = x → False := by
      intro hmod
      rcases Nat.lt_or_ge (x + 1) (n + 3) with h1 | h1
      · rw [Nat.mod_eq_of_lt h1] at hmod; omega
      · have hx1 : x + 1 = n + 3 := by omega
        rw [hx1, Nat.mod_self] at hmod; omega
    rcases h with h | h <;> exact this h

/-- On a cycle, `(x+1) % size = y` means either `y = x + 1` or we wrapped around. -/
theorem Comp.cycle_succ_mod {n x y : ℕ} (hx : x < n + 3) (h : (x + 1) % (n + 3) = y) :
    x + 1 = y ∨ (x = n + 2 ∧ y = 0) := by
  rcases Nat.lt_or_ge (x + 1) (n + 3) with h1 | h1
  · left; rw [Nat.mod_eq_of_lt h1] at h; omega
  · right
    have hx1 : x + 1 = n + 3 := by omega
    rw [hx1, Nat.mod_self] at h
    omega

/-- Consecutive positions inside a component are adjacent. -/
theorem Comp.adj_succ (c : Comp) {x : ℕ} (h : x + 1 < c.size) : c.Adj x (x + 1) := by
  cases c with
  | path n => exact Or.inl rfl
  | cycle n => exact Or.inl (Nat.mod_eq_of_lt (by simpa [Comp.size] using h))

/-! ## The domination order on components -/

/-- The domination relation on components: a path is dominated by any longer path and by
any cycle with at least as many vertices, a cycle is dominated by any cycle with at least
as many vertices, and a cycle is dominated by no path.  `Comp.le c d` implies that the
component `c` is a minor of the component `d` (this is what is proved below, in
`Math2.forest_isMinor_of_sublistForall₂`); the converse also holds but is not needed. -/
def Comp.le : Comp → Comp → Prop
  | .path m, .path n => m ≤ n
  | .path m, .cycle n => m ≤ n + 3
  | .cycle _, .path _ => False
  | .cycle m, .cycle n => m ≤ n

theorem Comp.le_refl (c : Comp) : c.le c := by cases c <;> simp [Comp.le]

theorem Comp.le_trans {a b c : Comp} : a.le b → b.le c → a.le c := by
  cases a <;> cases b <;> cases c <;> simp [Comp.le] <;> omega

instance : IsPreorder Comp Comp.le where
  refl := Comp.le_refl
  trans := fun _ _ _ => Comp.le_trans

/-- The size parameter of a component. -/
def Comp.param : Comp → ℕ
  | .path n => n
  | .cycle n => n

/-- On an infinite set of indices, some later term has a larger (or equal) value. -/
theorem exists_le_on_infinite (g : ℕ → ℕ) {T : Set ℕ} (hT : T.Infinite) :
    ∃ i ∈ T, ∃ j ∈ T, i < j ∧ g i ≤ g j := by
  classical
  obtain ⟨i, hiT⟩ := hT.nonempty
  set A : Set ℕ := g '' T with hA
  have hAne : (g i) ∈ A := ⟨i, hiT, rfl⟩
  obtain ⟨i₀, hi₀T, hi₀⟩ : ∃ i₀ ∈ T, g i₀ = sInf A := by
    have : sInf A ∈ A := Nat.sInf_mem ⟨g i, hAne⟩
    obtain ⟨i₀, hi₀T, hi₀⟩ := this
    exact ⟨i₀, hi₀T, hi₀⟩
  obtain ⟨j, hjT, hj⟩ := hT.exists_gt i₀
  refine ⟨i₀, hi₀T, j, hjT, hj, ?_⟩
  rw [hi₀]
  exact Nat.sInf_le ⟨j, hjT, rfl⟩

/-- Components are well-quasi-ordered by `Comp.le`. -/
theorem comp_partiallyWellOrderedOn :
    (Set.univ : Set Comp).PartiallyWellOrderedOn Comp.le := by
  classical
  intro f
  set g : ℕ → Comp := fun n => (f n).1 with hg
  set T : Set ℕ := {n | ∃ k, g n = Comp.cycle k} with hT
  have hsplit : T.Infinite ∨ (Tᶜ).Infinite := by
    rcases Set.finite_or_infinite T with hfin | hinf
    · refine Or.inr ?_
      rcases Set.finite_or_infinite (Tᶜ) with hfin' | hinf'
      · exact absurd (by simpa [Set.union_compl_self] using hfin.union hfin')
          (Set.infinite_univ (α := ℕ))
      · exact hinf'
    · exact Or.inl hinf
  have key : ∃ m n, m < n ∧ Comp.le (g m) (g n) := by
    rcases hsplit with hinf | hinf
    · obtain ⟨i, hi, j, hj, hij, hle⟩ := exists_le_on_infinite (fun n => (g n).param) hinf
      obtain ⟨a, ha⟩ := hi
      obtain ⟨b, hb⟩ := hj
      refine ⟨i, j, hij, ?_⟩
      rw [ha, hb]
      rw [ha, hb] at hle
      simpa [Comp.le, Comp.param] using hle
    · obtain ⟨i, hi, j, hj, hij, hle⟩ := exists_le_on_infinite (fun n => (g n).param) hinf
      have ha : ∃ a, g i = Comp.path a := by
        cases hgi : g i with
        | path a => exact ⟨a, rfl⟩
        | cycle a => exact absurd ⟨a, hgi⟩ hi
      have hb : ∃ b, g j = Comp.path b := by
        cases hgj : g j with
        | path b => exact ⟨b, rfl⟩
        | cycle b => exact absurd ⟨b, hgj⟩ hj
      obtain ⟨a, ha⟩ := ha
      obtain ⟨b, hb⟩ := hb
      refine ⟨i, j, hij, ?_⟩
      rw [ha, hb]
      rw [ha, hb] at hle
      simpa [Comp.le, Comp.param] using hle
  exact key

/-! ## Forests of paths and cycles -/

/-- The component of index `i` of the list `l` (with a junk value out of range). -/
def compAt (l : List Comp) (i : ℕ) : Comp := l.getD i (Comp.path 0)

/-- Vertices of the disjoint union of the components listed in `l`: pairs `(i, x)` with `i`
the index of the component and `x` a position inside it. -/
abbrev ForestVerts (l : List Comp) : Type :=
  {p : ℕ × ℕ // p.1 < l.length ∧ p.2 < (compAt l p.1).size}

/-- `Forest l` is the disjoint union of the components listed in `l`. -/
def Forest (l : List Comp) : SimpleGraph (ForestVerts l) where
  Adj u v := u.1.1 = v.1.1 ∧ (compAt l u.1.1).Adj u.1.2 v.1.2
  symm := by
    rintro u v ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    rw [← h1]
    exact Comp.adj_symm _ h2
  loopless := ⟨by rintro u ⟨-, h⟩; exact Comp.adj_irrefl _ u.2.2 h⟩

/-! Sanity checks on the definition of `Forest`: consecutive positions inside a component
are adjacent, non-consecutive positions of a path are not, the two ends of a cycle are
adjacent, and distinct components are not joined. -/

example : (Forest [Comp.path 3]).Adj ⟨(0, 0), by decide⟩ ⟨(0, 1), by decide⟩ :=
  ⟨rfl, Or.inl rfl⟩

example : ¬ (Forest [Comp.path 3]).Adj ⟨(0, 0), by decide⟩ ⟨(0, 2), by decide⟩ := by
  rintro ⟨-, h | h⟩ <;> simp at h

example : (Forest [Comp.cycle 0]).Adj ⟨(0, 0), by decide⟩ ⟨(0, 2), by decide⟩ :=
  ⟨rfl, Or.inr rfl⟩

example : ¬ (Forest [Comp.path 3, Comp.path 3]).Adj ((⟨(0, 0), by decide⟩ :
    ForestVerts [Comp.path 3, Comp.path 3])) ⟨(1, 0), by decide⟩ := by
  rintro ⟨h, -⟩
  simp at h

/-- A graph is a *forest of paths and cycles* if it is isomorphic to a disjoint union of
finite paths and cycles.  (This class consists exactly of the finite graphs of maximum
degree at most two, but that structure theorem is not formalised here.) -/
def IsPathCycleForest {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ l : List Comp, Nonempty (G ≃g Forest l)

theorem isPathCycleForest_forest (l : List Comp) : IsPathCycleForest (Forest l) :=
  ⟨l, ⟨SimpleGraph.Iso.refl (G := Forest l)⟩⟩

/-- A *linear forest* is a disjoint union of paths. -/
def IsLinearForest {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ l : List ℕ, Nonempty (G ≃g Forest (l.map Comp.path))

theorem IsLinearForest.isPathCycleForest {V : Type u} {G : SimpleGraph V}
    (h : IsLinearForest G) : IsPathCycleForest G := by
  obtain ⟨l, e⟩ := h
  exact ⟨l.map Comp.path, e⟩

/-- An interval of positions inside a single component induces a connected subgraph. -/
theorem connected_interval {l : List Comp} {i a b : ℕ} (hi : i < l.length)
    (hab : a ≤ b) (hb : b < (compAt l i).size) :
    ((Forest l).induce {q : ForestVerts l | q.1.1 = i ∧ a ≤ q.1.2 ∧ q.1.2 ≤ b}).Connected := by
  set S : Set (ForestVerts l) := {q | q.1.1 = i ∧ a ≤ q.1.2 ∧ q.1.2 ≤ b} with hS
  have hlt : ∀ y : ℕ, y ≤ b → y < (compAt l i).size := fun y hy => lt_of_le_of_lt hy hb
  let v : ∀ y : ℕ, a ≤ y → y ≤ b → ↥S := fun y h1 h2 =>
    ⟨⟨(i, y), hi, hlt y h2⟩, rfl, h1, h2⟩
  haveI : Nonempty ↥S := ⟨v a le_rfl hab⟩
  refine SimpleGraph.Connected.mk ?_
  have key : ∀ y (h1 : a ≤ y) (h2 : y ≤ b),
      ((Forest l).induce S).Reachable (v a le_rfl hab) (v y h1 h2) := by
    intro y h1
    induction y, h1 using Nat.le_induction with
    | base => intro h2; exact SimpleGraph.Reachable.refl _
    | succ y hy ih =>
      intro h2
      have hstep : ((Forest l).induce S).Adj (v y hy (by omega)) (v (y + 1) (by omega) h2) :=
        ⟨rfl, Comp.adj_succ _ (hlt (y + 1) h2)⟩
      exact (ih (by omega)).trans hstep.reachable
  rintro ⟨⟨⟨i', x⟩, hx1, hx2⟩, hxS⟩ ⟨⟨⟨j', y⟩, hy1, hy2⟩, hyS⟩
  obtain ⟨hi', hax, hxb⟩ := hxS
  obtain ⟨hj', hay, hyb⟩ := hyS
  simp only at hi' hj'
  subst hi'
  subst hj'
  exact (key x hax hxb).symm.trans (key y hay hyb)

/-! ## Branch sets realizing a component as a minor of a larger component -/

/-- Lower endpoint of the branch set of position `x` of `c` inside `d`. -/
def brLo : Comp → Comp → ℕ → ℕ
  | .cycle m, .cycle n, x => if x = 0 then 0 else (n - m) + x
  | _, _, x => x

/-- Upper endpoint of the branch set of position `x` of `c` inside `d`. -/
def brHi : Comp → Comp → ℕ → ℕ
  | .cycle m, .cycle n, x => if x = 0 then n - m else (n - m) + x
  | _, _, x => x

theorem brLo_le_brHi (c d : Comp) (x : ℕ) : brLo c d x ≤ brHi c d x := by
  cases c <;> cases d <;> simp only [brLo, brHi] <;> first | omega | (split <;> omega)

theorem brHi_lt_size {c d : Comp} (hcd : c.le d) {x : ℕ} (hx : x < c.size) :
    brHi c d x < d.size := by
  cases c with
  | path m =>
    cases d with
    | path n => simp only [brHi]; simp only [Comp.le] at hcd; simp only [Comp.size] at *; omega
    | cycle n => simp only [brHi]; simp only [Comp.le] at hcd; simp only [Comp.size] at *; omega
  | cycle m =>
    cases d with
    | path n => exact absurd hcd (by simp [Comp.le])
    | cycle n =>
      simp only [Comp.le] at hcd
      simp only [Comp.size] at *
      simp only [brHi]
      split <;> omega

theorem brHi_lt_brLo {c d : Comp} (hcd : c.le d) {x x' : ℕ} (h : x < x') :
    brHi c d x < brLo c d x' := by
  cases c with
  | path m => cases d <;> simp only [brHi, brLo] <;> omega
  | cycle m =>
    cases d with
    | path n => exact absurd hcd (by simp [Comp.le])
    | cycle n =>
      simp only [brHi, brLo]
      split <;> split <;> omega

/-- If two positions of `c` are adjacent, then their branch sets in `d` are joined by an
edge of `d`. -/
theorem exists_adj_branch {c d : Comp} (hcd : c.le d) {x x' : ℕ}
    (hx : x < c.size) (hx' : x' < c.size) (hadj : c.Adj x x') :
    ∃ y y', brLo c d x ≤ y ∧ y ≤ brHi c d x ∧ brLo c d x' ≤ y' ∧ y' ≤ brHi c d x' ∧
      d.Adj y y' := by
  cases c with
  | path m =>
    simp only [Comp.Adj] at hadj
    simp only [Comp.size] at hx hx'
    cases d with
    | path n =>
      exact ⟨x, x', le_rfl, le_rfl, le_rfl, le_rfl, by simpa [Comp.Adj, brLo, brHi] using hadj⟩
    | cycle n =>
      simp only [Comp.le] at hcd
      refine ⟨x, x', le_rfl, le_rfl, le_rfl, le_rfl, ?_⟩
      simp only [Comp.Adj]
      rcases hadj with h | h
      · left; rw [← h]; exact Nat.mod_eq_of_lt (by omega)
      · right; rw [← h]; exact Nat.mod_eq_of_lt (by omega)
  | cycle m =>
    cases d with
    | path n => exact absurd hcd (by simp [Comp.le])
    | cycle n =>
      simp only [Comp.le] at hcd
      simp only [Comp.size] at hx hx'
      simp only [Comp.Adj] at hadj
      have main : ∀ z z' : ℕ, z < m + 3 → z' < m + 3 → (z + 1) % (m + 3) = z' →
          ∃ y y', brLo (.cycle m) (.cycle n) z ≤ y ∧ y ≤ brHi (.cycle m) (.cycle n) z ∧
            brLo (.cycle m) (.cycle n) z' ≤ y' ∧ y' ≤ brHi (.cycle m) (.cycle n) z' ∧
            Comp.Adj (.cycle n) y y' := by
        intro z z' hz hz' hmod
        rcases Comp.cycle_succ_mod hz hmod with hcase | ⟨hz2, hz'2⟩
        · refine ⟨(n - m) + z, (n - m) + z', ?_, ?_, ?_, ?_, ?_⟩
          · simp only [brLo]; split <;> omega
          · simp only [brHi]; split <;> omega
          · simp only [brLo]; split <;> omega
          · simp only [brHi]; split <;> omega
          · simp only [Comp.Adj]
            left
            have : (n - m) + z + 1 = (n - m) + z' := by omega
            rw [this]
            exact Nat.mod_eq_of_lt (by omega)
        · subst hz2; subst hz'2
          refine ⟨n + 2, 0, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [brLo]; split <;> omega
          · simp only [brHi]; split <;> omega
          · simp [brLo]
          · simp [brHi]
          · simp only [Comp.Adj]
            left
            have : n + 2 + 1 = n + 3 := by omega
            rw [this, Nat.mod_self]
      rcases hadj with h | h
      · exact main x x' hx hx' h
      · obtain ⟨y', y, h1, h2, h3, h4, h5⟩ := main x' x hx' hx h
        exact ⟨y, y', h3, h4, h1, h2, Comp.adj_symm _ h5⟩

/-! ## Domination of component lists gives a minor -/

theorem forest_isMinor_of_sublistForall₂ {l₁ l₂ : List Comp}
    (h : List.SublistForall₂ Comp.le l₁ l₂) : IsMinor (Forest l₁) (Forest l₂) := by
  obtain ⟨σ, hmono, hσ⟩ :=
    exists_strictMono_of_sublistForall₂ (d := Comp.path 0) h
  have hlen : ∀ u : ForestVerts l₁, σ u.1.1 < l₂.length := fun u => (hσ u.1.1 u.2.1).1
  have hle : ∀ u : ForestVerts l₁, (compAt l₁ u.1.1).le (compAt l₂ (σ u.1.1)) :=
    fun u => (hσ u.1.1 u.2.1).2
  refine ⟨fun u => {q : ForestVerts l₂ | q.1.1 = σ u.1.1 ∧
      brLo (compAt l₁ u.1.1) (compAt l₂ (σ u.1.1)) u.1.2 ≤ q.1.2 ∧
      q.1.2 ≤ brHi (compAt l₁ u.1.1) (compAt l₂ (σ u.1.1)) u.1.2}, ?_, ?_, ?_, ?_⟩
  · intro u
    refine ⟨⟨(σ u.1.1, brLo (compAt l₁ u.1.1) (compAt l₂ (σ u.1.1)) u.1.2), hlen u, ?_⟩,
      rfl, le_rfl, brLo_le_brHi _ _ _⟩
    exact lt_of_le_of_lt (brLo_le_brHi _ _ _) (brHi_lt_size (hle u) u.2.2)
  · intro u
    exact connected_interval (hlen u) (brLo_le_brHi _ _ _) (brHi_lt_size (hle u) u.2.2)
  · rintro u u' hne
    rw [Set.disjoint_left]
    rintro q ⟨hq1, hq2, hq3⟩ ⟨hq1', hq2', hq3'⟩
    have hii : u.1.1 = u'.1.1 := hmono.injective (hq1 ▸ hq1')
    have hxx : u.1.2 ≠ u'.1.2 := by
      intro hcon
      exact hne (Subtype.ext (Prod.ext hii hcon))
    rcases Nat.lt_or_ge u.1.2 u'.1.2 with hlt | hge
    · have := brHi_lt_brLo (c := compAt l₁ u.1.1) (d := compAt l₂ (σ u.1.1)) (hle u) hlt
      rw [← hii] at hq2'
      omega
    · have hlt' : u'.1.2 < u.1.2 := by omega
      have := brHi_lt_brLo (c := compAt l₁ u'.1.1) (d := compAt l₂ (σ u'.1.1)) (hle u') hlt'
      rw [← hii] at this hq3'
      omega
  · rintro ⟨⟨i, x⟩, hu1, hu2⟩ ⟨⟨i', x'⟩, hu1', hu2'⟩ ⟨hidx, hadj⟩
    obtain rfl : i = i' := hidx
    obtain ⟨y, y', hy1, hy2, hy3, hy4, hyadj⟩ :=
      exists_adj_branch (c := compAt l₁ i) (hσ i hu1).2 hu2 hu2' hadj
    exact ⟨⟨(σ i, y), (hσ i hu1).1, lt_of_le_of_lt hy2 (brHi_lt_size (hσ i hu1).2 hu2)⟩,
      ⟨rfl, hy1, hy2⟩,
      ⟨(σ i, y'), (hσ i hu1).1, lt_of_le_of_lt hy4 (brHi_lt_size (hσ i hu1).2 hu2')⟩,
      ⟨rfl, hy3, hy4⟩, ⟨rfl, hyadj⟩⟩

/-! Sanity checks: a small cycle is a minor of a larger one (obtained by contracting a
segment), and a path is a minor of a long enough cycle. -/

example : IsMinor (Forest [Comp.cycle 0]) (Forest [Comp.cycle 5]) :=
  forest_isMinor_of_sublistForall₂
    (List.SublistForall₂.cons (by simp [Comp.le]) List.SublistForall₂.nil)

example : IsMinor (Forest [Comp.path 2]) (Forest [Comp.cycle 0]) :=
  forest_isMinor_of_sublistForall₂
    (List.SublistForall₂.cons (by simp [Comp.le]) List.SublistForall₂.nil)

/-! ## Well-quasi-ordering -/

/-- **Robertson–Seymour, well-quasi-ordering by minors, for graphs of maximum degree at
most two.**

For any sequence `G` of graphs, each of which is a disjoint union of finite paths and
cycles, there are indices `i < j` such that `G i` is a minor of `G j`.  Together with
`Math2.isMinor_refl` and `Math2.IsMinor.trans` this says exactly that the minor relation is
a well-quasi-order on this class of graphs: it is a quasi-order with no infinite antichain
and no infinite strictly descending sequence.

The proof follows the Robertson–Seymour scheme in the case where the graph minor theorem
reduces to Higman's lemma: such a graph is encoded by the list of its components, a
component `c` is a minor of a component `d` exactly when `Comp.le c d`, which is a
well-quasi-order on components, an entrywise domination of one list of components by a
sublist of another produces a minor (using contractions inside cycles), and Higman's lemma
supplies such a domination between two terms of any infinite sequence of lists. -/
theorem robertson_seymour {V : ℕ → Type u} (G : ∀ i, SimpleGraph (V i))
    (hG : ∀ i, IsPathCycleForest (G i)) :
    ∃ i j, i < j ∧ IsMinor (G i) (G j) := by
  choose l hl using hG
  have hpwo :
      {L : List Comp | ∀ x ∈ L, x ∈ (Set.univ : Set Comp)}.PartiallyWellOrderedOn
        (List.SublistForall₂ Comp.le) :=
    Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ Comp.le
      comp_partiallyWellOrderedOn
  obtain ⟨i, j, hij, hsub⟩ := hpwo.exists_lt (f := l) (by simp)
  exact ⟨i, j, hij,
    IsMinor.congr (hl i).some (hl j).some.symm (forest_isMinor_of_sublistForall₂ hsub)⟩

/-- **Well-quasi-ordering by minors for linear forests**, a special case of
`Math2.robertson_seymour`. -/
theorem robertson_seymour_linearForest {V : ℕ → Type u} (G : ∀ i, SimpleGraph (V i))
    (hG : ∀ i, IsLinearForest (G i)) :
    ∃ i j, i < j ∧ IsMinor (G i) (G j) :=
  robertson_seymour G fun i => (hG i).isPathCycleForest

/-! ## The general statement

For the record, here is the statement of the full Robertson–Seymour graph minor theorem for
arbitrary finite graphs.  The theorem proved above, `Math2.robertson_seymour`, is its
restriction to the class of disjoint unions of paths and cycles; the general case is not
proved here. -/
def GraphMinorTheorem : Prop :=
  ∀ {V : ℕ → Type} (_ : ∀ i, Finite (V i)) (G : ∀ i, SimpleGraph (V i)),
    ∃ i j, i < j ∧ IsMinor (G i) (G j)

end Math2

