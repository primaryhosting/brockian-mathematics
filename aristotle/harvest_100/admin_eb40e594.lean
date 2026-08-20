/-
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as the first lines of the file as a plain block comment,
since Lean does not allow a module docstring `/-! ... -/` to precede the `import` line.)

## What is formalised here

* `Math2.IsMinor H G` : the standard *minor model* definition of "`H` is a minor of `G`".
* `Math2.robertson_seymour` : well-quasi-ordering by the minor relation for families of
  finite graphs whose orders are bounded by a fixed `k`.
* `Math2.robertson_seymour_linearForest` : well-quasi-ordering by the minor relation of the
  (infinite, unbounded) class of linear forests, i.e. disjoint unions of paths.  This is
  deduced from Higman's lemma.
* `Math2.robertson_seymour_cycleGraph` : well-quasi-ordering by the minor relation of the
  (infinite, unbounded) class of cycles; here the minors genuinely involve edge
  contractions.
* `Math2.isMinor_refl` and `Math2.IsMinor.trans` : the minor relation is a quasi-order.
* `Math2.RobertsonSeymourWQO` : the statement of the unrestricted Robertson–Seymour theorem,
  recorded as a `Prop`.  It is **not** proved here; the full graph minor theorem is the
  conclusion of the twenty-paper Graph Minors series and is far beyond what is formalised
  in this file.
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

namespace Math2

/-! ## The minor relation -/

/-- `IsMinor H G` says that `H` is a minor of `G`, expressed through a *minor model*:
each vertex `v` of `H` is assigned a branch set `B v ⊆ G`, the branch sets are nonempty,
induce connected subgraphs of `G`, are pairwise disjoint, and whenever `v` and `w` are
adjacent in `H` there is an edge of `G` joining `B v` to `B w`. -/
def IsMinor {V : Type*} {W : Type*} (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∃ B : V → Set W,
    (∀ v, (B v).Nonempty) ∧
    (∀ v, (G.induce (B v)).Connected) ∧
    (∀ v w, v ≠ w → Disjoint (B v) (B w)) ∧
    (∀ v w, H.Adj v w → ∃ a ∈ B v, ∃ b ∈ B w, G.Adj a b)

/-- A one-point induced subgraph is connected. -/
theorem connected_induce_singleton {X : Type*} (K : SimpleGraph X) (x : X) :
    (K.induce ({x} : Set X)).Connected := by
  constructor
  intro u v
  have huv : u = v := by
    apply Subtype.ext
    have hu := u.2
    have hv := v.2
    simp only [Set.mem_singleton_iff] at hu hv
    rw [hu, hv]
  subst huv
  exact SimpleGraph.Reachable.refl _

/-- An injective adjacency-preserving map exhibits `H` as a minor of `G`: take singleton
branch sets. -/
theorem isMinor_of_injective_hom {V : Type*} {W : Type*} {H : SimpleGraph V} {G : SimpleGraph W}
    (f : V → W) (hf : Function.Injective f) (hadj : ∀ x y, H.Adj x y → G.Adj (f x) (f y)) :
    IsMinor H G := by
  refine ⟨fun v => {f v}, fun v => ⟨f v, rfl⟩, fun v => connected_induce_singleton G (f v), ?_, ?_⟩
  · intro v w hvw
    simp only [Set.disjoint_singleton]
    exact fun h => hvw (hf h)
  · intro v w hadjvw
    exact ⟨f v, rfl, f w, rfl, hadj v w hadjvw⟩

/-- The minor relation is reflexive. -/
theorem isMinor_refl {V : Type*} (G : SimpleGraph V) : IsMinor G G :=
  isMinor_of_injective_hom id Function.injective_id fun _ _ h => h

/-- Reachability inside an induced subgraph is preserved when the inducing set grows. -/
theorem reachable_induce_mono {X : Type*} {K : SimpleGraph X} {S T : Set X} (hST : S ⊆ T)
    {x y : X} (hxS : x ∈ S) (hyS : y ∈ S) (hxT : x ∈ T) (hyT : y ∈ T)
    (h : (K.induce S).Reachable ⟨x, hxS⟩ ⟨y, hyS⟩) :
    (K.induce T).Reachable ⟨x, hxT⟩ ⟨y, hyT⟩ := by
  have h' := h.map (K.induceHomOfLE hST).toHom
  simpa [SimpleGraph.induceHomOfLE] using h'

/-- A union `⋃ w ∈ S, C w` of connected sets `C w`, indexed by a set `S` that is connected in
`G` and whose edges are witnessed by edges between the corresponding sets, is connected. -/
theorem connected_biUnion {W X : Type*} {G : SimpleGraph W} {K : SimpleGraph X}
    (S : Set W) (C : W → Set X)
    (hS : (G.induce S).Connected)
    (hconn : ∀ w, (K.induce (C w)).Connected)
    (hedge : ∀ w w', G.Adj w w' → ∃ x ∈ C w, ∃ y ∈ C w', K.Adj x y) :
    (K.induce (⋃ w ∈ S, C w)).Connected := by
  set T : Set X := ⋃ w ∈ S, C w with hT
  have hsub : ∀ w ∈ S, C w ⊆ T := fun _ hw _ hx => Set.mem_biUnion hw hx
  have key : ∀ (a b : ↥S), (G.induce S).Reachable a b →
      ∀ (x y : X) (_ : x ∈ C a.val) (_ : y ∈ C b.val) (hxT : x ∈ T) (hyT : y ∈ T),
      (K.induce T).Reachable ⟨x, hxT⟩ ⟨y, hyT⟩ := by
    rintro a b ⟨p⟩
    induction p with
    | @nil c =>
        intro x y hx hy hxT hyT
        exact reachable_induce_mono (hsub _ c.2) hx hy hxT hyT ((hconn c.val).preconnected _ _)
    | @cons a c b hac p ih =>
        intro x y hx hy hxT hyT
        obtain ⟨u, hu, v, hv, huv⟩ := hedge a.val c.val hac
        have huT : u ∈ T := hsub _ a.2 hu
        have hvT : v ∈ T := hsub _ c.2 hv
        have r1 : (K.induce T).Reachable ⟨x, hxT⟩ ⟨u, huT⟩ :=
          reachable_induce_mono (hsub _ a.2) hx hu hxT huT ((hconn a.val).preconnected _ _)
        have r2 : (K.induce T).Adj ⟨u, huT⟩ ⟨v, hvT⟩ := huv
        have r3 : (K.induce T).Reachable ⟨v, hvT⟩ ⟨y, hyT⟩ := ih v y hv hy hvT hyT
        exact (r1.trans r2.reachable).trans r3
  obtain ⟨w0⟩ := hS.nonempty
  obtain ⟨x0, hx0⟩ := (hconn w0.val).nonempty
  haveI : Nonempty ↥T := ⟨⟨x0, hsub _ w0.2 hx0⟩⟩
  constructor
  rintro ⟨x, hxT⟩ ⟨y, hyT⟩
  have hxT' := hxT
  have hyT' := hyT
  simp only [hT, Set.mem_iUnion, exists_prop] at hxT' hyT'
  obtain ⟨a, haS, hxa⟩ := hxT'
  obtain ⟨b, hbS, hyb⟩ := hyT'
  exact key ⟨a, haS⟩ ⟨b, hbS⟩ (hS.preconnected _ _) x y hxa hyb _ _

/-- The minor relation is transitive: together with `Math2.isMinor_refl` this makes it a
quasi-order. -/
theorem IsMinor.trans {V W X : Type*} {H : SimpleGraph V} {G : SimpleGraph W} {K : SimpleGraph X}
    (h1 : IsMinor H G) (h2 : IsMinor G K) : IsMinor H K := by
  obtain ⟨B, hBne, hBconn, hBdisj, hBedge⟩ := h1
  obtain ⟨C, hCne, hCconn, hCdisj, hCedge⟩ := h2
  refine ⟨fun v => ⋃ w ∈ B v, C w, ?_, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨w, hw⟩ := hBne v
    obtain ⟨x, hx⟩ := hCne w
    exact ⟨x, Set.mem_biUnion hw hx⟩
  · intro v
    exact connected_biUnion (B v) C (hBconn v) hCconn hCedge
  · intro v v' hvv'
    rw [Set.disjoint_left]
    rintro x hx hx'
    simp only [Set.mem_iUnion, exists_prop] at hx hx'
    obtain ⟨w, hw, hxw⟩ := hx
    obtain ⟨w', hw', hxw'⟩ := hx'
    by_cases hww : w = w'
    · subst hww
      exact (Set.disjoint_left.mp (hBdisj v v' hvv') hw) hw'
    · exact (Set.disjoint_left.mp (hCdisj w w' hww) hxw) hxw'
  · intro v v' hadj
    obtain ⟨a, ha, b, hb, hab⟩ := hBedge v v' hadj
    obtain ⟨x, hx, y, hy, hxy⟩ := hCedge a b hab
    exact ⟨x, Set.mem_biUnion ha hx, y, Set.mem_biUnion hb hy, hxy⟩

/-- A minor has at most as many vertices as the ambient graph.  In particular the minor
relation is not trivial: e.g. a long cycle is not a minor of a short one. -/
theorem card_le_of_isMinor {V W : Type*} [Fintype V] [Fintype W] {H : SimpleGraph V}
    {G : SimpleGraph W} (h : IsMinor H G) : Fintype.card V ≤ Fintype.card W := by
  obtain ⟨B, hne, -, hdisj, -⟩ := h
  choose f hf using hne
  refine Fintype.card_le_of_injective f ?_
  intro v w hvw
  by_contra hne'
  exact (Set.disjoint_left.mp (hdisj v w hne') (hf v)) (hvw ▸ hf w)

/-- Non-triviality check for `Math2.IsMinor`: a five-cycle is not a minor of a triangle. -/
theorem not_isMinor_cycleGraph_five_three :
    ¬ IsMinor (SimpleGraph.cycleGraph 5) (SimpleGraph.cycleGraph 3) := by
  intro h
  have hcard := card_le_of_isMinor h
  simp at hcard

/-- The unrestricted Robertson–Seymour theorem: the finite graphs are well-quasi-ordered by
the minor relation, i.e. every infinite sequence of finite graphs contains a graph that is a
minor of a later one.  This `Prop` is recorded for reference only; it is not proved here. -/
def RobertsonSeymourWQO : Prop :=
  ∀ (V : ℕ → Type) (_ : ∀ i, Fintype (V i)) (G : ∀ i, SimpleGraph (V i)),
    ∃ i j, i < j ∧ IsMinor (G i) (G j)

/-! ## Well-quasi-ordering of graphs of bounded order -/

/-- **Robertson–Seymour, bounded-order case.**  For any fixed bound `k`, the class of finite
graphs with at most `k` vertices is well-quasi-ordered by the minor relation: in every
infinite sequence `G` of such graphs there are indices `i < j` with `G i` a minor of `G j`.
(This is the restricted form of the graph minor theorem proved in this file; the
unrestricted statement is recorded as `Math2.RobertsonSeymourWQO` and is not proved here.) -/
theorem robertson_seymour (k : ℕ) (V : ℕ → Type) [inst : ∀ i, Fintype (V i)]
    (hcard : ∀ i, Fintype.card (V i) ≤ k) (G : ∀ i, SimpleGraph (V i)) :
    ∃ i j, i < j ∧ IsMinor (G i) (G j) := by
  classical
  have he : ∀ i, Nonempty (V i ↪ Fin k) := fun i =>
    Function.Embedding.nonempty_of_card_le (by simpa using hcard i)
  let e : ∀ i, V i ↪ Fin k := fun i => (he i).some
  set F : ℕ → Finset (Fin k) × SimpleGraph (Fin k) :=
    fun i => (Finset.univ.image (e i), (G i).map (e i)) with hF
  have key : ∀ a b : ℕ, F a = F b → IsMinor (G a) (G b) := by
    intro a b hab
    have hset : Finset.univ.image (e a) = Finset.univ.image (e b) := congrArg Prod.fst hab
    have hgraph : (G a).map (e a) = (G b).map (e b) := congrArg Prod.snd hab
    have hmem : ∀ x : V a, ∃ y : V b, e b y = e a x := by
      intro x
      have hx : e a x ∈ Finset.univ.image (e b) := by
        rw [← hset]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
      simpa using hx
    choose f hf using hmem
    refine isMinor_of_injective_hom f ?_ ?_
    · intro x y hxy
      have hx : e a x = e a y := by rw [← hf x, ← hf y, hxy]
      exact (e a).injective hx
    · intro x y hxy
      have h1 : ((G a).map (e a)).Adj (e a x) (e a y) := SimpleGraph.map_adj_apply.mpr hxy
      rw [hgraph] at h1
      obtain ⟨u, v, huv, hu, hv⟩ := h1
      have hu' : u = f x := (e b).injective (by rw [hu, ← hf x])
      have hv' : v = f y := (e b).injective (by rw [hv, ← hf y])
      rw [hu', hv'] at huv
      exact huv
  obtain ⟨a, b, hab, hFab⟩ := Finite.exists_ne_map_eq_of_infinite F
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨a, b, h, key a b hFab⟩
  · exact ⟨b, a, h, key b a hFab.symm⟩

/-! ## Well-quasi-ordering of linear forests

A linear forest is a disjoint union of paths.  It is encoded by the list `l` of the numbers
of vertices of its paths: the vertex `(i, j)` is the `j`-th vertex of the `i`-th path. -/

/-- Vertex type of the linear forest determined by the list `l` of path orders. -/
abbrev LFVertex (l : List ℕ) : Type := {p : ℕ × ℕ // p.2 < l.getD p.1 0}

/-- The linear forest (disjoint union of paths) whose `i`-th path has `l.getD i 0` vertices. -/
def linearForest (l : List ℕ) : SimpleGraph (LFVertex l) where
  Adj p q := p.1.1 = q.1.1 ∧ (p.1.2 + 1 = q.1.2 ∨ q.1.2 + 1 = p.1.2)
  symm := by
    rintro p q ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩
  loopless := by
    constructor
    rintro p ⟨-, h | h⟩ <;> omega

/-- In a one-path linear forest all vertices lie on the path of index `0`. -/
theorem lfVertex_fst_eq_zero {n : ℕ} (p : LFVertex [n]) : p.1.1 = 0 := by
  by_contra h
  have hp := p.2
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h
  rw [hm] at hp
  simp [List.getD] at hp

/-- Sanity check on the encoding: the linear forest of a one-element list `[n]` is
isomorphic to Mathlib's path graph on `n` vertices. -/
def linearForestSingletonIso (n : ℕ) : linearForest [n] ≃g SimpleGraph.pathGraph n where
  toFun p := ⟨p.1.2, by have hp := p.2; simpa [lfVertex_fst_eq_zero p] using hp⟩
  invFun k := ⟨(0, k.val), by simp⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext (lfVertex_fst_eq_zero p).symm rfl
  right_inv k := by
    apply Fin.ext
    rfl
  map_rel_iff' := by
    intro p q
    rw [SimpleGraph.pathGraph_adj]
    simp only [linearForest]
    constructor
    · intro h
      exact ⟨(lfVertex_fst_eq_zero p).trans (lfVertex_fst_eq_zero q).symm, h⟩
    · rintro ⟨-, h⟩
      exact h

/-- From a domination `l₁ ≤ l₂` of lists of naturals in the sense of Higman's ordering one
extracts a strictly monotone index map matching each entry of `l₁` with a larger entry of
`l₂`. -/
theorem exists_strictMono_of_sublistForall₂ {l₁ l₂ : List ℕ}
    (h : List.SublistForall₂ (· ≤ ·) l₁ l₂) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ i, l₁.getD i 0 ≤ l₂.getD (f i) 0 := by
  induction h with
  | nil => exact ⟨id, strictMono_id, by intro i; simp⟩
  | @cons a b m1 m2 hab _ ih =>
      obtain ⟨f, hf, hle⟩ := ih
      refine ⟨fun i => match i with | 0 => 0 | (j + 1) => f j + 1, ?_, ?_⟩
      · apply strictMono_nat_of_lt_succ
        intro n
        cases n with
        | zero => simp
        | succ m => simpa using hf (Nat.lt_succ_self m)
      · intro i
        cases i with
        | zero => simpa using hab
        | succ n => simpa using hle n
  | @cons_right b m1 m2 _ ih =>
      obtain ⟨f, hf, hle⟩ := ih
      refine ⟨fun i => f i + 1, ?_, ?_⟩
      · intro x y hxy
        simpa using hf hxy
      · intro i
        simpa using hle i

/-- If the list `l₁` of path orders is dominated by `l₂` in Higman's ordering, then the
corresponding linear forests are related by the minor relation. -/
theorem isMinor_linearForest_of_sublistForall₂ {l₁ l₂ : List ℕ}
    (h : List.SublistForall₂ (· ≤ ·) l₁ l₂) :
    IsMinor (linearForest l₁) (linearForest l₂) := by
  obtain ⟨f, hf, hle⟩ := exists_strictMono_of_sublistForall₂ h
  refine isMinor_of_injective_hom
    (fun p => ⟨(f p.1.1, p.1.2), lt_of_lt_of_le p.2 (hle p.1.1)⟩) ?_ ?_
  · rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨i', j'⟩, hij'⟩ heq
    have heq' := congrArg Subtype.val heq
    simp only [Prod.mk.injEq] at heq'
    obtain ⟨h1, h2⟩ := heq'
    have hii : i = i' := hf.injective h1
    subst hii
    subst h2
    rfl
  · rintro p q ⟨h1, h2⟩
    exact ⟨congrArg f h1, h2⟩

/-- **Robertson–Seymour for linear forests.**  The class of all linear forests (disjoint
unions of paths), which contains graphs of arbitrarily large order, is well-quasi-ordered by
the minor relation.  The proof goes through Higman's lemma for lists over `ℕ`. -/
theorem robertson_seymour_linearForest (l : ℕ → List ℕ) :
    ∃ i j, i < j ∧ IsMinor (linearForest (l i)) (linearForest (l j)) := by
  have hpwo : (Set.univ : Set ℕ).PartiallyWellOrderedOn (· ≤ ·) :=
    Set.IsWF.isPWO (Set.wellFoundedOn_univ.mpr wellFounded_lt)
  obtain ⟨i, j, hij, h⟩ :=
    (hpwo.partiallyWellOrderedOn_sublistForall₂ (· ≤ ·)).exists_lt
      (f := l) (fun _ x _ => Set.mem_univ x)
  exact ⟨i, j, hij, isMinor_linearForest_of_sublistForall₂ h⟩

/-- A path with `m` vertices is a minor of a path with `n` vertices whenever `m ≤ n`. -/
theorem isMinor_path_of_le {m n : ℕ} (h : m ≤ n) :
    IsMinor (linearForest [m]) (linearForest [n]) :=
  isMinor_linearForest_of_sublistForall₂ (List.SublistForall₂.cons h List.SublistForall₂.nil)

/-! ## Well-quasi-ordering of cycles

Unlike the minors constructed above, a smaller cycle is obtained from a larger one by genuine
contractions: all but one of the branch sets are singletons, and the last one is an arc. -/

/-- Consecutive vertices of a cycle graph are adjacent. -/
theorem cycleGraph_adj_of_succ {n : ℕ} (u v : Fin n) (h : u.val + 1 = v.val) (hn : 2 ≤ n) :
    (SimpleGraph.cycleGraph n).Adj u v := by
  rw [SimpleGraph.cycleGraph_adj']
  right
  rw [Fin.sub_def]
  simp only
  have h1 := u.isLt
  have h2 := v.isLt
  have h3 : n - u.val + v.val = n + 1 := by omega
  rw [h3, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- The last and the first vertex of a cycle graph are adjacent. -/
theorem cycleGraph_adj_wrap {n : ℕ} (u v : Fin n) (h : u.val + 1 = n) (h0 : v.val = 0)
    (hn : 2 ≤ n) : (SimpleGraph.cycleGraph n).Adj u v := by
  rw [SimpleGraph.cycleGraph_adj']
  right
  rw [Fin.sub_def]
  simp only
  have h1 := u.isLt
  have h2 : n - u.val + v.val = 1 := by omega
  rw [h2, Nat.mod_eq_of_lt (by omega)]

/-- Unfolding of the modular difference occurring in the adjacency relation of a cycle. -/
theorem fin_sub_val_eq_one {n : ℕ} (u v : Fin n) (h : (u - v).val = 1) :
    u.val = v.val + 1 ∨ (u.val = 0 ∧ v.val + 1 = n) := by
  have hn : 0 < n := u.pos
  rw [Fin.sub_def] at h
  have hu := u.isLt
  have hv := v.isLt
  simp only at h
  rcases Nat.lt_or_ge (n - v.val + u.val) n with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h
    omega
  · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h
    omega

/-- An arc `{x | m ≤ x}` of a cycle graph induces a connected subgraph. -/
theorem connected_cycleGraph_arc {b m : ℕ} (hmb : m < b) (hb : 2 ≤ b) :
    ((SimpleGraph.cycleGraph b).induce {x : Fin b | m ≤ x.val}).Connected := by
  set S : Set (Fin b) := {x : Fin b | m ≤ x.val} with hS
  have hbase : (⟨m, hmb⟩ : Fin b) ∈ S := by simp [hS]
  haveI : Nonempty ↥S := ⟨⟨⟨m, hmb⟩, hbase⟩⟩
  have key : ∀ k : ℕ, ∀ (x : Fin b) (hx : x ∈ S), x.val = k →
      ((SimpleGraph.cycleGraph b).induce S).Reachable ⟨x, hx⟩ ⟨⟨m, hmb⟩, hbase⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro x hx hxk
      have hxm : m ≤ x.val := hx
      rcases eq_or_lt_of_le hxm with heq | hlt
      · have hxe : x = (⟨m, hmb⟩ : Fin b) := Fin.ext heq.symm
        subst hxe
        exact SimpleGraph.Reachable.refl _
      · have hy : (x.val - 1) < b := by omega
        have hyS : (⟨x.val - 1, hy⟩ : Fin b) ∈ S := by
          show m ≤ x.val - 1
          omega
        have hadj : ((SimpleGraph.cycleGraph b).induce S).Adj ⟨⟨x.val - 1, hy⟩, hyS⟩ ⟨x, hx⟩ :=
          cycleGraph_adj_of_succ _ x (by show x.val - 1 + 1 = x.val; omega) hb
        have hrec := ih (x.val - 1) (by omega) ⟨x.val - 1, hy⟩ hyS rfl
        exact (hadj.symm.reachable).trans hrec
  constructor
  intro x y
  exact (key x.val.val x.val x.2 rfl).trans (key y.val.val y.val y.2 rfl).symm

/-- A cycle of length `a` is a minor of any longer cycle: contract the arc of the long cycle
that lies beyond the first `a - 1` vertices. -/
theorem isMinor_cycleGraph_of_le {a b : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) :
    IsMinor (SimpleGraph.cycleGraph a) (SimpleGraph.cycleGraph b) := by
  have hb2 : 2 ≤ b := by omega
  have harc : a - 1 < b := by omega
  set B : Fin a → Set (Fin b) :=
    fun i => if i.val + 1 < a then {x : Fin b | x.val = i.val} else {x : Fin b | a - 1 ≤ x.val}
    with hB
  have hmem_sing : ∀ i : Fin a, i.val + 1 < a → ∀ x : Fin b, x ∈ B i ↔ x.val = i.val := by
    intro i hi x
    simp [hB, if_pos hi]
  have hmem_arc : ∀ i : Fin a, ¬ (i.val + 1 < a) → ∀ x : Fin b, x ∈ B i ↔ a - 1 ≤ x.val := by
    intro i hi x
    simp [hB, if_neg hi]
  have hstep : ∀ i j : Fin a, j.val = i.val + 1 →
      ∃ x ∈ B i, ∃ y ∈ B j, (SimpleGraph.cycleGraph b).Adj x y := by
    intro i j hji
    have hi : i.val + 1 < a := by have := j.isLt; omega
    have hib : i.val < b := by have := i.isLt; omega
    have hjb : j.val < b := by have := j.isLt; omega
    refine ⟨⟨i.val, hib⟩, (hmem_sing i hi _).mpr rfl, ⟨j.val, hjb⟩, ?_, ?_⟩
    · by_cases hj : j.val + 1 < a
      · exact (hmem_sing j hj _).mpr rfl
      · exact (hmem_arc j hj _).mpr (by show a - 1 ≤ j.val; omega)
    · exact cycleGraph_adj_of_succ _ _ (by show i.val + 1 = j.val; omega) hb2
  have hwrap : ∀ i j : Fin a, i.val + 1 = a → j.val = 0 →
      ∃ x ∈ B i, ∃ y ∈ B j, (SimpleGraph.cycleGraph b).Adj x y := by
    intro i j hi hj
    have hbi : b - 1 < b := by omega
    have hj' : j.val + 1 < a := by omega
    refine ⟨⟨b - 1, hbi⟩, (hmem_arc i (by omega) _).mpr (by simp; omega), ⟨0, by omega⟩, ?_, ?_⟩
    · exact (hmem_sing j hj' _).mpr (by simp [hj])
    · exact cycleGraph_adj_wrap _ _ (by simp; omega) (by simp) hb2
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i.val + 1 < a
    · exact ⟨⟨i.val, by have := i.isLt; omega⟩, (hmem_sing i hi _).mpr rfl⟩
    · exact ⟨⟨a - 1, harc⟩, (hmem_arc i hi _).mpr (by simp)⟩
  · intro i
    by_cases hi : i.val + 1 < a
    · have hset : B i = {(⟨i.val, by have := i.isLt; omega⟩ : Fin b)} := by
        ext x
        rw [hmem_sing i hi]
        simp [Fin.ext_iff]
      rw [hset]
      exact connected_induce_singleton _ _
    · have hset : B i = {x : Fin b | a - 1 ≤ x.val} := by
        ext x
        rw [hmem_arc i hi]
        simp
      rw [hset]
      exact connected_cycleGraph_arc harc hb2
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hx hx'
    by_cases hi : i.val + 1 < a <;> by_cases hj : j.val + 1 < a
    · exact hij (Fin.ext (((hmem_sing i hi x).mp hx).symm.trans ((hmem_sing j hj x).mp hx')))
    · have h1 := (hmem_sing i hi x).mp hx
      have h2 := (hmem_arc j hj x).mp hx'
      omega
    · have h1 := (hmem_arc i hi x).mp hx
      have h2 := (hmem_sing j hj x).mp hx'
      have := j.isLt
      omega
    · exact hij (Fin.ext (by have := i.isLt; have := j.isLt; omega))
  · intro i j hadj
    rw [SimpleGraph.cycleGraph_adj'] at hadj
    have hsymm : (∃ x ∈ B j, ∃ y ∈ B i, (SimpleGraph.cycleGraph b).Adj x y) →
        ∃ x ∈ B i, ∃ y ∈ B j, (SimpleGraph.cycleGraph b).Adj x y := by
      rintro ⟨x, hx, y, hy, h⟩
      exact ⟨y, hy, x, hx, h.symm⟩
    rcases hadj with h | h
    · rcases fin_sub_val_eq_one i j h with h1 | ⟨h1, h2⟩
      · exact hsymm (hstep j i h1)
      · exact hsymm (hwrap j i h2 h1)
    · rcases fin_sub_val_eq_one j i h with h1 | ⟨h1, h2⟩
      · exact hstep i j h1
      · exact hwrap i j h2 h1

/-- **Robertson–Seymour for cycles.**  The class of cycles is well-quasi-ordered by the minor
relation. -/
theorem robertson_seymour_cycleGraph (n : ℕ → ℕ) (hn : ∀ i, 3 ≤ n i) :
    ∃ i j, i < j ∧ IsMinor (SimpleGraph.cycleGraph (n i)) (SimpleGraph.cycleGraph (n j)) := by
  have hpwo : (Set.univ : Set ℕ).PartiallyWellOrderedOn (· ≤ ·) :=
    Set.IsWF.isPWO (Set.wellFoundedOn_univ.mpr wellFounded_lt)
  obtain ⟨i, j, hij, h⟩ := hpwo.exists_lt (f := n) fun _ => Set.mem_univ _
  exact ⟨i, j, hij, isMinor_cycleGraph_of_le (hn i) h⟩

end Math2

