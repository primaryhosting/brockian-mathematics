import Mathlib
import RequestProject.ReingoldSlL

/-!
## Existence of universal exploration sequences

The hypothesis `CS.HasPolyUES` used in `RequestProject/ReingoldSlL.lean` asks for universal
exploration sequences of *polynomial* length; producing such short sequences is the deep part
of Reingold's theorem and is not formalised.  Here we prove, unconditionally, that universal
exploration sequences of *some* finite length always exist (`CS.exists_ues`).  This shows that
the notion is satisfiable — the only missing ingredient in `CS.HasPolyUES` is the polynomial
length bound.
-/

set_option autoImplicit false

namespace CS

namespace RotGraph

variable {n d : ℕ}

/-- The walk of length `k` only depends on the first `k` offsets. -/
lemma walk_congr (G : RotGraph n d) (seq seq' : ℕ → Fin d) (p : Fin n × Fin d) (k : ℕ)
    (h : ∀ j < k, seq j = seq' j) : G.walk seq p k = G.walk seq' p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [walk_succ, walk_succ, ih (fun j hj => h j (by omega)), h k (by omega)]

/-- Splitting a walk into two consecutive stretches. -/
lemma walk_add (G : RotGraph n d) (seq : ℕ → Fin d) (p : Fin n × Fin d) (a b : ℕ) :
    G.walk seq p (a + b) = G.walk (fun j => seq (a + j)) (G.walk seq p a) b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [← Nat.add_assoc, walk_succ, walk_succ, ih]

/-- Reachability in a rotation graph is symmetric. -/
lemma reachable_symm (G : RotGraph n d) {u v : Fin n} (h : G.Reachable u v) : G.Reachable v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (G.adj_symm hbc) ih

end RotGraph

/-- Any label can be reached from any other by adding a suitable offset. -/
lemma exists_addOff {d : ℕ} (i e : Fin d) : ∃ a : Fin d, addOff i a = e := by
  have hd : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  refine ⟨⟨(e.1 + d - i.1) % d, Nat.mod_lt _ hd⟩, ?_⟩
  apply Fin.ext
  show (i.1 + (e.1 + d - i.1) % d) % d = e.1
  have h1 : (i.1 + (e.1 + d - i.1) % d) % d = (i.1 + (e.1 + d - i.1)) % d := by
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod]
    conv_rhs => rw [Nat.add_mod]
  rw [h1, show i.1 + (e.1 + d - i.1) = e.1 + d by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt e.isLt]

variable {n d : ℕ}

/-- **Steering.**  Three exploration steps suffice to traverse any prescribed edge `e` at the
current vertex: the first step is forced, the second one walks back along it, and the third
one takes the edge `e`. -/
lemma exists_steer (G : RotGraph n d) (p : Fin n × Fin d) (e : Fin d) :
    ∃ w : ℕ → Fin d, (G.walk w p 3).1 = (G.rot (p.1, e)).1 := by
  obtain ⟨a₁, ha₁⟩ := exists_addOff (G.rot p).2 (G.rot p).2
  obtain ⟨a₂, ha₂⟩ := exists_addOff p.2 e
  refine ⟨fun j => if j = 1 then a₂ else a₁, ?_⟩
  have h1 : G.walk (fun j => if j = 1 then a₂ else a₁) p 1 = G.rot p := by
    show G.stepE _ p = _
    simp only [RotGraph.stepE, if_neg (by norm_num : ¬ (0 : ℕ) = 1), ha₁]
  have h2 : G.walk (fun j => if j = 1 then a₂ else a₁) p 2 = (p.1, e) := by
    show G.stepE _ (G.walk (fun j => if j = 1 then a₂ else a₁) p 1) = _
    rw [h1]
    show ((G.rot (G.rot p)).1, addOff (G.rot (G.rot p)).2 (if (1 : ℕ) = 1 then a₂ else a₁))
        = (p.1, e)
    rw [if_pos rfl, G.rot_involutive p, ha₂]
  show (G.stepE _ (G.walk (fun j => if j = 1 then a₂ else a₁) p 2)).1 = _
  rw [h2]
  rfl

/-- From any state, some finite sequence of offsets drives the exploration walk to any vertex
of the connected component. -/
lemma exists_offsets_reach (G : RotGraph n d) (t : Fin n) {v : Fin n} (hv : G.Reachable v t) :
    ∀ p : Fin n × Fin d, p.1 = v →
      ∃ (L : ℕ) (w : ℕ → Fin d), ∃ k ≤ L, (G.walk w p k).1 = t := by
  induction hv using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun p hp => ⟨0, fun _ => p.2, 0, le_refl 0, hp⟩
  | head hac _ ih =>
      rename_i x c _
      intro p hp
      obtain ⟨e, he⟩ : ∃ e : Fin d, (G.rot (p.1, e)).1 = c := by
        rw [hp]; exact hac
      obtain ⟨w₀, hw₀⟩ := exists_steer G p e
      obtain ⟨L₁, w₁, k₁, hk₁, hw₁⟩ := ih (G.walk w₀ p 3) (by rw [hw₀]; exact he)
      refine ⟨3 + L₁, fun j => if j < 3 then w₀ j else w₁ (j - 3), 3 + k₁, by omega, ?_⟩
      rw [G.walk_add]
      have hpre : G.walk (fun j => if j < 3 then w₀ j else w₁ (j - 3)) p 3 = G.walk w₀ p 3 :=
        G.walk_congr _ _ p 3 (fun j hj => by simp [hj])
      rw [hpre]
      have hsuf : (fun j => if 3 + j < 3 then w₀ (3 + j) else w₁ (3 + j - 3)) = w₁ := by
        funext j
        simp
      rw [hsuf]
      exact hw₁

variable [NeZero d]

/-- Greedy construction: for any finite list of instances there is a single offset sequence
solving all of them. -/
lemma exists_seq_for_list (l : List (RotGraph n d × Fin n × Fin n)) :
    ∃ (T : ℕ) (seq : ℕ → Fin d), ∀ x ∈ l, x.1.Reachable x.2.1 x.2.2 →
      ∃ k ≤ T, (x.1.walk seq (x.2.1, 0) k).1 = x.2.2 := by
  induction l with
  | nil => exact ⟨0, fun _ => 0, by simp⟩
  | cons x l ih =>
      obtain ⟨T, seq, hseq⟩ := ih
      by_cases hx : x.1.Reachable x.2.1 x.2.2
      · set G := x.1
        set s := x.2.1
        set t := x.2.2
        set p := G.walk seq (s, 0) T with hp
        have hreach : G.Reachable p.1 t :=
          (G.reachable_symm (by simpa [hp] using G.walk_reachable seq (s, 0) T)).trans hx
        obtain ⟨L, w, k, hk, hw⟩ := exists_offsets_reach G t hreach p rfl
        refine ⟨T + L, fun j => if j < T then seq j else w (j - T), ?_⟩
        intro y hy hyreach
        rcases List.mem_cons.1 hy with rfl | hy'
        · refine ⟨T + k, by omega, ?_⟩
          rw [G.walk_add]
          have hpre : G.walk (fun j => if j < T then seq j else w (j - T)) (s, 0) T
              = G.walk seq (s, 0) T := G.walk_congr _ _ _ T (fun j hj => by simp [hj])
          rw [hpre, ← hp]
          have hsuf : (fun j => if T + j < T then seq (T + j) else w (T + j - T)) = w := by
            funext j; simp
          rw [hsuf]
          exact hw
        · obtain ⟨k', hk', hw'⟩ := hseq y hy' hyreach
          refine ⟨k', by omega, ?_⟩
          have : y.1.walk (fun j => if j < T then seq j else w (j - T)) (y.2.1, 0) k'
              = y.1.walk seq (y.2.1, 0) k' :=
            y.1.walk_congr _ _ _ k' (fun j hj => by simp [show j < T by omega])
          rw [this]
          exact hw'
      · refine ⟨T, seq, ?_⟩
        intro y hy hyreach
        rcases List.mem_cons.1 hy with rfl | hy'
        · exact absurd hyreach hx
        · exact hseq y hy' hyreach

noncomputable instance : Fintype (RotGraph n d) :=
  Fintype.ofInjective (fun G : RotGraph n d => G.rot) (by
    intro G H h
    cases G; cases H; simpa using h)

/-- **Universal exploration sequences exist** (of some, in general exponential, length).
Reingold's theorem is the much stronger statement that they exist of polynomial length,
which is the content of the hypothesis `CS.HasPolyUES`. -/
theorem exists_ues (n d : ℕ) [NeZero d] : ∃ (T : ℕ) (seq : ℕ → Fin d), IsUES n d T seq := by
  obtain ⟨T, seq, hseq⟩ :=
    exists_seq_for_list (Finset.univ : Finset (RotGraph n d × Fin n × Fin n)).toList
  refine ⟨T, seq, ?_⟩
  intro G s t hst
  exact hseq (G, s, t) (by simp) hst

end CS

/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file formalises the algorithmic content of Reingold's theorem
(`SL = L`, i.e. undirected `s`-`t` connectivity is decidable in logarithmic space)
in the following model.

* An undirected `d`-regular multigraph on the vertex set `Fin n` is presented by its
  **rotation map** `rot : Fin n × Fin d → Fin n × Fin d`, an involution: `rot (v, i) = (w, j)`
  means that the `i`-th edge leaving `v` arrives at `w` as its `j`-th edge.  (Self-loops are
  allowed, so every symmetric bounded-degree graph can be presented this way after padding.)

* A **space bounded machine** (`CS.Machine`) has a finite configuration type `C`, an initial
  configuration depending on the two query vertices `s`, `t`, and at each step it makes exactly
  one query to the rotation map of the input graph and updates its configuration accordingly.
  The space used by the machine is `log₂ (card C)`; the input is read-only and is accessed
  only through rotation-map queries, so this is the usual model of a log-space algorithm
  with a graph given as input.

* The deep ingredient of Reingold's theorem is isolated as the hypothesis
  `CS.HasPolyUES`: for all `n` and `d` there is a **universal exploration sequence** of
  length polynomial in `n * d`, i.e. a sequence of edge-label offsets which, followed from
  any starting vertex of any `d`-regular rotation graph on `Fin n`, visits the whole connected
  component of the starting vertex.  Reingold's zig-zag construction produces such sequences
  (and produces them log-space uniformly); that construction is *not* formalised here and is
  the reason the results below are stated conditionally on `CS.HasPolyUES`.

Everything else is proved: that the exploration walk never leaves the connected component
(soundness), that the resulting machine is correct on all inputs, that its configuration
space is polynomially bounded — hence it uses logarithmic space — and that consequently every
symmetric nondeterministic space-bounded machine can be simulated deterministically with only
a polynomial blow-up of the configuration space (`SL ⊆ L`).

The companion file `RequestProject/UESExistence.lean` proves unconditionally that universal
exploration sequences of *some* finite (in general exponential) length always exist
(`CS.exists_ues`), so `CS.HasPolyUES` is a statement purely about their *length*; making the
length polynomial is exactly what Reingold's construction achieves.

Two caveats on the formalisation.  First, the converse inclusion `L ⊆ SL` is the easy standard
one and is not formalised here.  Second, the statements quantify, for each input size, over the
existence of a machine; the machine is built from the exploration sequence by one fixed recipe
(`CS.Machine.connMachine`), so log-space uniformity of Reingold's sequences yields a uniform
algorithm, but uniformity of the family is not itself part of the formal statements.
-/

set_option autoImplicit false

namespace CS

/-! ## Rotation graphs -/

/-- An undirected `d`-regular multigraph on `Fin n`, given by its rotation map:
`rot (v, i) = (w, j)` says that the `i`-th edge at `v` leads to `w`, where it is the `j`-th
edge.  The involutivity of `rot` is exactly the statement that the graph is undirected. -/
structure RotGraph (n d : ℕ) where
  /-- The rotation map. -/
  rot : Fin n × Fin d → Fin n × Fin d
  /-- The rotation map is an involution. -/
  rot_involutive : Function.Involutive rot

/-- Add an offset to an edge label (the argument `i : Fin d` witnesses `0 < d`). -/
def addOff {d : ℕ} (i a : Fin d) : Fin d :=
  ⟨(i.1 + a.1) % d, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

namespace RotGraph

variable {n d : ℕ}

/-- Adjacency in a rotation graph. -/
def Adj (G : RotGraph n d) (u v : Fin n) : Prop := ∃ i : Fin d, (G.rot (u, i)).1 = v

lemma adj_rot (G : RotGraph n d) (p : Fin n × Fin d) : G.Adj p.1 (G.rot p).1 := ⟨p.2, by simp⟩

lemma adj_symm (G : RotGraph n d) {u v : Fin n} (h : G.Adj u v) : G.Adj v u := by
  obtain ⟨i, hi⟩ := h
  refine ⟨(G.rot (u, i)).2, ?_⟩
  have h2 := G.rot_involutive (u, i)
  rw [← hi]
  simp [h2]

/-- Undirected `s`-`t` connectivity: `t` is reachable from `s`. -/
def Reachable (G : RotGraph n d) : Fin n → Fin n → Prop := Relation.ReflTransGen G.Adj

/-- One step of an exploration walk: traverse the current edge, then add the offset `a`
to the label of the arriving edge. -/
def stepE (G : RotGraph n d) (a : Fin d) (p : Fin n × Fin d) : Fin n × Fin d :=
  ((G.rot p).1, addOff (G.rot p).2 a)

/-- The exploration walk driven by the offset sequence `seq`, started at the
vertex/label pair `p`. -/
def walk (G : RotGraph n d) (seq : ℕ → Fin d) (p : Fin n × Fin d) : ℕ → Fin n × Fin d
  | 0 => p
  | k+1 => G.stepE (seq k) (G.walk seq p k)

lemma walk_succ (G : RotGraph n d) (seq : ℕ → Fin d) (p : Fin n × Fin d) (k : ℕ) :
    G.walk seq p (k+1) = G.stepE (seq k) (G.walk seq p k) := rfl

/-- Soundness of the exploration walk: it never leaves the connected component of its
starting vertex. -/
lemma walk_reachable (G : RotGraph n d) (seq : ℕ → Fin d) (p : Fin n × Fin d) (k : ℕ) :
    G.Reachable p.1 (G.walk seq p k).1 := by
  induction k with
  | zero => exact Relation.ReflTransGen.refl
  | succ k ih => exact ih.tail (G.adj_rot _)

end RotGraph

/-! ## Universal exploration sequences -/

/-- `seq` is a universal exploration sequence of length `T` for `d`-regular rotation graphs
on `Fin n`: from any start vertex, following the offsets of `seq` for at most `T` steps
visits every vertex of the connected component of the start vertex. -/
def IsUES (n d T : ℕ) [NeZero d] (seq : ℕ → Fin d) : Prop :=
  ∀ (G : RotGraph n d) (s t : Fin n), G.Reachable s t →
    ∃ k ≤ T, (G.walk seq (s, 0) k).1 = t

/-- **The input from Reingold's theorem.**  For every vertex count `n` and degree `d` there is
a universal exploration sequence of length polynomial in `n * d` (the polynomial degree `c`
being uniform in `n` and `d`).  Reingold's zig-zag based construction supplies such sequences;
that construction is not formalised here. -/
def HasPolyUES : Prop :=
  ∃ c : ℕ, ∀ (n d : ℕ) [NeZero d], ∃ (T : ℕ) (seq : ℕ → Fin d),
    T ≤ (n * d + 1) ^ c ∧ IsUES n d T seq

/-! ## Space bounded machines with query access to the input graph -/

/-- A deterministic machine which decides a property of pairs of vertices of a rotation graph.
It has a finite configuration space `C`; in each step it queries the rotation map at the pair
`query c` and moves to the configuration `next c` applied to the answer.  Space usage is
`log₂ (card C)`. -/
structure Machine (n d : ℕ) where
  /-- The configuration type. -/
  C : Type
  /-- The configuration type is finite. -/
  fintypeC : Fintype C
  /-- The initial configuration on the query pair `(s, t)`. -/
  init : Fin n → Fin n → C
  /-- The rotation-map entry queried in the current configuration. -/
  query : C → Fin n × Fin d
  /-- The transition function, fed with the answer to the query. -/
  next : C → Fin n × Fin d → C
  /-- The accepting configurations. -/
  accept : C → Bool

namespace Machine

variable {n d : ℕ}

/-- The number of configurations; the space used by the machine is `log₂` of this. -/
def numConfigs (M : Machine n d) : ℕ := @Fintype.card M.C M.fintypeC

/-- The space (in bits) used by the machine. -/
def space (M : Machine n d) : ℕ := Nat.log 2 M.numConfigs

/-- One step of `M` on the input graph `G`. -/
def stepG (M : Machine n d) (G : RotGraph n d) (c : M.C) : M.C := M.next c (G.rot (M.query c))

/-- The configuration of `M` after `k` steps on input `G`, started at `c`. -/
def run (M : Machine n d) (G : RotGraph n d) (c : M.C) (k : ℕ) : M.C := (M.stepG G)^[k] c

/-- `M` accepts the pair `(s, t)` on input `G`. -/
def Accepts (M : Machine n d) (G : RotGraph n d) (s t : Fin n) : Prop :=
  ∃ k, M.accept (M.run G (M.init s t) k) = true

lemma run_succ (M : Machine n d) (G : RotGraph n d) (c : M.C) (k : ℕ) :
    M.run G c (k+1) = M.stepG G (M.run G c k) := Function.iterate_succ_apply' _ _ _

/-! ### The connectivity machine

Given a universal exploration sequence `seq` of length `T`, the machine simply follows the
exploration walk for `T` steps, remembering the current vertex/label pair, the target vertex,
a step counter, and one bit recording whether the target has been seen. -/

/-- The machine that decides `s`-`t` connectivity by following the exploration sequence `seq`
for `T` steps. -/
noncomputable def connMachine (n d T : ℕ) [NeZero d] (seq : ℕ → Fin d) : Machine n d where
  C := (Fin n × Fin d) × Fin n × Fin (T+1) × Bool
  fintypeC := inferInstance
  init s t := ((s, 0), t, 0, decide (s = t))
  query c := c.1
  next c ans :=
    if (c.2.2.1 : ℕ) = T then c
    else
      (((ans.1, addOff ans.2 (seq (c.2.2.1 : ℕ))), c.2.1, c.2.2.1 + 1,
        c.2.2.2 || decide (ans.1 = c.2.1)))
  accept c := c.2.2.2

variable {T : ℕ} [NeZero d] {seq : ℕ → Fin d}

lemma connMachine_stepG (G : RotGraph n d)
    (c : (Fin n × Fin d) × Fin n × Fin (T+1) × Bool) :
    (connMachine n d T seq).stepG G c =
      (if (c.2.2.1 : ℕ) = T then c
      else (((G.rot c.1).1, addOff (G.rot c.1).2 (seq (c.2.2.1 : ℕ))), c.2.1, c.2.2.1 + 1,
        c.2.2.2 || decide ((G.rot c.1).1 = c.2.1))) := rfl

lemma connMachine_numConfigs (n d T : ℕ) [NeZero d] (seq : ℕ → Fin d) :
    (connMachine n d T seq).numConfigs = n * d * (n * ((T + 1) * 2)) := by
  simp [numConfigs, connMachine]

/-- The state of the connectivity machine after `k` steps: it holds the `min k T`-th point of
the exploration walk, the target vertex, the counter `min k T`, and the bit recording whether
the target has been visited so far. -/
lemma connMachine_invariant (G : RotGraph n d) (s t : Fin n) (k : ℕ) :
    ((connMachine n d T seq).run G ((connMachine n d T seq).init s t) k).1
        = G.walk seq (s, 0) (min k T) ∧
      ((connMachine n d T seq).run G ((connMachine n d T seq).init s t) k).2.1 = t ∧
      ((((connMachine n d T seq).run G ((connMachine n d T seq).init s t) k).2.2.1 : ℕ)
        = min k T) ∧
      (((connMachine n d T seq).run G ((connMachine n d T seq).init s t) k).2.2.2 = true
        ↔ ∃ j ≤ min k T, (G.walk seq (s, 0) j).1 = t) := by
  induction k with
  | zero =>
      refine ⟨rfl, rfl, rfl, ?_⟩
      show (decide (s = t) = true) ↔ _
      simp [RotGraph.walk]
  | succ k ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      rw [run_succ, connMachine_stepG]
      rcases Nat.lt_or_ge k T with hk | hk
      · have hm : min k T = k := min_eq_left hk.le
        have hm' : min (k+1) T = k+1 := min_eq_left hk
        rw [hm] at h1 h3 h4
        rw [hm']
        rw [if_neg (by rw [h3]; omega)]
        have hval : ((((connMachine n d T seq).run G ((connMachine n d T seq).init s t) k).2.2.1
            + 1 : Fin (T+1)) : ℕ) = k + 1 := by
          rw [Fin.val_add_one_of_lt (by rw [Fin.lt_def, h3]; simpa using hk), h3]
        refine ⟨by simp only [h1, h3]; rfl, h2, hval, ?_⟩
        simp only [Bool.or_eq_true, decide_eq_true_eq, h4, h1, h2]
        constructor
        · rintro (⟨j, hj, hjt⟩ | h)
          · exact ⟨j, by omega, hjt⟩
          · exact ⟨k+1, le_refl _, h⟩
        · rintro ⟨j, hj, hjt⟩
          rcases Nat.lt_or_ge j (k+1) with hj' | hj'
          · exact Or.inl ⟨j, by omega, hjt⟩
          · have hjk : j = k + 1 := by omega
            subst hjk
            exact Or.inr hjt
      · have hm : min k T = T := min_eq_right hk
        have hm' : min (k+1) T = T := min_eq_right (by omega)
        rw [hm] at h1 h3 h4
        rw [hm', if_pos h3]
        exact ⟨h1, h2, h3, h4⟩

lemma connMachine_accepts_iff (G : RotGraph n d) (s t : Fin n) :
    (connMachine n d T seq).Accepts G s t ↔ ∃ j ≤ T, (G.walk seq (s, 0) j).1 = t := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨-, -, -, h4⟩ := connMachine_invariant (T := T) (seq := seq) G s t k
    obtain ⟨j, hj, hjt⟩ := h4.1 hk
    exact ⟨j, le_trans hj (min_le_right _ _), hjt⟩
  · rintro ⟨j, hj, hjt⟩
    obtain ⟨-, -, -, h4⟩ := connMachine_invariant (T := T) (seq := seq) G s t T
    refine ⟨T, h4.2 ?_⟩
    exact ⟨j, by simpa using hj, hjt⟩

/-- Correctness of the connectivity machine, given a universal exploration sequence. -/
theorem connMachine_correct (hues : IsUES n d T seq) (G : RotGraph n d) (s t : Fin n) :
    (connMachine n d T seq).Accepts G s t ↔ G.Reachable s t := by
  rw [connMachine_accepts_iff]
  constructor
  · rintro ⟨j, -, hjt⟩
    have := G.walk_reachable seq (s, 0) j
    rw [hjt] at this
    exact this
  · intro h
    exact hues G s t h

end Machine

/-! ## Arithmetic auxiliaries -/

lemma numConfigs_bound {n d T c : ℕ} (hd1 : 1 ≤ d) (hT : T ≤ (n * d + 1) ^ c) :
    n * d * (n * ((T + 1) * 2)) ≤ (n * d + 2) ^ (c + 5) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · simp [hn0]
  set B := n * d + 2
  have hB2 : 2 ≤ B := by omega
  have hn : n ≤ B :=
    le_trans (by simpa using Nat.mul_le_mul (le_refl n) hd1) (Nat.le_add_right _ 2)
  have hd : d ≤ B :=
    le_trans (by simpa using Nat.mul_le_mul hn0 (le_refl d)) (Nat.le_add_right _ 2)
  have hpow : (n * d + 1) ^ c ≤ B ^ c := Nat.pow_le_pow_left (by omega) c
  have hone : 1 ≤ B ^ c := Nat.one_le_pow _ _ (by omega)
  have hT' : T + 1 ≤ B ^ (c + 1) := by
    have hBc : B ^ (c + 1) = B ^ c * B := by ring
    calc T + 1 ≤ B ^ c + 1 := by omega
      _ ≤ B ^ c * 2 := by omega
      _ ≤ B ^ c * B := Nat.mul_le_mul_left _ hB2
      _ = B ^ (c + 1) := hBc.symm
  calc n * d * (n * ((T + 1) * 2))
      ≤ B * B * (B * (B ^ (c + 1) * B)) := by
        refine Nat.mul_le_mul (Nat.mul_le_mul hn hd) (Nat.mul_le_mul hn (Nat.mul_le_mul hT' hB2))
    _ = B ^ (c + 5) := by ring

lemma log_le_of_le_pow {N B c : ℕ} (h : N ≤ B ^ c) :
    Nat.log 2 N ≤ c * (Nat.log 2 B + 1) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [hN]
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    have hN1 : N = 1 := le_antisymm (by simpa using h) hN
    simp [hN1]
  have hBlt : B < 2 ^ (Nat.log 2 B + 1) := Nat.lt_pow_succ_log_self (by norm_num) B
  have hlt : N < 2 ^ (c * (Nat.log 2 B + 1)) := by
    calc N ≤ B ^ c := h
      _ < (2 ^ (Nat.log 2 B + 1)) ^ c := Nat.pow_lt_pow_left hBlt hc.ne'
      _ = 2 ^ (c * (Nat.log 2 B + 1)) := by rw [← pow_mul, Nat.mul_comm]
  exact le_of_lt (Nat.log_lt_of_lt_pow hN.ne' hlt)

/-! ## Undirected s-t connectivity is in logarithmic space -/

/-- **Undirected `s`-`t` connectivity is in `L`** (given Reingold's universal exploration
sequences): there is a polynomial degree `c` such that for every vertex count `n` and every
degree `d` there is a machine `M` with at most `(n * d + 2) ^ c` configurations — i.e. using
`O(log (n * d))` bits of space — which, with read-only query access to the rotation map of
the input graph, decides for every graph `G` and every pair of vertices `s`, `t` whether `t`
is reachable from `s`. -/
theorem ustcon_in_logspace (h : HasPolyUES) :
    ∃ c : ℕ, ∀ (n d : ℕ) [NeZero d], ∃ M : Machine n d,
      M.numConfigs ≤ (n * d + 2) ^ c ∧
      M.space ≤ c * (Nat.log 2 (n * d + 2) + 1) ∧
      ∀ (G : RotGraph n d) (s t : Fin n), M.Accepts G s t ↔ G.Reachable s t := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c + 5, ?_⟩
  intro n d _
  obtain ⟨T, seq, hT, hues⟩ := hc n d
  refine ⟨Machine.connMachine n d T seq, ?_, ?_, ?_⟩
  · rw [Machine.connMachine_numConfigs]
    exact numConfigs_bound (Nat.pos_of_ne_zero (NeZero.ne d)) hT
  · refine log_le_of_le_pow ?_
    rw [Machine.connMachine_numConfigs]
    exact numConfigs_bound (Nat.pos_of_ne_zero (NeZero.ne d)) hT
  · intro G s t
    exact Machine.connMachine_correct hues G s t

/-! ## Symmetric nondeterministic machines: `SL ⊆ L` -/

/-- A symmetric nondeterministic space-bounded machine: its configuration graph is an
undirected `d`-regular multigraph on the (finite) configuration type, presented by a rotation
map, with a distinguished initial configuration and a distinguished accepting configuration
(the standard normalisation of a symmetric machine). -/
structure SymMachine (d : ℕ) where
  /-- The configuration type. -/
  C : Type
  /-- The configuration type is finite. -/
  fintypeC : Fintype C
  /-- The rotation map of the configuration graph. -/
  rot : C × Fin d → C × Fin d
  /-- Symmetry of the configuration graph. -/
  rot_involutive : Function.Involutive rot
  /-- The initial configuration. -/
  start : C
  /-- The unique accepting configuration. -/
  acc : C

namespace SymMachine

variable {d : ℕ}

/-- The number of configurations. -/
def numConfigs (S : SymMachine d) : ℕ := @Fintype.card S.C S.fintypeC

/-- Adjacency of configurations. -/
def Adj (S : SymMachine d) (u v : S.C) : Prop := ∃ i : Fin d, (S.rot (u, i)).1 = v

/-- A symmetric machine accepts iff the accepting configuration is reachable from the
initial one in its (undirected) configuration graph. -/
def Accepts (S : SymMachine d) : Prop := Relation.ReflTransGen S.Adj S.start S.acc

end SymMachine

/-- A deterministic space-bounded machine with no external input. -/
structure DetMachine where
  /-- The configuration type. -/
  D : Type
  /-- The configuration type is finite. -/
  fintypeD : Fintype D
  /-- The transition function. -/
  step : D → D
  /-- The initial configuration. -/
  start : D
  /-- The accepting configurations. -/
  accept : D → Bool

namespace DetMachine

/-- The number of configurations. -/
def numConfigs (M : DetMachine) : ℕ := @Fintype.card M.D M.fintypeD

/-- The space (in bits) used by the machine. -/
def space (M : DetMachine) : ℕ := Nat.log 2 M.numConfigs

/-- `M` accepts if some configuration in its (deterministic) run is accepting. -/
def Accepts (M : DetMachine) : Prop := ∃ k, M.accept (M.step^[k] M.start) = true

end DetMachine

/-- The rotation graph on `Fin (card S.C)` obtained from the configuration graph of a
symmetric machine by transporting along an enumeration of the configurations. -/
noncomputable def SymMachine.toRotGraph {d : ℕ} (S : SymMachine d) :
    RotGraph (@Fintype.card S.C S.fintypeC) d :=
  letI := S.fintypeC
  let e : S.C ≃ Fin (Fintype.card S.C) := Fintype.equivFin S.C
  { rot := fun p => ((e (S.rot (e.symm p.1, p.2)).1), (S.rot (e.symm p.1, p.2)).2)
    rot_involutive := by
      intro p
      simp only [Equiv.symm_apply_apply]
      have := S.rot_involutive (e.symm p.1, p.2)
      rw [show ((S.rot (e.symm p.1, p.2)).1, (S.rot (e.symm p.1, p.2)).2)
        = S.rot (e.symm p.1, p.2) from rfl, this]
      simp }

lemma SymMachine.toRotGraph_adj_iff {d : ℕ} (S : SymMachine d) (u v : S.C) :
    letI := S.fintypeC
    S.toRotGraph.Adj (Fintype.equivFin S.C u) (Fintype.equivFin S.C v) ↔ S.Adj u v := by
  letI := S.fintypeC
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have : (Fintype.equivFin S.C).symm ((Fintype.equivFin S.C) u) = u := by simp
    simp only [SymMachine.toRotGraph, this] at hi
    have := congrArg (Fintype.equivFin S.C).symm hi
    simpa using this
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simp only [SymMachine.toRotGraph, Equiv.symm_apply_apply]
    rw [hi]

lemma SymMachine.reachable_iff {d : ℕ} (S : SymMachine d) (u v : S.C) :
    letI := S.fintypeC
    S.toRotGraph.Reachable (Fintype.equivFin S.C u) (Fintype.equivFin S.C v)
      ↔ Relation.ReflTransGen S.Adj u v := by
  letI := S.fintypeC
  set e : S.C ≃ Fin (Fintype.card S.C) := Fintype.equivFin S.C with he
  constructor
  · intro h
    have hlift := Relation.ReflTransGen.lift (f := fun x => e.symm x)
      (fun a b hab => (S.toRotGraph_adj_iff (e.symm a) (e.symm b)).1 (by simpa [he] using hab)) h
    simpa [he] using hlift
  · intro h
    exact Relation.ReflTransGen.lift (f := fun x => e x)
      (fun a b hab => (S.toRotGraph_adj_iff a b).2 hab) h

/-- Turning a `Machine` run on a fixed input graph, from a fixed initial configuration,
into a `DetMachine`. -/
noncomputable def Machine.toDet {n d : ℕ} (M : Machine n d) (G : RotGraph n d) (s t : Fin n) :
    DetMachine where
  D := M.C
  fintypeD := M.fintypeC
  step := M.stepG G
  start := M.init s t
  accept := M.accept

lemma Machine.toDet_accepts_iff {n d : ℕ} (M : Machine n d) (G : RotGraph n d) (s t : Fin n) :
    (M.toDet G s t).Accepts ↔ M.Accepts G s t := Iff.rfl

lemma Machine.toDet_numConfigs {n d : ℕ} (M : Machine n d) (G : RotGraph n d) (s t : Fin n) :
    (M.toDet G s t).numConfigs = M.numConfigs := rfl

/-- **`SL ⊆ L`** (given Reingold's universal exploration sequences): every symmetric
nondeterministic space-bounded machine is simulated by a deterministic machine whose
configuration space is polynomially bounded in that of the symmetric machine; equivalently,
a symmetric nondeterministic machine using space `s` is simulated deterministically in
space `O(s)`. -/
theorem sl_subseteq_logspace (h : HasPolyUES) :
    ∃ c : ℕ, ∀ (d : ℕ) [NeZero d] (S : SymMachine d), ∃ M : DetMachine,
      M.numConfigs ≤ (S.numConfigs * d + 2) ^ c ∧
      M.space ≤ c * (Nat.log 2 (S.numConfigs * d + 2) + 1) ∧
      (M.Accepts ↔ S.Accepts) := by
  obtain ⟨c, hc⟩ := ustcon_in_logspace h
  refine ⟨c, ?_⟩
  intro d _ S
  letI := S.fintypeC
  obtain ⟨M, hcard, hspace, hcorrect⟩ := hc (Fintype.card S.C) d
  set e : S.C ≃ Fin (Fintype.card S.C) := Fintype.equivFin S.C with he
  refine ⟨M.toDet S.toRotGraph (e S.start) (e S.acc), ?_, ?_, ?_⟩
  · rw [Machine.toDet_numConfigs]
    exact hcard
  · rw [DetMachine.space, Machine.toDet_numConfigs]
    exact hspace
  · rw [Machine.toDet_accepts_iff, hcorrect]
    exact S.reachable_iff S.start S.acc

/-- **Reingold's theorem** (conditional on the universal exploration sequences produced by the
zig-zag construction, `HasPolyUES`): undirected `s`-`t` connectivity is decidable in
logarithmic space, and consequently every symmetric nondeterministic space-bounded machine can
be simulated deterministically with only a constant-factor increase of the space, i.e.
`SL ⊆ L`. -/
theorem reingold_sl_l (h : HasPolyUES) :
    (∃ c : ℕ, ∀ (n d : ℕ) [NeZero d], ∃ M : Machine n d,
        M.numConfigs ≤ (n * d + 2) ^ c ∧
        M.space ≤ c * (Nat.log 2 (n * d + 2) + 1) ∧
        ∀ (G : RotGraph n d) (s t : Fin n), M.Accepts G s t ↔ G.Reachable s t) ∧
      (∃ c : ℕ, ∀ (d : ℕ) [NeZero d] (S : SymMachine d), ∃ M : DetMachine,
        M.numConfigs ≤ (S.numConfigs * d + 2) ^ c ∧
        M.space ≤ c * (Nat.log 2 (S.numConfigs * d + 2) + 1) ∧
        (M.Accepts ↔ S.Accepts)) :=
  ⟨ustcon_in_logspace h, sl_subseteq_logspace h⟩

end CS

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

