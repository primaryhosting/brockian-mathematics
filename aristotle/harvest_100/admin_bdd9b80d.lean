/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

/-!
## Scope of this file

Reingold's theorem `SL = L` says that undirected `s`-`t` connectivity can be decided in
logarithmic space.  Its proof has two ingredients:

1. a logarithmic-space transformation turning an arbitrary undirected graph into a
   constant-degree graph of logarithmic diameter (an expander), preserving connectivity, and
2. the observation that connectivity in a constant-degree graph of logarithmic diameter is
   decidable in logarithmic space, by exhaustively trying all label sequences of logarithmic
   length.

What is formalized and proved here, axiom-free, is a complete machine model of space-bounded
computation with oracle access to the input graph, together with step 2: the theorem
`CS.reingold_sl_l` builds an explicit machine with polynomially many configurations (i.e.
`O(log n)` bits of memory) that decides `s`-`t` connectivity on `d`-regular graphs of diameter
at most `C * log₂ n`.  Step 1 — the expander transformation via the zig-zag product — is *not*
formalized here, so the general statement `SL = L` is not obtained.
-/

namespace CS

/-! ## Undirected graphs given by a rotation map -/

/-- A `d`-regular undirected graph on the vertex set `Fin n`, presented (as in Reingold's
algorithm) by a *rotation map*: `nbr v i` is the `i`-th neighbour of `v`, and `rot v i` is the
label under which the edge is traversed backwards.  The axiom `nbr_rot` says that following an
edge and then its reverse label returns to the starting vertex; this is exactly what makes the
adjacency relation symmetric, i.e. the graph undirected. -/
structure LGraph (n d : ℕ) where
  nbr : Fin n → Fin d → Fin n
  rot : Fin n → Fin d → Fin d
  nbr_rot : ∀ v i, nbr (nbr v i) (rot v i) = v

variable {n d : ℕ}

/-- Adjacency of the labelled graph. -/
def LGraph.Adj (G : LGraph n d) (u v : Fin n) : Prop := ∃ i, G.nbr u i = v

lemma LGraph.adj_symm (G : LGraph n d) {u v : Fin n} (h : G.Adj u v) : G.Adj v u := by
  obtain ⟨i, rfl⟩ := h
  exact ⟨G.rot u i, G.nbr_rot u i⟩

/-- Connectivity: the reflexive-transitive closure of adjacency. -/
def LGraph.Reach (G : LGraph n d) : Fin n → Fin n → Prop := Relation.ReflTransGen G.Adj

lemma LGraph.Reach.refl (G : LGraph n d) (u : Fin n) : G.Reach u u := Relation.ReflTransGen.refl

lemma LGraph.Reach.tail {G : LGraph n d} {u v w : Fin n} (h : G.Reach u v) (h' : G.Adj v w) :
    G.Reach u w := Relation.ReflTransGen.tail h h'

/-- The walk from `s` that follows the sequence of edge labels `c`. -/
def LGraph.walk (G : LGraph n d) (s : Fin n) (c : ℕ → Fin d) : ℕ → Fin n
  | 0 => s
  | j + 1 => G.nbr (G.walk s c j) (c j)

/-- `G` has diameter at most `D`: any two connected vertices are joined by a labelled walk of
length at most `D`. -/
def LGraph.HasDiameterAtMost (G : LGraph n d) (D : ℕ) : Prop :=
  ∀ u v : Fin n, G.Reach u v → ∃ (c : ℕ → Fin d) (j : ℕ), j ≤ D ∧ G.walk u c j = v

lemma LGraph.reach_walk (G : LGraph n d) (s : Fin n) (c : ℕ → Fin d) (j : ℕ) :
    G.Reach s (G.walk s c j) := by
  induction j with
  | zero => exact Relation.ReflTransGen.refl
  | succ j ih => exact ih.tail ⟨c j, rfl⟩

/-! ## A space-bounded machine model

A machine has a finite set of configurations (its "memory"); the amount of space it uses is
`log₂` of the number of configurations.  It accesses the input graph only through queries: in
configuration `q` it asks for the `i`-th neighbour of a vertex `v` and moves to a new
configuration depending on the answer, or it halts with a Boolean answer. -/

structure Machine (n d : ℕ) where
  State : Type
  [fin : Fintype State]
  start : State
  act : State → (Fin n × Fin d) ⊕ Bool
  next : State → Fin n → State

attribute [instance] Machine.fin

/-- One computation step in the graph `G`. -/
def Machine.stepS (M : Machine n d) (G : LGraph n d) (q : M.State) : M.State ⊕ Bool :=
  match M.act q with
  | Sum.inl (v, i) => Sum.inl (M.next q (G.nbr v i))
  | Sum.inr b => Sum.inr b

/-- `m` computation steps starting from `q`. -/
def Machine.multi (M : Machine n d) (G : LGraph n d) : ℕ → M.State → M.State ⊕ Bool
  | 0, q => Sum.inl q
  | m + 1, q =>
      match M.stepS G q with
      | Sum.inl q' => M.multi G m q'
      | Sum.inr b => Sum.inr b

/-- The machine halts on `G` with output `b`. -/
def Machine.Outputs (M : Machine n d) (G : LGraph n d) (b : Bool) : Prop :=
  ∃ m, M.multi G m M.start = Sum.inr b

/-- The machine decides whether `t` is reachable from `s` in `G`. -/
def Machine.Decides (M : Machine n d) (G : LGraph n d) (s t : Fin n) : Prop :=
  (G.Reach s t → M.Outputs G true) ∧ (¬ G.Reach s t → M.Outputs G false)

lemma Machine.multi_succ_inl {M : Machine n d} {G : LGraph n d} {m : ℕ} {q q' : M.State}
    (hs : M.stepS G q = Sum.inl q') : M.multi G (m + 1) q = M.multi G m q' := by
  simp [Machine.multi, hs]

lemma Machine.multi_succ_inr {M : Machine n d} {G : LGraph n d} {m : ℕ} {q : M.State} {b : Bool}
    (hs : M.stepS G q = Sum.inr b) : M.multi G (m + 1) q = Sum.inr b := by
  simp [Machine.multi, hs]

lemma Machine.multi_add {M : Machine n d} {G : LGraph n d} {a b : ℕ} {q q' : M.State}
    (h : M.multi G a q = Sum.inl q') : M.multi G (a + b) q = M.multi G b q' := by
  induction a generalizing q with
  | zero =>
      simp only [Machine.multi] at h
      cases h
      simp
  | succ a ih =>
      rw [Nat.succ_add]
      cases hs : M.stepS G q with
      | inl q'' =>
          rw [Machine.multi_succ_inl hs] at h ⊢
          exact ih h
      | inr bb =>
          rw [Machine.multi_succ_inr hs] at h
          exact absurd h (by simp)

lemma Machine.multi_halt {M : Machine n d} {G : LGraph n d} {a b : ℕ} {q : M.State} {bb : Bool}
    (h : M.multi G a q = Sum.inr bb) : M.multi G (a + b) q = Sum.inr bb := by
  induction a generalizing q with
  | zero => simp only [Machine.multi] at h; exact absurd h (by simp)
  | succ a ih =>
      rw [Nat.succ_add]
      cases hs : M.stepS G q with
      | inl q'' =>
          rw [Machine.multi_succ_inl hs] at h ⊢
          exact ih h
      | inr b' =>
          rw [Machine.multi_succ_inr hs] at h ⊢
          exact h


/-! ## The search machine

For a graph of degree `d` and diameter at most `D` we build an explicit machine that decides
`s`-`t` connectivity: it enumerates all label sequences `w ∈ (Fin d)^D` (encoded as a number
`k < d ^ D` in base `d`) and, for each of them, walks from `s` following the labels, checking at
every step whether `t` has been reached.  Its memory consists of the current sequence `k`, the
number `i ≤ D` of steps taken so far, and the current vertex, i.e. `d ^ D * (D + 1) * n`
configurations, which is `O(D * log d + log n)` bits of space. -/

/-- The `i`-th digit of `k` in base `d`. -/
def dg (d k i : ℕ) : ℕ := k / d ^ i % d

lemma dg_lt {d : ℕ} (hd : 0 < d) (k i : ℕ) : dg d k i < d := Nat.mod_lt _ hd

/-- The `i`-th digit of `k` in base `d`, as an edge label. -/
def digF {d : ℕ} (hd : 0 < d) (k i : ℕ) : Fin d := ⟨dg d k i, dg_lt hd k i⟩

/-- Configurations of the search machine. -/
abbrev St (n d D : ℕ) : Type := Fin (d ^ D) × Fin (D + 1) × Fin n

/-- Move to the next label sequence. -/
def kSucc {d D : ℕ} (k : Fin (d ^ D)) : Fin (d ^ D) :=
  if h : (k : ℕ) + 1 < d ^ D then ⟨(k : ℕ) + 1, h⟩ else k

/-- Increase the step counter. -/
def iSucc {D : ℕ} (i : Fin (D + 1)) : Fin (D + 1) :=
  if h : (i : ℕ) + 1 < D + 1 then ⟨(i : ℕ) + 1, h⟩ else i

/-- The action taken in a configuration. -/
def actF {n d : ℕ} (hd : 0 < d) (D : ℕ) (t : Fin n) (q : St n d D) : (Fin n × Fin d) ⊕ Bool :=
  if q.2.2 = t then Sum.inr true
  else if (q.2.1 : ℕ) = D then
    (if (q.1 : ℕ) + 1 = d ^ D then Sum.inr false else Sum.inl (q.2.2, ⟨0, hd⟩))
  else Sum.inl (q.2.2, digF hd (q.1 : ℕ) (q.2.1 : ℕ))

/-- The transition on the answer to a query. -/
def nextF {n d : ℕ} (D : ℕ) (s : Fin n) (q : St n d D) (w : Fin n) : St n d D :=
  if (q.2.1 : ℕ) = D then (kSucc q.1, ⟨0, Nat.succ_pos D⟩, s) else (q.1, iSucc q.2.1, w)

/-- The search machine. -/
def searchMachine {n d : ℕ} (hd : 0 < d) (D : ℕ) (s t : Fin n) : Machine n d where
  State := St n d D
  start := (⟨0, pow_pos hd D⟩, ⟨0, Nat.succ_pos D⟩, s)
  act := actF hd D t
  next := nextF D s

lemma card_searchMachine {n d : ℕ} (hd : 0 < d) (D : ℕ) (s t : Fin n) :
    Fintype.card (searchMachine hd D s t).State = d ^ D * ((D + 1) * n) := by
  simp [searchMachine, St]

/-- A configuration described by natural numbers. -/
def stq {n d D : ℕ} (k i : ℕ) (hk : k < d ^ D) (hi : i ≤ D) (v : Fin n) : St n d D :=
  (⟨k, hk⟩, ⟨i, Nat.lt_succ_of_le hi⟩, v)

variable {G : LGraph n d}

lemma stepS_found {D k i : ℕ} (hd : 0 < d) {s t v : Fin n} (hk : k < d ^ D) (hi : i ≤ D)
    (hv : v = t) :
    (searchMachine hd D s t).stepS G (stq k i hk hi v) = Sum.inr true := by
  simp [Machine.stepS, searchMachine, actF, stq, hv]

lemma stepS_step {D k i : ℕ} (hd : 0 < d) {s t v : Fin n} (hk : k < d ^ D) (hi : i < D)
    (hv : v ≠ t) :
    (searchMachine hd D s t).stepS G (stq k i hk hi.le v)
      = Sum.inl (stq k (i + 1) hk hi (G.nbr v (digF hd k i))) := by
  simp only [Machine.stepS, searchMachine, actF, nextF, stq, if_neg hv,
    if_neg (show ¬ i = D by omega), iSucc, dif_pos (show i + 1 < D + 1 by omega)]

lemma stepS_last {D k : ℕ} (hd : 0 < d) {s t v : Fin n} (hk : k < d ^ D) (hv : v ≠ t)
    (hlast : k + 1 = d ^ D) :
    (searchMachine hd D s t).stepS G (stq k D hk le_rfl v) = Sum.inr false := by
  simp [Machine.stepS, searchMachine, actF, stq, hv, hlast]

lemma stepS_advance {D k : ℕ} (hd : 0 < d) {s t v : Fin n} (hk : k < d ^ D) (hv : v ≠ t)
    (hk1 : k + 1 < d ^ D) :
    (searchMachine hd D s t).stepS G (stq k D hk le_rfl v)
      = Sum.inl (stq (k + 1) 0 hk1 (Nat.zero_le D) s) := by
  simp only [Machine.stepS, searchMachine, actF, nextF, stq, if_neg hv,
    if_neg (show ¬ k + 1 = d ^ D by omega)]
  simp only [kSucc, dif_pos hk1]
  rfl

/-- The walk from `s` following the base-`d` digits of `k`. -/
def Wk (G : LGraph n d) (hd : 0 < d) (s : Fin n) (k : ℕ) (j : ℕ) : Fin n :=
  G.walk s (fun i => digF hd k i) j

lemma Wk_zero (G : LGraph n d) (hd : 0 < d) (s : Fin n) (k : ℕ) : Wk G hd s k 0 = s := rfl

lemma Wk_succ (G : LGraph n d) (hd : 0 < d) (s : Fin n) (k j : ℕ) :
    Wk G hd s k (j + 1) = G.nbr (Wk G hd s k j) (digF hd k j) := rfl

lemma reach_Wk (G : LGraph n d) (hd : 0 < d) (s : Fin n) (k j : ℕ) :
    G.Reach s (Wk G hd s k j) := G.reach_walk s _ j

/-- If `t` occurs on the walk for sequence `k` at some step `j` with `i ≤ j ≤ D`, then from the
configuration at step `i` the machine halts with `true`. -/
lemma halts_true_of_hit {D : ℕ} (hd : 0 < d) {s t : Fin n} (k : ℕ) (hk : k < d ^ D) :
    ∀ (r i j : ℕ) (hi : i ≤ D), j - i = r → i ≤ j → j ≤ D → Wk G hd s k j = t →
      ∃ m, (searchMachine hd D s t).multi G m (stq k i hk hi (Wk G hd s k i))
        = Sum.inr true := by
  intro r
  induction r with
  | zero =>
      intro i j hi hr hij hjD hW
      have hij' : i = j := by omega
      subst hij'
      exact ⟨1, Machine.multi_succ_inr (stepS_found hd hk hi hW)⟩
  | succ r ih =>
      intro i j hi hr hij hjD hW
      by_cases hv : Wk G hd s k i = t
      · exact ⟨1, Machine.multi_succ_inr (stepS_found hd hk hi hv)⟩
      · have hiD : i < D := by omega
        obtain ⟨m, hm⟩ := ih (i + 1) j hiD (by omega) (by omega) hjD hW
        exact ⟨m + 1, by rw [Machine.multi_succ_inl (stepS_step (G := G) hd hk hiD hv)]; exact hm⟩

/-- If `t` never occurs on the walk for sequence `k`, the machine sweeps to the end of that
walk. -/
lemma sweep_to_end {D : ℕ} (hd : 0 < d) {s t : Fin n} (k : ℕ) (hk : k < d ^ D)
    (hno : ∀ j, j ≤ D → Wk G hd s k j ≠ t) :
    ∀ (i : ℕ) (hi : i ≤ D), ∃ m,
      (searchMachine hd D s t).multi G m (stq k i hk hi (Wk G hd s k i))
        = Sum.inl (stq k D hk le_rfl (Wk G hd s k D)) := by
  have key : ∀ (p i : ℕ) (hi : i ≤ D), D - i = p → ∃ m,
      (searchMachine hd D s t).multi G m (stq k i hk hi (Wk G hd s k i))
        = Sum.inl (stq k D hk le_rfl (Wk G hd s k D)) := by
    intro p
    induction p with
    | zero =>
        intro i hi hp
        have : i = D := by omega
        subst this
        exact ⟨0, rfl⟩
    | succ p ih =>
        intro i hi hp
        have hiD : i < D := by omega
        obtain ⟨m, hm⟩ := ih (i + 1) hiD (by omega)
        exact ⟨m + 1, by
          rw [Machine.multi_succ_inl (stepS_step (G := G) hd hk hiD (hno i hi))]
          exact hm⟩
  intro i hi
  exact key (D - i) i hi rfl

/-- If `t` occurs somewhere on a walk with index at least `k`, the machine started at sequence
`k` halts with `true`. -/
lemma halts_true {D : ℕ} (hd : 0 < d) {s t : Fin n} :
    ∀ (r k : ℕ) (hk : k < d ^ D), d ^ D - k = r →
      (∃ k' j, k ≤ k' ∧ k' < d ^ D ∧ j ≤ D ∧ Wk G hd s k' j = t) →
      ∃ m, (searchMachine hd D s t).multi G m (stq k 0 hk (Nat.zero_le D) s) = Sum.inr true := by
  intro r
  induction r with
  | zero => intro k hk hr _; omega
  | succ r ih =>
      rintro k hk hr ⟨k', j, hkk', hk', hj, hW⟩
      by_cases hex : ∃ j', j' ≤ D ∧ Wk G hd s k j' = t
      · obtain ⟨j', hj', hW'⟩ := hex
        exact halts_true_of_hit hd k hk j' 0 j' (Nat.zero_le D) (by omega) (Nat.zero_le j') hj' hW'
      · push_neg at hex
        have hno : ∀ j', j' ≤ D → Wk G hd s k j' ≠ t := hex
        have hklt : k < k' := by
          rcases eq_or_lt_of_le hkk' with rfl | hlt
          · exact absurd hW (hno j hj)
          · exact hlt
        have hk1 : k + 1 < d ^ D := by omega
        obtain ⟨m1, hm1⟩ := sweep_to_end (t := t) hd k hk hno 0 (Nat.zero_le D)
        have hm1' : (searchMachine hd D s t).multi G m1 (stq k 0 hk (Nat.zero_le D) s)
            = Sum.inl (stq k D hk le_rfl (Wk G hd s k D)) := hm1
        obtain ⟨m2, hm2⟩ := ih (k + 1) hk1 (by omega) ⟨k', j, by omega, hk', hj, hW⟩
        refine ⟨m1 + (m2 + 1), ?_⟩
        rw [Machine.multi_add hm1',
          Machine.multi_succ_inl (stepS_advance (G := G) hd hk (hno D le_rfl) hk1)]
        exact hm2

/-- If `t` occurs on no walk with index at least `k`, the machine started at sequence `k` halts
with `false`. -/
lemma halts_false {D : ℕ} (hd : 0 < d) {s t : Fin n} :
    ∀ (r k : ℕ) (hk : k < d ^ D), d ^ D - k = r →
      (∀ k' j, k ≤ k' → k' < d ^ D → j ≤ D → Wk G hd s k' j ≠ t) →
      ∃ m, (searchMachine hd D s t).multi G m (stq k 0 hk (Nat.zero_le D) s) = Sum.inr false := by
  intro r
  induction r with
  | zero => intro k hk hr _; omega
  | succ r ih =>
      intro k hk hr hno'
      have hno : ∀ j, j ≤ D → Wk G hd s k j ≠ t := fun j hj => hno' k j le_rfl hk hj
      obtain ⟨m1, hm1⟩ := sweep_to_end (t := t) hd k hk hno 0 (Nat.zero_le D)
      have hm1' : (searchMachine hd D s t).multi G m1 (stq k 0 hk (Nat.zero_le D) s)
          = Sum.inl (stq k D hk le_rfl (Wk G hd s k D)) := hm1
      by_cases hlast : k + 1 = d ^ D
      · refine ⟨m1 + 1, ?_⟩
        rw [Machine.multi_add hm1',
          Machine.multi_succ_inr (stepS_last (G := G) hd hk (hno D le_rfl) hlast)]
      · have hk1 : k + 1 < d ^ D := by omega
        obtain ⟨m2, hm2⟩ := ih (k + 1) hk1 (by omega)
          fun k'' j hk'' h1 h2 => hno' k'' j (by omega) h1 h2
        refine ⟨m1 + (m2 + 1), ?_⟩
        rw [Machine.multi_add hm1',
          Machine.multi_succ_inl (stepS_advance (G := G) hd hk (hno D le_rfl) hk1)]
        exact hm2

/-- Every sequence of `D` labels is the base-`d` expansion of some `k < d ^ D`. -/
lemma exists_code {d : ℕ} (hd : 0 < d) (D : ℕ) (c : ℕ → Fin d) :
    ∃ k, k < d ^ D ∧ ∀ i, i < D → dg d k i = (c i : ℕ) := by
  induction D generalizing c with
  | zero => exact ⟨0, by simp, by omega⟩
  | succ D ih =>
      obtain ⟨k', hk', hdig⟩ := ih (fun i => c (i + 1))
      have h0 : (c 0 : ℕ) < d := (c 0).isLt
      have hdiv : ((c 0 : ℕ) + d * k') / d = k' := by
        rw [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt h0, Nat.zero_add]
      refine ⟨(c 0 : ℕ) + d * k', ?_, ?_⟩
      · have hle : d * k' + d ≤ d * d ^ D := by
          have h1 : k' + 1 ≤ d ^ D := hk'
          calc d * k' + d = d * (k' + 1) := by ring
            _ ≤ d * d ^ D := Nat.mul_le_mul_left d h1
        have : d ^ (D + 1) = d * d ^ D := by ring
        omega
      · intro i hi
        match i with
        | 0 =>
            simp only [dg, pow_zero, Nat.div_one]
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
        | (i + 1) =>
            have hstep : dg d ((c 0 : ℕ) + d * k') (i + 1) = dg d k' i := by
              unfold dg
              rw [show d ^ (i + 1) = d * d ^ i by ring, ← Nat.div_div_eq_div_mul, hdiv]
            rw [hstep]
            exact hdig i (by omega)

lemma walk_congr (G : LGraph n d) (s : Fin n) (c c' : ℕ → Fin d) :
    ∀ (j : ℕ), (∀ i, i < j → c i = c' i) → G.walk s c j = G.walk s c' j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro h
      have hj : G.walk s c j = G.walk s c' j := ih fun i hi => h i (by omega)
      show G.nbr (G.walk s c j) (c j) = G.nbr (G.walk s c' j) (c' j)
      rw [hj, h j (by omega)]

/-- **Main construction.**  Undirected `s`-`t` connectivity in a `d`-regular graph of diameter at
most `D` is decided by a machine with `d ^ D * ((D + 1) * n)` configurations. -/
theorem exists_machine_of_diameter {n d : ℕ} (hd : 0 < d) (D : ℕ) (G : LGraph n d) (s t : Fin n)
    (hD : G.HasDiameterAtMost D) :
    ∃ M : Machine n d, Fintype.card M.State ≤ d ^ D * ((D + 1) * n) ∧ M.Decides G s t := by
  refine ⟨searchMachine hd D s t, le_of_eq (card_searchMachine hd D s t), ?_, ?_⟩
  · intro hreach
    obtain ⟨c, j, hj, hcj⟩ := hD s t hreach
    obtain ⟨k, hk, hdig⟩ := exists_code hd D c
    have hW : Wk G hd s k j = t := by
      have : Wk G hd s k j = G.walk s c j := by
        refine walk_congr G s _ c j ?_
        intro i hi
        exact Fin.ext (hdig i (by omega))
      rw [this, hcj]
    obtain ⟨m, hm⟩ :=
      halts_true (G := G) hd (d ^ D - 0) 0 (pow_pos hd D) rfl ⟨k, j, Nat.zero_le k, hk, hj, hW⟩
    exact ⟨m, hm⟩
  · intro hreach
    obtain ⟨m, hm⟩ := halts_false (G := G) (s := s) (t := t) hd (d ^ D - 0) 0 (pow_pos hd D) rfl
      (by
        intro k' j _ _ _ hW
        exact hreach (hW ▸ reach_Wk G hd s k' j))
    exact ⟨m, hm⟩


/-! ## Logarithmic space

`Fintype.card M.State ≤ a * n ^ k` says exactly that the machine's memory consists of
`O(log n)` bits, i.e. that it runs in logarithmic space. -/

lemma two_pow_clog_le (n : ℕ) (hn : 0 < n) : 2 ^ Nat.clog 2 n ≤ 2 * n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · simp [show n = 1 by omega]
  · have hpos : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) (by omega)
    have hlt : 2 ^ (Nat.clog 2 n - 1) < n := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
    calc 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n - 1) := by
          rw [← pow_succ']
          congr 1
          omega
      _ ≤ 2 * n := by omega

/-- **Undirected `s`-`t` connectivity in logarithmic space** (the final stage of Reingold's
algorithm, which is where the claim `SL = L` comes from).

For a fixed degree `d` and a fixed constant `C`, undirected `s`-`t` connectivity on
`d`-regular graphs on `n` vertices whose diameter is at most `C * log₂ n` — the situation
Reingold's expander transformation reduces the general problem to — is decided by a machine
whose number of configurations is bounded by a polynomial `a * n ^ k` in `n`, uniformly in `n`.
Equivalently, the machine uses `O(log n)` bits of work memory, i.e. it is a logarithmic-space
algorithm for undirected connectivity.

The machine only accesses the input graph through neighbour queries, and the bound on the number
of its configurations is the formal expression of its space usage. -/
theorem reingold_sl_l (d C : ℕ) (hd : 0 < d) :
    ∃ a k : ℕ, ∀ (n : ℕ) (G : LGraph n d) (s t : Fin n),
      G.HasDiameterAtMost (C * Nat.clog 2 n) →
      ∃ M : Machine n d, Fintype.card M.State ≤ a * n ^ k ∧ M.Decides G s t := by
  refine ⟨2 ^ (Nat.clog 2 d * C) * (C + 1), Nat.clog 2 d * C + 2, ?_⟩
  intro n G s t hD
  obtain ⟨M, hcard, hdec⟩ := exists_machine_of_diameter hd (C * Nat.clog 2 n) G s t hD
  refine ⟨M, ?_, hdec⟩
  have hn : 0 < n := by have := s.isLt; omega
  set e := Nat.clog 2 d with he
  set D := C * Nat.clog 2 n with hDdef
  have h1 : d ^ D ≤ 2 ^ (e * C) * n ^ (e * C) := by
    have hd2 : d ≤ 2 ^ e := Nat.le_pow_clog (by norm_num) d
    calc d ^ D ≤ (2 ^ e) ^ D := Nat.pow_le_pow_left hd2 D
      _ = (2 ^ Nat.clog 2 n) ^ (e * C) := by
          rw [← pow_mul, ← pow_mul, hDdef]
          congr 1
          ring
      _ ≤ (2 * n) ^ (e * C) := Nat.pow_le_pow_left (two_pow_clog_le n hn) _
      _ = 2 ^ (e * C) * n ^ (e * C) := by rw [mul_pow]
  have hc : Nat.clog 2 n ≤ n := Nat.clog_le_of_le_pow (le_of_lt n.lt_two_pow_self)
  have h2 : D + 1 ≤ (C + 1) * n := by
    have hcc : C * Nat.clog 2 n ≤ C * n := Nat.mul_le_mul_left C hc
    calc D + 1 = C * Nat.clog 2 n + 1 := rfl
      _ ≤ C * n + n := by omega
      _ = (C + 1) * n := by ring
  calc Fintype.card M.State ≤ d ^ D * ((D + 1) * n) := hcard
    _ ≤ 2 ^ (e * C) * n ^ (e * C) * (((C + 1) * n) * n) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul_right n h2)
    _ = 2 ^ (e * C) * (C + 1) * n ^ (e * C + 2) := by ring


/-! ## The model really does decide connectivity

The hypotheses of `reingold_sl_l` are not vacuous: *every* `d`-regular graph on `n` vertices has
diameter at most `n - 1`, so the search machine decides `s`-`t` connectivity for every input
graph — the point of the log-diameter hypothesis is only that it makes the space usage
logarithmic. -/

lemma reach_iff_exists_walk (hd : 0 < d) (G : LGraph n d) (s v : Fin n) :
    G.Reach s v ↔ ∃ (c : ℕ → Fin d) (j : ℕ), G.walk s c j = v := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨fun _ => ⟨0, hd⟩, 0, rfl⟩
    | tail _ hadj ih =>
        obtain ⟨c, j, hcj⟩ := ih
        obtain ⟨i, hi⟩ := hadj
        refine ⟨fun m => if m = j then i else c m, j + 1, ?_⟩
        show G.nbr (G.walk s _ j) _ = _
        rw [walk_congr G s (fun m => if m = j then i else c m) c j
          (fun m hm => by simp [Nat.ne_of_lt hm]), hcj]
        simpa using hi
  · rintro ⟨c, j, rfl⟩
    exact G.reach_walk s c j

/-- A walk that visits a vertex twice can be shortened. -/
lemma exists_walk_lt (G : LGraph n d) (s v : Fin n) :
    ∀ (j : ℕ) (c : ℕ → Fin d), G.walk s c j = v → ∃ (c' : ℕ → Fin d) (j' : ℕ),
      j' < n ∧ G.walk s c' j' = v := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro c hc
    rcases Nat.lt_or_ge j n with hj | hj
    · exact ⟨c, j, hj, hc⟩
    · have hcard : Fintype.card (Fin n) < Fintype.card (Fin (j + 1)) := by
        simp only [Fintype.card_fin]; omega
      obtain ⟨x, y, hxy, hfxy⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (j + 1) => G.walk s c (i : ℕ)) hcard
      -- put the two coinciding positions in increasing order
      obtain ⟨a, b, hab, hb, heq⟩ :
          ∃ a b : ℕ, a < b ∧ b ≤ j ∧ G.walk s c a = G.walk s c b := by
        rcases lt_or_gt_of_ne (fun h : (x : ℕ) = (y : ℕ) => hxy (Fin.ext h)) with h | h
        · exact ⟨(x : ℕ), (y : ℕ), h, Nat.lt_succ_iff.mp y.isLt, hfxy⟩
        · exact ⟨(y : ℕ), (x : ℕ), h, Nat.lt_succ_iff.mp x.isLt, hfxy.symm⟩
      set sh := b - a with hsh
      set c' : ℕ → Fin d := fun m => if m < a then c m else c (m + sh) with hc'
      have hstart : G.walk s c' a = G.walk s c b := by
        rw [walk_congr G s c' c a (fun m hm => by simp [hc', hm]), heq]
      have hrun : ∀ m, G.walk s c' (a + m) = G.walk s c (b + m) := by
        intro m
        induction m with
        | zero => simpa using hstart
        | succ m ihm =>
            show G.nbr (G.walk s c' (a + m)) (c' (a + m)) = _
            rw [ihm]
            have : c' (a + m) = c (b + m) := by
              simp only [hc', if_neg (by omega : ¬ a + m < a), hsh]
              congr 1
              omega
            rw [this]
            rfl
      have hfinal : G.walk s c' (j - sh) = v := by
        have h1 : j - sh = a + (j - b) := by omega
        have h2 : b + (j - b) = j := by omega
        rw [h1, hrun (j - b), h2, hc]
      exact ih (j - sh) (by omega) c' hfinal

/-- Every `d`-regular graph on `n` vertices has diameter at most `n - 1`. -/
lemma hasDiameterAtMost_card (hd : 0 < d) (G : LGraph n d) :
    G.HasDiameterAtMost (n - 1) := by
  intro u v huv
  obtain ⟨c, j, hcj⟩ := (reach_iff_exists_walk hd G u v).1 huv
  obtain ⟨c', j', hj', hc'⟩ := exists_walk_lt G u v j c hcj
  exact ⟨c', j', by omega, hc'⟩

/-- In particular, undirected `s`-`t` connectivity is decided by a machine of the above kind for
*every* input graph. -/
theorem exists_machine (hd : 0 < d) (G : LGraph n d) (s t : Fin n) :
    ∃ M : Machine n d, M.Decides G s t :=
  let ⟨M, _, hM⟩ := exists_machine_of_diameter hd (n - 1) G s t (hasDiameterAtMost_card hd G)
  ⟨M, hM⟩

end CS


#print axioms CS.reingold_sl_l
#print axioms CS.exists_machine_of_diameter
#print axioms CS.exists_machine

