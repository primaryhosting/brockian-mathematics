/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Undirected s-t connectivity in logarithmic space (`SL = L`)

This file develops a self-contained formalisation of the statement
"undirected s-t connectivity is decidable in logarithmic space".

## The model of computation

A log-space machine working on `n`-vertex graphs is modelled by
`CS.GraphMachine`: a family of *configuration spaces* `Conf n`, one for each
input size, together with

* an initial configuration `init n s t` (the machine starts knowing the two
  distinguished vertices, which take `O(log n)` bits to write down);
* a *query* function, selecting the single entry of the adjacency matrix that
  the machine inspects in the current configuration (this is the read-only
  input head: the input is never stored in the configuration);
* a deterministic transition `step`, depending only on the current
  configuration and the bit that was read;
* an output function `out`, which is `none` while the machine is still running.

The machine runs in space `O(log n)` exactly when its configuration space has
polynomial size, which is what `CS.GraphMachine.PolySize` records.  This is the
standard configuration-graph characterisation of log-space computation.

`CS.InLogspace P` says that some polynomially-sized machine decides `P`, where
"decides" means that the *first* output produced by the machine is the correct
answer (`CS.GraphMachine.Decides`).

## The result

`CS.reingold_sl_l` shows that undirected s-t connectivity (`CS.USTCON`) is
decided by such a machine, assuming the combinatorial core of Reingold's
theorem, stated here as `CS.UESHypothesis`: for every vertex count `n` there is
a *universal exploration sequence* of polynomial length, i.e. a single sequence
of vertex names `u 0, u 1, …` such that the greedy walk
"move to `u k` if it is adjacent to the current vertex, otherwise stay put"
started anywhere visits the whole connected component of its starting point.

`CS.exists_universal_seq` proves unconditionally that universal exploration
sequences always exist (with no bound on their length), so the content of
`CS.UESHypothesis` is exactly the polynomial length bound, which is the
combinatorial heart of Reingold's theorem.
-/

namespace CS

/-! ## Undirected graphs and connectivity -/

/-- An undirected graph on the vertex set `Fin n`, given by a symmetric
adjacency matrix. -/
def UGraph (n : ℕ) : Type := {A : Fin n → Fin n → Bool // ∀ u v, A u v = A v u}

instance (n : ℕ) : Fintype (UGraph n) := Subtype.fintype _

/-- Adjacency in an undirected graph. -/
def UGraph.Adj {n : ℕ} (G : UGraph n) (u v : Fin n) : Bool := G.1 u v

lemma UGraph.adj_symm {n : ℕ} (G : UGraph n) (u v : Fin n) : G.Adj u v = G.Adj v u := G.2 u v

/-- `Reach G s t` : the vertex `t` can be reached from `s` along edges of `G`. -/
def Reach {n : ℕ} (G : UGraph n) (s t : Fin n) : Prop :=
  Relation.ReflTransGen (fun u v => G.Adj u v = true) s t

/-- Undirected s-t connectivity, as a property of graph instances. -/
def USTCON : ∀ n : ℕ, UGraph n → Fin n → Fin n → Prop := fun _ G s t => Reach G s t

/-! ## Log-space machines on graphs -/

/-- A deterministic machine deciding properties of `n`-vertex undirected
graphs.  The input (the adjacency matrix) is only accessible through the
`query`/`step` interface: in each configuration the machine names one matrix
entry and its transition may depend on the value of that single bit. -/
structure GraphMachine where
  /-- The configuration space for inputs with `n` vertices. -/
  Conf : ℕ → Type
  /-- Configurations form a finite type. -/
  fintypeConf : ∀ n, Fintype (Conf n)
  /-- The initial configuration, given the two distinguished vertices. -/
  init : ∀ n, Fin n → Fin n → Conf n
  /-- The adjacency-matrix entry inspected in the current configuration. -/
  query : ∀ n, Conf n → Fin n × Fin n
  /-- The transition function, reading the queried bit. -/
  step : ∀ n, Conf n → Bool → Conf n
  /-- The output: `none` while the computation is still running. -/
  out : ∀ n, Conf n → Option Bool

attribute [instance] GraphMachine.fintypeConf

/-- The configuration after `k` steps. -/
def GraphMachine.run (M : GraphMachine) {n : ℕ} (G : UGraph n) (c : M.Conf n) : ℕ → M.Conf n
  | 0 => c
  | k + 1 =>
      M.step n (M.run G c k)
        (G.Adj (M.query n (M.run G c k)).1 (M.query n (M.run G c k)).2)

/-- The machine halts with answer `b`: the first output it produces is `b`. -/
def GraphMachine.Halts (M : GraphMachine) {n : ℕ} (G : UGraph n) (c : M.Conf n) (b : Bool) :
    Prop :=
  ∃ k, M.out n (M.run G c k) = some b ∧ ∀ j < k, M.out n (M.run G c j) = none

/-- The machine uses logarithmic space: its configuration space has
polynomially bounded size. -/
def GraphMachine.PolySize (M : GraphMachine) : Prop :=
  ∃ C d : ℕ, ∀ n : ℕ, Fintype.card (M.Conf n) ≤ C * (n + 1) ^ d

/-- The machine decides the property `P`. -/
def GraphMachine.Decides (M : GraphMachine)
    (P : ∀ n : ℕ, UGraph n → Fin n → Fin n → Prop) : Prop :=
  ∀ (n : ℕ) (G : UGraph n) (s t : Fin n),
    (P n G s t → M.Halts G (M.init n s t) true) ∧
      (¬ P n G s t → M.Halts G (M.init n s t) false)

/-- A property of graph instances is in log-space. -/
def InLogspace (P : ∀ n : ℕ, UGraph n → Fin n → Fin n → Prop) : Prop :=
  ∃ M : GraphMachine, M.PolySize ∧ M.Decides P

/-! ## Universal exploration sequences -/

/-- The greedy walk driven by the sequence `u`: at step `k` the walker moves to
`u k` if that vertex is adjacent to its current position, and stays put
otherwise. -/
def walk {n : ℕ} (G : UGraph n) (u : ℕ → Fin n) (s : Fin n) : ℕ → Fin n
  | 0 => s
  | k + 1 => if G.Adj (walk G u s k) (u k) then u k else walk G u s k

lemma walk_succ {n : ℕ} (G : UGraph n) (u : ℕ → Fin n) (s : Fin n) (k : ℕ) :
    walk G u s (k + 1) = if G.Adj (walk G u s k) (u k) then u k else walk G u s k := rfl

/-- The walk never leaves the connected component of its starting point. -/
lemma reach_walk {n : ℕ} (G : UGraph n) (u : ℕ → Fin n) (s : Fin n) (k : ℕ) :
    Reach G s (walk G u s k) := by
  induction k with
  | zero => exact Relation.ReflTransGen.refl
  | succ k ih =>
      rw [walk_succ]
      by_cases h : G.Adj (walk G u s k) (u k) = true
      · rw [if_pos h]; exact ih.tail h
      · rw [if_neg h]; exact ih

/-- The walk up to time `k` only depends on the first `k` entries of the
sequence. -/
lemma walk_congr {n : ℕ} (G : UGraph n) (u v : ℕ → Fin n) (s : Fin n) (k : ℕ)
    (h : ∀ i < k, u i = v i) : walk G u s k = walk G v s k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk : ∀ i < k, u i = v i := fun i hi => h i (by omega)
      rw [walk_succ, walk_succ, ih hk, h k (by omega)]

/-- `u` is a universal exploration sequence of length `L` for `n`-vertex
graphs: from any start vertex, the first `L` steps of the greedy walk visit
every vertex of the connected component of the start. -/
def IsUniversalSeq {n : ℕ} (u : ℕ → Fin n) (L : ℕ) : Prop :=
  ∀ (G : UGraph n) (s t : Fin n), Reach G s t → ∃ k ≤ L, walk G u s k = t

/-- **The combinatorial core of Reingold's theorem.**  There are universal
exploration sequences of polynomial length. -/
def UESHypothesis : Prop :=
  ∃ C d : ℕ, ∀ n : ℕ, 0 < n → ∃ u : ℕ → Fin n, IsUniversalSeq u (C * (n + 1) ^ d)

/-! ## The machine built from a universal exploration sequence -/

section Construction

variable (C d : ℕ) (f : ∀ n : ℕ, 0 < n → ℕ → Fin n)

/-- The length bound used by the machine. -/
def bnd (n : ℕ) : ℕ := C * (n + 1) ^ d

/-- The exploration sequence used at size `n`; the extra vertex argument is
only a dummy making the definition total when `n = 0`. -/
def useq (n : ℕ) (v : Fin n) (i : ℕ) : Fin n := if h : 0 < n then f n h i else v

lemma useq_eq {n : ℕ} (h : 0 < n) (v : Fin n) : useq f n v = f n h := by
  funext i; simp [useq, h]

/-- The log-space machine that follows the exploration sequence. -/
def uesMachine : GraphMachine where
  Conf n := Fin n × Fin n × Fin (bnd C d n + 1)
  fintypeConf _ := inferInstance
  init _ s t := (s, t, ⟨0, Nat.succ_pos _⟩)
  query n c := (c.1, useq f n c.1 c.2.2.1)
  step n c b :=
    if h : c.2.2.1 < bnd C d n then
      ((if b then useq f n c.1 c.2.2.1 else c.1), c.2.1, ⟨c.2.2.1 + 1, by omega⟩)
    else c
  out n c :=
    if c.1 = c.2.1 then some true
    else if c.2.2.1 = bnd C d n then some false else none

lemma uesMachine_run {n : ℕ} (hn : 0 < n) (G : UGraph n) (s t : Fin n) (k : ℕ) :
    (uesMachine C d f).run G ((uesMachine C d f).init n s t) k =
      (walk G (f n hn) s (min k (bnd C d n)), t,
        ⟨min k (bnd C d n), by omega⟩) := by
  induction k with
  | zero => simp [GraphMachine.run, uesMachine, walk]
  | succ k ih =>
      rw [GraphMachine.run, ih]
      by_cases hlt : min k (bnd C d n) < bnd C d n
      · have hk : k < bnd C d n := by omega
        have h1 : min k (bnd C d n) = k := by omega
        have h2 : min (k + 1) (bnd C d n) = k + 1 := by omega
        simp only [uesMachine, h1, useq_eq f hn]
        rw [dif_pos (by omega : k < bnd C d n)]
        simp only [h2, walk_succ]
      · have hk : min k (bnd C d n) = bnd C d n := by omega
        have h2 : min (k + 1) (bnd C d n) = bnd C d n := by omega
        simp only [uesMachine, hk, h2]
        rw [dif_neg (by omega : ¬ bnd C d n < bnd C d n)]

lemma uesMachine_polySize : (uesMachine C d f).PolySize := by
  refine ⟨C + 1, d + 2, fun n => ?_⟩
  have : Fintype.card ((uesMachine C d f).Conf n) = n * (n * (bnd C d n + 1)) := by
    simp [uesMachine, Fintype.card_prod]
  rw [this]
  have h1 : n * (n * (bnd C d n + 1)) ≤ (n + 1) * ((n + 1) * (C * (n + 1) ^ d + 1)) := by
    have : bnd C d n = C * (n + 1) ^ d := rfl
    rw [this]
    exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) le_rfl)
  refine h1.trans ?_
  have h2 : (n + 1) * ((n + 1) * (C * (n + 1) ^ d + 1)) = (n + 1) ^ 2 * (C * (n + 1) ^ d + 1) := by
    ring
  rw [h2]
  have h3 : C * (n + 1) ^ d + 1 ≤ (C + 1) * (n + 1) ^ d := by
    have : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    nlinarith [Nat.one_le_pow d (n + 1) (by omega : 0 < n + 1)]
  calc (n + 1) ^ 2 * (C * (n + 1) ^ d + 1) ≤ (n + 1) ^ 2 * ((C + 1) * (n + 1) ^ d) :=
        Nat.mul_le_mul_left _ h3
    _ = (C + 1) * (n + 1) ^ (d + 2) := by ring

lemma uesMachine_decides
    (hf : ∀ (n : ℕ) (hn : 0 < n), IsUniversalSeq (f n hn) (bnd C d n)) :
    (uesMachine C d f).Decides USTCON := by
  intro n G s t
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) s.isLt
  have hne : ∀ j, ¬ Reach G s t → walk G (f n hn) s j ≠ t := by
    intro j h hj
    exact h (hj ▸ reach_walk G (f n hn) s j)
  constructor
  · intro hP
    obtain ⟨k, hkL, hkt⟩ := hf n hn G s t hP
    have hex : ∃ m, walk G (f n hn) s m = t := ⟨k, hkt⟩
    have hk0 : walk G (f n hn) s (Nat.find hex) = t := Nat.find_spec hex
    have hk0le : Nat.find hex ≤ bnd C d n := le_trans (Nat.find_min' hex hkt) hkL
    refine ⟨Nat.find hex, ?_, ?_⟩
    · rw [uesMachine_run C d f hn G s t]
      have : min (Nat.find hex) (bnd C d n) = Nat.find hex := by omega
      simp [uesMachine, this, hk0]
    · intro j hj
      rw [uesMachine_run C d f hn G s t]
      have hjL : min j (bnd C d n) = j := by omega
      have hjt : walk G (f n hn) s j ≠ t := Nat.find_min hex hj
      simp [uesMachine, hjL, hjt]
      omega
  · intro hP
    refine ⟨bnd C d n, ?_, ?_⟩
    · rw [uesMachine_run C d f hn G s t]
      simp [uesMachine, hne _ hP]
    · intro j hj
      rw [uesMachine_run C d f hn G s t]
      have hjL : min j (bnd C d n) = j := by omega
      simp [uesMachine, hjL, hne _ hP]
      omega

theorem reingold_sl_l (H : UESHypothesis) : InLogspace USTCON := by
  obtain ⟨C, d, hC⟩ := H
  choose f hf using hC
  exact ⟨uesMachine C d f, uesMachine_polySize C d f, uesMachine_decides C d f hf⟩

end Construction

/-! ## Universal exploration sequences always exist

The hypothesis `UESHypothesis` used above is not vacuous: universal exploration
sequences do exist for every vertex count.  The elementary argument below gives
no useful bound on their length; obtaining a *polynomial* length bound is the
combinatorial heart of Reingold's theorem. -/

instance (n : ℕ) : DecidableEq (UGraph n) := Subtype.instDecidableEq

/-- Reachability in an undirected graph is symmetric. -/
lemma reach_symm {n : ℕ} {G : UGraph n} {s t : Fin n} (h : Reach G s t) : Reach G t s := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hb hbt ih =>
      refine Relation.ReflTransGen.head ?_ ih
      rw [G.adj_symm]; exact hbt

/-- Concatenation of two instruction sequences. -/
def catSeq {n : ℕ} (ℓ : ℕ) (u v : ℕ → Fin n) (i : ℕ) : Fin n :=
  if i < ℓ then u i else v (i - ℓ)

lemma walk_catSeq_le {n : ℕ} (G : UGraph n) (ℓ : ℕ) (u v : ℕ → Fin n) (s : Fin n) {k : ℕ}
    (hk : k ≤ ℓ) : walk G (catSeq ℓ u v) s k = walk G u s k := by
  refine walk_congr G _ _ s k (fun i hi => ?_)
  simp [catSeq, show i < ℓ by omega]

lemma walk_catSeq_add {n : ℕ} (G : UGraph n) (ℓ : ℕ) (u v : ℕ → Fin n) (s : Fin n) (j : ℕ) :
    walk G (catSeq ℓ u v) s (ℓ + j) = walk G v (walk G u s ℓ) j := by
  induction j with
  | zero => simpa using walk_catSeq_le G ℓ u v s (le_refl ℓ)
  | succ j ih =>
      have hℓ : ℓ + (j + 1) = (ℓ + j) + 1 := by omega
      rw [hℓ, walk_succ, walk_succ, ih]
      have : catSeq ℓ u v (ℓ + j) = v j := by
        simp [catSeq, show ¬ (ℓ + j < ℓ) by omega]
      rw [this]

/-- From any vertex one can steer the walk to any vertex of its component. -/
lemma exists_seq_reaching {n : ℕ} (G : UGraph n) {v t : Fin n} (h : Reach G v t) :
    ∃ (m : ℕ) (w : ℕ → Fin n), walk G w v m = t := by
  induction h with
  | refl => exact ⟨0, fun _ => v, rfl⟩
  | @tail x y _ hxy ih =>
      obtain ⟨m, w, hw⟩ := ih
      refine ⟨m + 1, catSeq m w (fun _ => y), ?_⟩
      have h1 : walk G (catSeq m w fun _ => y) v (m + 1) =
          walk G (fun _ => y) (walk G w v m) 1 := walk_catSeq_add G m w _ v 1
      rw [h1, hw, walk_succ]
      show (if G.Adj x y then y else x) = y
      simp [hxy]

private lemma exists_seq_for_finset {n : ℕ} (hn : 0 < n)
    (S : Finset (UGraph n × Fin n × Fin n)) :
    ∃ (L : ℕ) (u : ℕ → Fin n), ∀ p ∈ S, Reach p.1 p.2.1 p.2.2 →
      ∃ k ≤ L, walk p.1 u p.2.1 k = p.2.2 := by
  classical
  induction S using Finset.induction with
  | empty => exact ⟨0, (fun _ => ⟨0, hn⟩), by simp⟩
  | insert p S _ ih =>
      obtain ⟨L, u, hu⟩ := ih
      obtain ⟨G, s, t⟩ := p
      by_cases hst : Reach G s t
      · have hv : Reach G (walk G u s L) t :=
          (reach_symm (reach_walk G u s L)).trans hst
        obtain ⟨m, w, hw⟩ := exists_seq_reaching G hv
        refine ⟨L + m, catSeq L u w, ?_⟩
        rintro q hq hq'
        rcases Finset.mem_insert.1 hq with rfl | hqS
        · refine ⟨L + m, le_rfl, ?_⟩
          rw [walk_catSeq_add G L u w s m, hw]
        · obtain ⟨k, hkL, hk⟩ := hu q hqS hq'
          exact ⟨k, by omega, by rw [walk_catSeq_le q.1 L u w q.2.1 hkL]; exact hk⟩
      · refine ⟨L, u, ?_⟩
        rintro q hq hq'
        rcases Finset.mem_insert.1 hq with rfl | hqS
        · exact absurd hq' hst
        · exact hu q hqS hq'

/-- **Universal exploration sequences exist.**  For every positive vertex count
there is a finite instruction sequence whose greedy walk explores the whole
connected component of its starting vertex, in every `n`-vertex undirected
graph and from every starting vertex. -/
theorem exists_universal_seq (n : ℕ) (hn : 0 < n) :
    ∃ (L : ℕ) (u : ℕ → Fin n), IsUniversalSeq u L := by
  classical
  obtain ⟨L, u, hu⟩ := exists_seq_for_finset hn (Finset.univ : Finset (UGraph n × Fin n × Fin n))
  exact ⟨L, u, fun G s t h => hu (G, s, t) (Finset.mem_univ _) h⟩

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

