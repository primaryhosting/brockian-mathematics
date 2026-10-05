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

set_option autoImplicit false
set_option maxHeartbeats 1000000

attribute [local instance 0] Classical.propDecidable

namespace CS

/-!
## Overview

This file formalises Reingold's theorem `SL = L`, i.e. that undirected `s`-`t`
connectivity (`USTCON`) can be decided in logarithmic space, in the following
form.

* Section 1 sets up a space-bounded machine model `SMachine`: a deterministic
  machine with a finite state space which reads its input only through oracle
  queries (a read-only input tape with random access).  A machine uses space
  `log₂ (Fintype.card S)`, so *logarithmic space* means a family of machines
  whose state spaces have polynomially bounded cardinality.
* Section 2 proves that such machines compose (`SMachine.comp_computes`): an
  outer machine using an oracle which is itself computed by an inner
  space-bounded machine can be simulated by a single machine whose state space
  is the product of the two.  This is the usual "recompute instead of store"
  closure of logspace under composition.
* Section 3 defines undirected `s`-`t` connectivity and the predicate
  `USTCON_in_L`.
* Section 4 builds, *unconditionally*, an explicit machine `searchM` which
  decides connectivity in a `D`-regular graph presented by a rotation map, all
  of whose components have diameter at most `d`, by trying all `D ^ d` walks of
  length `d` in turn (`searchM_computes`).  Its state space has cardinality
  `O(n² · N³ · D^d · d)`, which is polynomial when `D` is constant and
  `D ^ d` is polynomial; this is the final phase of Reingold's algorithm.
* Section 5 packages the deep combinatorial content of Reingold's theorem — the
  zig-zag/derandomised-squaring transformation of an arbitrary undirected graph
  into a constant-degree graph of logarithmic diameter, computable in
  logarithmic space and preserving connectivity — as the structure
  `ReingoldReduction`, and derives from it the main theorem `reingold_sl_l`:
  undirected `s`-`t` connectivity is decidable in logarithmic space.

Two caveats about the scope of what is proved here.  First, the existence of a
`ReingoldReduction` (the zig-zag construction and its spectral analysis) is a
hypothesis of `reingold_sl_l`, not something proved here; everything else — the
search machine, its correctness, the composition theorem, and the space
accounting — is proved unconditionally.  Second, `USTCON_in_L` asserts the
existence of a family of machines indexed by the input length without imposing
a further uniformity condition on the family; the family produced by
`reingold_sl_l` is nevertheless given by explicit computable data (`searchM`
composed with the given transducer).
-/

/-!
## A space-bounded machine model

A `SMachine Q A I O S` is a deterministic machine with (finite) state space `S`
which reads its input only through *queries*: in state `s` it asks the oracle
`f : Q → A` the question `query s` and uses the answer to move to the next state.
It starts in state `init i` on input `i : I` and halts as soon as `out s` is
`some o`, which is then its output.

The *space* used by such a machine is `log₂ (card S)`, so a family of machines
with `card S ≤ poly(n)` is exactly a logarithmic-space machine family (the input
being read through the oracle, i.e. a read-only input tape with random access).
-/

/-- A deterministic oracle-query machine with state space `S`. -/
structure SMachine (Q A I O S : Type) where
  /-- Initial state on a given input. -/
  init : I → S
  /-- The oracle query asked in a given state. -/
  query : S → Q
  /-- The transition function, given the answer to the query. -/
  step : S → A → S
  /-- Output of a halting state (`none` if the state is not halting). -/
  out : S → Option O

namespace SMachine

variable {Q A I O S : Type}

/-- One step of the machine relative to the oracle `f`; halting states are fixed. -/
def stepOnce (M : SMachine Q A I O S) (f : Q → A) (s : S) : S :=
  if (M.out s).isSome then s else M.step s (f (M.query s))

/-- The state after `T` steps starting from `s`. -/
def run (M : SMachine Q A I O S) (f : Q → A) (s : S) (T : ℕ) : S :=
  (M.stepOnce f)^[T] s

/-- The output after `T` steps on input `i`. -/
def eval (M : SMachine Q A I O S) (f : Q → A) (i : I) (T : ℕ) : Option O :=
  M.out (M.run f (M.init i) T)

/-- `M` computes the function `g` relative to the oracle `f`. -/
def Computes (M : SMachine Q A I O S) (f : Q → A) (g : I → O) : Prop :=
  ∀ i, ∃ T, M.eval f i T = some (g i)

@[simp] theorem run_zero (M : SMachine Q A I O S) (f : Q → A) (s : S) :
    M.run f s 0 = s := rfl

theorem run_one (M : SMachine Q A I O S) (f : Q → A) (s : S) :
    M.run f s 1 = M.stepOnce f s := rfl

theorem run_succ (M : SMachine Q A I O S) (f : Q → A) (s : S) (T : ℕ) :
    M.run f s (T + 1) = M.stepOnce f (M.run f s T) :=
  Function.iterate_succ_apply' _ _ _

theorem run_add (M : SMachine Q A I O S) (f : Q → A) (s : S) (T₁ T₂ : ℕ) :
    M.run f s (T₁ + T₂) = M.run f (M.run f s T₁) T₂ := by
  simp [run, add_comm T₁ T₂, Function.iterate_add_apply]

theorem stepOnce_of_halt {M : SMachine Q A I O S} {f : Q → A} {s : S} {o : O}
    (h : M.out s = some o) : M.stepOnce f s = s := by
  simp [stepOnce, h]

theorem run_of_halt {M : SMachine Q A I O S} {f : Q → A} {s : S} {o : O}
    (h : M.out s = some o) (T : ℕ) : M.run f s T = s :=
  Function.iterate_fixed (stepOnce_of_halt h) T

theorem out_run_mono {M : SMachine Q A I O S} {f : Q → A} {s : S} {o : O} {T T' : ℕ}
    (h : M.out (M.run f s T) = some o) (hT : T ≤ T') :
    M.out (M.run f s T') = some o := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hT
  rw [run_add, run_of_halt h]
  exact h

end SMachine

/-!
## Composition of space-bounded machines

If `M₂` computes the oracle `h` from the oracle `f`, and `M₁` computes `g` from
the oracle `h`, then the two can be composed into a single machine with state
space `S₁ × S₂` computing `g` from `f`: whenever the outer machine asks a
question, the inner machine is run from scratch to answer it.  This is the usual
"recompute instead of store" argument showing that logspace computations are
closed under composition.
-/

namespace SMachine

variable {Q A Q' A' I O S₁ S₂ : Type}

/-- The composition of an outer machine `M₁` (using oracle `h`) with an inner
machine `M₂` (computing `h` from `f`). -/
def comp (M₁ : SMachine Q' A' I O S₁) (M₂ : SMachine Q A Q' A' S₂) :
    SMachine Q A I O (S₁ × S₂) where
  init i := (M₁.init i, M₂.init (M₁.query (M₁.init i)))
  query p := M₂.query p.2
  step p a :=
    match M₂.out p.2 with
    | some b => (M₁.step p.1 b, M₂.init (M₁.query (M₁.step p.1 b)))
    | none => (p.1, M₂.step p.2 a)
  out p := M₁.out p.1

theorem comp_computes {M₁ : SMachine Q' A' I O S₁} {M₂ : SMachine Q A Q' A' S₂}
    {f : Q → A} {h : Q' → A'} {g : I → O}
    (h₂ : M₂.Computes f h) (h₁ : M₁.Computes h g) :
    (M₁.comp M₂).Computes f g := by
  classical
  -- Answering one query of the outer machine.
  have inner : ∀ s₁ : S₁, M₁.out s₁ = none →
      ∃ T, (M₁.comp M₂).run f (s₁, M₂.init (M₁.query s₁)) T =
        (M₁.stepOnce h s₁, M₂.init (M₁.query (M₁.stepOnce h s₁))) := by
    intro s₁ hs₁
    obtain ⟨T₁, hT₁⟩ := h₂ (M₁.query s₁)
    have hex : ∃ T, (M₂.out (M₂.run f (M₂.init (M₁.query s₁)) T)).isSome := by
      refine ⟨T₁, ?_⟩
      rw [show M₂.out (M₂.run f (M₂.init (M₁.query s₁)) T₁) = some (h (M₁.query s₁)) from hT₁]
      rfl
    classical
    set T₀ := Nat.find hex with hT₀def
    have hfind : (M₂.out (M₂.run f (M₂.init (M₁.query s₁)) T₀)).isSome := Nat.find_spec hex
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hfind
    -- the answer found is the correct one
    have hbval : b = h (M₁.query s₁) := by
      have h1 : M₂.out (M₂.run f (M₂.init (M₁.query s₁)) (max T₀ T₁)) = some b :=
        SMachine.out_run_mono hb (le_max_left _ _)
      have h2 : M₂.out (M₂.run f (M₂.init (M₁.query s₁)) (max T₀ T₁)) =
          some (h (M₁.query s₁)) := SMachine.out_run_mono hT₁ (le_max_right _ _)
      exact Option.some.inj (h1.symm.trans h2)
    -- the composed machine simulates the inner machine
    have sim : ∀ k, k ≤ T₀ → (M₁.comp M₂).run f (s₁, M₂.init (M₁.query s₁)) k =
        (s₁, M₂.run f (M₂.init (M₁.query s₁)) k) := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        have hk' : k ≤ T₀ := Nat.le_of_succ_le hk
        have hnot : ¬ (M₂.out (M₂.run f (M₂.init (M₁.query s₁)) k)).isSome :=
          Nat.find_min hex (by omega)
        have hnone : M₂.out (M₂.run f (M₂.init (M₁.query s₁)) k) = none :=
          Option.not_isSome_iff_eq_none.mp hnot
        rw [SMachine.run_succ, ih hk', SMachine.run_succ]
        simp only [SMachine.stepOnce, SMachine.comp, hs₁, hnone]
        simp
    refine ⟨T₀ + 1, ?_⟩
    rw [SMachine.run_succ, sim T₀ le_rfl]
    simp only [SMachine.stepOnce, SMachine.comp, hs₁, hb]
    simp only [Option.isSome_none, Bool.false_eq_true, if_false]
    rw [hbval]
  -- Simulating the outer machine step by step.
  have outer : ∀ (i : I) (k : ℕ), ∃ T, (M₁.comp M₂).run f ((M₁.comp M₂).init i) T =
      (M₁.run h (M₁.init i) k,
        M₂.init (M₁.query (M₁.run h (M₁.init i) k))) := by
    intro i k
    induction k with
    | zero => exact ⟨0, rfl⟩
    | succ k ih =>
      obtain ⟨T, hT⟩ := ih
      rcases Option.eq_none_or_eq_some (M₁.out (M₁.run h (M₁.init i) k)) with hnone | ⟨o, ho⟩
      · obtain ⟨T', hT'⟩ := inner (M₁.run h (M₁.init i) k) hnone
        refine ⟨T + T', ?_⟩
        rw [SMachine.run_add, hT, hT', SMachine.run_succ]
      · refine ⟨T, ?_⟩
        rw [SMachine.run_succ, SMachine.stepOnce_of_halt ho]
        exact hT
  intro i
  obtain ⟨k, hk⟩ := h₁ i
  obtain ⟨T, hT⟩ := outer i k
  exact ⟨T, by rw [SMachine.eval, hT]; exact hk⟩

end SMachine

/-!
## Undirected `s`-`t` connectivity

The input graph is given by its adjacency matrix `adj : Fin n → Fin n → Bool`,
assumed symmetric.  `AdjReach adj s t` says that `t` is reachable from `s`.
-/

/-- Reachability in the graph with adjacency matrix `adj`. -/
def AdjReach {n : ℕ} (adj : Fin n → Fin n → Bool) (s t : Fin n) : Prop :=
  Relation.ReflTransGen (fun u v => adj u v = true) s t

/-- The result of following the sequence of edge labels `l` from the vertex `v`
in the graph described by the rotation map `rot`. -/
def walkL {N D : ℕ} (rot : Fin N → Fin D → Fin N) : Fin N → List (Fin D) → Fin N
  | v, [] => v
  | v, a :: l => walkL rot (rot v a) l

/-- `t` can be reached from `s` by a walk of length at most `d` in the
`D`-regular graph described by the rotation map `rot`. -/
def ReachWithin {N D : ℕ} (rot : Fin N → Fin D → Fin N) (d : ℕ) (s t : Fin N) : Prop :=
  ∃ l : List (Fin D), l.length ≤ d ∧ walkL rot s l = t

/-!
## Undirected connectivity is in logspace

`USTCON_in_L` says: there is a family of machines with polynomially many states
(i.e. logarithmic space) which, given the adjacency matrix of an undirected
graph on `n` vertices as an oracle, decides reachability between the two input
vertices.
-/

/-- Undirected `s`-`t` connectivity is decidable in logarithmic space. -/
def USTCON_in_L : Prop :=
  ∃ (c : ℕ) (S : ℕ → Type) (inst : ∀ n, Fintype (S n))
      (M : ∀ n, SMachine (Fin n × Fin n) Bool (Fin n × Fin n) Bool (S n)),
    (∀ n, @Fintype.card (S n) (inst n) ≤ (n + 2) ^ c) ∧
    ∀ (n : ℕ) (adj : Fin n → Fin n → Bool), (∀ u v, adj u v = adj v u) →
      (M n).Computes (fun p => adj p.1 p.2)
        (fun p => decide (AdjReach adj p.1 p.2))

/-!
## The exhaustive-search machine

For a `D`-regular graph presented by a rotation map, all of whose connected
components have diameter at most `d`, connectivity can be decided by trying all
`D ^ d` walks of length `d` in turn, keeping only the current walk index, the
position along it, and the current vertex.  This uses `O(d log D + log N)` bits,
which is logarithmic when `D` is constant and `d = O(log N)`.
-/

/-- The state of the exhaustive-search machine. -/
structure SearchState (n N D d : ℕ) where
  /-- The source vertex of the original instance. -/
  s : Fin n
  /-- The target vertex of the original instance. -/
  t : Fin n
  /-- Which phase the machine is in. -/
  tag : Fin 4
  /-- The image of the source vertex. -/
  sp : Fin N
  /-- The image of the target vertex. -/
  tp : Fin N
  /-- The current vertex of the walk. -/
  v : Fin N
  /-- The index of the walk currently being tried. -/
  j : Fin (D ^ d)
  /-- The position along the current walk. -/
  i : Fin (d + 1)
  /-- Whether the target has been seen so far. -/
  found : Bool

namespace SearchState

variable {n N D d : ℕ}

/-- `SearchState` is a product of finite types. -/
def equivProd (n N D d : ℕ) : SearchState n N D d ≃
    (Fin n × Fin n × Fin 4 × Fin N × Fin N × Fin N × Fin (D ^ d) × Fin (d + 1) × Bool) where
  toFun st := (st.s, st.t, st.tag, st.sp, st.tp, st.v, st.j, st.i, st.found)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1,
    p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2⟩
  left_inv := by intro st; cases st; rfl
  right_inv := by intro p; rfl

instance : Fintype (SearchState n N D d) := Fintype.ofEquiv _ (equivProd n N D d).symm

theorem card_eq (n N D d : ℕ) : Fintype.card (SearchState n N D d) =
    n * (n * (4 * (N * (N * (N * (D ^ d * ((d + 1) * 2))))))) := by
  rw [Fintype.card_congr (equivProd n N D d)]
  simp [Fintype.card_prod]

end SearchState

/-- An explicit enumeration of the words of length `d` over the alphabet `Fin D`
(the base-`D` digit expansion). -/
def wordEquiv (D d : ℕ) : Fin (D ^ d) ≃ (Fin d → Fin D) := finFunctionFinEquiv.symm

/-- The vertex reached after `k` steps of the walk with label word `w`. -/
def walkFin {N D d : ℕ} (rot : Fin N → Fin D → Fin N) (v0 : Fin N) (w : Fin d → Fin D)
    (k : ℕ) : Fin N :=
  walkL rot v0 ((List.ofFn w).take k)

theorem walkL_append {N D : ℕ} (rot : Fin N → Fin D → Fin N) (v : Fin N) (l : List (Fin D))
    (a : Fin D) : walkL rot v (l ++ [a]) = rot (walkL rot v l) a := by
  induction l generalizing v with
  | nil => rfl
  | cons b l ih => simp [walkL, ih]

@[simp] theorem walkFin_zero {N D d : ℕ} (rot : Fin N → Fin D → Fin N) (v0 : Fin N)
    (w : Fin d → Fin D) : walkFin rot v0 w 0 = v0 := rfl

theorem walkFin_succ {N D d : ℕ} (rot : Fin N → Fin D → Fin N) (v0 : Fin N) (w : Fin d → Fin D)
    {k : ℕ} (hk : k < d) :
    walkFin rot v0 w (k + 1) = rot (walkFin rot v0 w k) (w ⟨k, hk⟩) := by
  have h : (List.ofFn w).take (k + 1) = (List.ofFn w).take k ++ [w ⟨k, hk⟩] := by
    rw [List.take_add_one]
    congr 1
    simp [hk]
  unfold walkFin
  rw [h, walkL_append]

/-- A walk of length at most `d` is the same thing as a prefix of a walk with a
label word of length exactly `d`. -/
theorem reachWithin_iff {N D d : ℕ} (hD : 0 < D) (rot : Fin N → Fin D → Fin N) (s t : Fin N) :
    ReachWithin rot d s t ↔ ∃ (w : Fin d → Fin D) (m : ℕ), m ≤ d ∧ walkFin rot s w m = t := by
  constructor
  · rintro ⟨l, hlen, hl⟩
    refine ⟨fun i => if h : i.1 < l.length then l[i.1] else ⟨0, hD⟩, l.length, hlen, ?_⟩
    have key : (List.ofFn (fun i : Fin d =>
        if h : i.1 < l.length then l[i.1] else (⟨0, hD⟩ : Fin D))).take l.length = l := by
      apply List.ext_getElem
      · simp; omega
      · intro k h1 h2
        simp only [List.getElem_take, List.getElem_ofFn]
        simp [h2]
    unfold walkFin
    rw [key]
    exact hl
  · rintro ⟨w, m, hm, hw⟩
    exact ⟨(List.ofFn w).take m, by simp, hw⟩

/-- The exhaustive-search machine. -/
def searchM (n N D d : ℕ) (hD : 0 < D) (hNn : 0 < n → 0 < N) :
    SMachine ((Fin N × Fin D) ⊕ Fin n) (Fin N) (Fin n × Fin n) Bool (SearchState n N D d) where
  init p :=
    ⟨p.1, p.2, 0, ⟨0, hNn (lt_of_le_of_lt (Nat.zero_le _) p.1.isLt)⟩,
      ⟨0, hNn (lt_of_le_of_lt (Nat.zero_le _) p.1.isLt)⟩,
      ⟨0, hNn (lt_of_le_of_lt (Nat.zero_le _) p.1.isLt)⟩,
      ⟨0, Nat.pow_pos hD⟩, ⟨0, Nat.succ_pos d⟩, false⟩
  query st :=
    if st.tag = 0 then Sum.inr st.s
    else if st.tag = 1 then Sum.inr st.t
    else Sum.inl (st.v,
      if h : st.i.1 < d then wordEquiv D d st.j ⟨st.i.1, h⟩ else ⟨0, hD⟩)
  step st a :=
    if st.tag = 0 then { st with tag := 1, sp := a }
    else if st.tag = 1 then
      ⟨st.s, st.t, 2, st.sp, a, st.sp, ⟨0, Nat.pow_pos hD⟩, ⟨0, Nat.succ_pos d⟩,
        decide (st.sp = a)⟩
    else if st.tag = 2 then
      (if h : st.i.1 < d then
        ⟨st.s, st.t, st.tag, st.sp, st.tp, a, st.j, ⟨st.i.1 + 1, by omega⟩,
          st.found || decide (a = st.tp)⟩
      else if h2 : st.j.1 + 1 < D ^ d then
        ⟨st.s, st.t, st.tag, st.sp, st.tp, st.sp, ⟨st.j.1 + 1, h2⟩, ⟨0, Nat.succ_pos d⟩,
          st.found⟩
      else { st with tag := 3 })
    else st
  out st := if st.tag = 3 then some st.found else none

/-- A state of the walking phase of the search machine. -/
def stw {n N D d : ℕ} (rot : Fin N → Fin D → Fin N) (s t : Fin n) (sp tp : Fin N)
    (j : Fin (D ^ d)) (i : ℕ) (F : Bool) : SearchState n N D d :=
  ⟨s, t, 2, sp, tp, walkFin rot sp (wordEquiv D d j) i, j, ⟨min i d, by omega⟩, F⟩

/-- Whether the target has been hit during the first `i` steps of the walk `w`. -/
noncomputable def hitB {N D d : ℕ} (rot : Fin N → Fin D → Fin N) (sp tp : Fin N)
    (w : Fin d → Fin D) (i : ℕ) : Bool :=
  decide (∃ m, 1 ≤ m ∧ m ≤ i ∧ walkFin rot sp w m = tp)

@[simp] theorem hitB_zero {N D d : ℕ} (rot : Fin N → Fin D → Fin N) (sp tp : Fin N)
    (w : Fin d → Fin D) : hitB rot sp tp w 0 = false := by
  simp only [hitB, decide_eq_false_iff_not]
  rintro ⟨m, h1, h2, -⟩
  omega

theorem hitB_succ {N D d : ℕ} (rot : Fin N → Fin D → Fin N) (sp tp : Fin N)
    (w : Fin d → Fin D) (i : ℕ) :
    hitB rot sp tp w (i + 1) =
      (hitB rot sp tp w i || decide (walkFin rot sp w (i + 1) = tp)) := by
  rw [Bool.eq_iff_iff]
  simp only [hitB, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨m, h1, h2, h3⟩
    rcases Nat.lt_or_ge m (i + 1) with h | h
    · exact Or.inl ⟨m, h1, by omega, h3⟩
    · exact Or.inr (by rw [show i + 1 = m by omega]; exact h3)
  · rintro (⟨m, h1, h2, h3⟩ | h)
    · exact ⟨m, h1, by omega, h3⟩
    · exact ⟨i + 1, by omega, le_rfl, h⟩

/-- Whether the target has been hit during the first `j` walks. -/
noncomputable def accB {N D : ℕ} (d : ℕ) (rot : Fin N → Fin D → Fin N) (sp tp : Fin N)
    (j : ℕ) : Bool :=
  decide (sp = tp ∨ ∃ j' : Fin (D ^ d), j'.1 < j ∧
    ∃ m, 1 ≤ m ∧ m ≤ d ∧ walkFin rot sp (wordEquiv D d j') m = tp)

theorem accB_zero {N D : ℕ} (d : ℕ) (rot : Fin N → Fin D → Fin N) (sp tp : Fin N) :
    accB d rot sp tp 0 = decide (sp = tp) := by
  refine decide_eq_decide.mpr ⟨?_, ?_⟩
  · rintro (h | ⟨j', hj', -⟩)
    · exact h
    · omega
  · exact Or.inl

theorem accB_succ {N D : ℕ} (d : ℕ) (rot : Fin N → Fin D → Fin N) (sp tp : Fin N) {j : ℕ}
    (hj : j < D ^ d) :
    accB d rot sp tp (j + 1) =
      (accB d rot sp tp j || hitB rot sp tp (wordEquiv D d ⟨j, hj⟩) d) := by
  rw [Bool.eq_iff_iff]
  simp only [accB, hitB, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨j', hj', m, h1, h2, h3⟩)
    · exact Or.inl (Or.inl h)
    · rcases Nat.lt_or_ge j'.1 j with h | h
      · exact Or.inl (Or.inr ⟨j', h, m, h1, h2, h3⟩)
      · have hjj : j'.1 = j := by omega
        have : j' = (⟨j, hj⟩ : Fin (D ^ d)) := Fin.ext (by simp [hjj])
        exact Or.inr ⟨m, h1, h2, by rw [← this]; exact h3⟩
  · rintro ((h | ⟨j', hj', m, h1, h2, h3⟩) | ⟨m, h1, h2, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j', by omega, m, h1, h2, h3⟩
    · exact Or.inr ⟨⟨j, hj⟩, by simp, m, h1, h2, h3⟩

theorem stepOnce_walk {n N D d : ℕ} (hD : 0 < D) (hNn : 0 < n → 0 < N)
    (rot : Fin N → Fin D → Fin N) (emb : Fin n → Fin N) (s t : Fin n) (sp tp : Fin N)
    (j : Fin (D ^ d)) {i : ℕ} (hi : i < d) (F : Bool) :
    (searchM n N D d hD hNn).stepOnce (Sum.elim (fun q => rot q.1 q.2) emb)
        (stw rot s t sp tp j i F) =
      stw rot s t sp tp j (i + 1)
        (F || decide (walkFin rot sp (wordEquiv D d j) (i + 1) = tp)) := by
  simp [SMachine.stepOnce, searchM, stw, Nat.min_eq_left hi.le,
    walkFin_succ rot sp (wordEquiv D d j) hi, hi]

theorem stepOnce_next {n N D d : ℕ} (hD : 0 < D) (hNn : 0 < n → 0 < N)
    (rot : Fin N → Fin D → Fin N) (emb : Fin n → Fin N) (s t : Fin n) (sp tp : Fin N)
    (j : Fin (D ^ d)) (hj : j.1 + 1 < D ^ d) (F : Bool) :
    (searchM n N D d hD hNn).stepOnce (Sum.elim (fun q => rot q.1 q.2) emb)
        (stw rot s t sp tp j d F) =
      stw rot s t sp tp ⟨j.1 + 1, hj⟩ 0 F := by
  simp [SMachine.stepOnce, searchM, stw, hj]

theorem out_stepOnce_last {n N D d : ℕ} (hD : 0 < D) (hNn : 0 < n → 0 < N)
    (rot : Fin N → Fin D → Fin N) (emb : Fin n → Fin N) (s t : Fin n) (sp tp : Fin N)
    (j : Fin (D ^ d)) (hj : ¬ j.1 + 1 < D ^ d) (F : Bool) :
    (searchM n N D d hD hNn).out ((searchM n N D d hD hNn).stepOnce
        (Sum.elim (fun q => rot q.1 q.2) emb) (stw rot s t sp tp j d F)) = some F := by
  simp [SMachine.stepOnce, searchM, stw, hj]

theorem run_word {n N D d : ℕ} (hD : 0 < D) (hNn : 0 < n → 0 < N)
    (rot : Fin N → Fin D → Fin N) (emb : Fin n → Fin N) (s t : Fin n) (sp tp : Fin N)
    (j : Fin (D ^ d)) (F : Bool) : ∀ i, i ≤ d →
    (searchM n N D d hD hNn).run (Sum.elim (fun q => rot q.1 q.2) emb)
        (stw rot s t sp tp j 0 F) i =
      stw rot s t sp tp j i (F || hitB rot sp tp (wordEquiv D d j) i) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    rw [SMachine.run_succ, ih (by omega), stepOnce_walk hD hNn rot emb s t sp tp j (by omega),
      hitB_succ, Bool.or_assoc]

theorem run_words {n N D d : ℕ} (hD : 0 < D) (hNn : 0 < n → 0 < N)
    (rot : Fin N → Fin D → Fin N) (emb : Fin n → Fin N) (s t : Fin n) (sp tp : Fin N) :
    ∀ j, (hj : j < D ^ d) →
    (searchM n N D d hD hNn).run (Sum.elim (fun q => rot q.1 q.2) emb)
        (stw rot s t sp tp ⟨0, Nat.pow_pos hD⟩ 0 (decide (sp = tp))) (j * (d + 1)) =
      stw rot s t sp tp ⟨j, hj⟩ 0 (accB d rot sp tp j) := by
  intro j
  induction j with
  | zero => intro _; simp [accB_zero]
  | succ j ih =>
    intro hj
    have hj' : j < D ^ d := by omega
    have harith : (j + 1) * (d + 1) = j * (d + 1) + (d + 1) := by ring
    rw [harith, SMachine.run_add _ _ _ (j * (d + 1)) (d + 1), ih hj',
      SMachine.run_add _ _ _ d 1, run_word hD hNn rot emb s t sp tp ⟨j, hj'⟩ _ d le_rfl,
      SMachine.run_one]
    rw [stepOnce_next hD hNn rot emb s t sp tp ⟨j, hj'⟩ (by simpa using hj),
      accB_succ d rot sp tp hj']

theorem searchM_computes (n N D d : ℕ) (hD : 0 < D) (hNn : 0 < n → 0 < N)
    (rot : Fin N → Fin D → Fin N) (emb : Fin n → Fin N) :
    (searchM n N D d hD hNn).Computes (Sum.elim (fun q => rot q.1 q.2) emb)
      (fun p => decide (ReachWithin rot d (emb p.1) (emb p.2))) := by
  rintro ⟨s, t⟩
  have hK : 0 < D ^ d := Nat.pow_pos hD
  -- the first two steps fetch the images of the two endpoints
  have hstart : (searchM n N D d hD hNn).run (Sum.elim (fun q => rot q.1 q.2) emb)
      ((searchM n N D d hD hNn).init (s, t)) 2 =
      stw rot s t (emb s) (emb t) ⟨0, hK⟩ 0 (decide (emb s = emb t)) := by
    rw [show (2 : ℕ) = 0 + 1 + 1 from rfl, SMachine.run_succ, SMachine.run_succ]
    simp [SMachine.run_zero, SMachine.stepOnce, searchM, stw]
  -- run through all the words
  have hlast : (searchM n N D d hD hNn).run (Sum.elim (fun q => rot q.1 q.2) emb)
      ((searchM n N D d hD hNn).init (s, t)) (2 + (D ^ d - 1) * (d + 1) + d) =
      stw rot s t (emb s) (emb t) ⟨D ^ d - 1, by omega⟩ d
        (accB d rot (emb s) (emb t) (D ^ d)) := by
    rw [SMachine.run_add _ _ _ (2 + (D ^ d - 1) * (d + 1)) d,
      SMachine.run_add _ _ _ 2 ((D ^ d - 1) * (d + 1)), hstart,
      run_words hD hNn rot emb s t (emb s) (emb t) (D ^ d - 1) (by omega),
      run_word hD hNn rot emb s t (emb s) (emb t) ⟨D ^ d - 1, by omega⟩ _ d le_rfl,
      ← accB_succ d rot (emb s) (emb t) (show D ^ d - 1 < D ^ d by omega)]
    congr 2
    omega
  refine ⟨2 + (D ^ d - 1) * (d + 1) + d + 1, ?_⟩
  rw [SMachine.eval, SMachine.run_succ, hlast,
    out_stepOnce_last hD hNn rot emb s t (emb s) (emb t) ⟨D ^ d - 1, by omega⟩
      (by simp; omega)]
  congr 1
  -- the accumulated answer is exactly reachability within `d` steps
  simp only [accB, reachWithin_iff hD rot (emb s) (emb t)]
  refine decide_eq_decide.mpr ⟨?_, ?_⟩
  · rintro (h | ⟨j', -, m, h1, h2, h3⟩)
    · exact ⟨fun _ => ⟨0, hD⟩, 0, Nat.zero_le _, h⟩
    · exact ⟨wordEquiv D d j', m, h2, h3⟩
  · rintro ⟨w, m, hm, hw⟩
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact Or.inl (by simpa using hw)
    · refine Or.inr ⟨(wordEquiv D d).symm w, ((wordEquiv D d).symm w).isLt, m, hpos, hm, ?_⟩
      rwa [Equiv.apply_symm_apply]

/-- **Unconditional**: in a `D`-regular graph on `N` vertices presented by a
rotation map, decide whether `t` is reachable from `s` by a walk of length at
most `d`, using a machine with `O(N⁵ · D^d · d)` states, i.e. space
`O(log N + d log D)`.  This is the last phase of Reingold's algorithm: applied
to a constant-degree graph of logarithmic diameter it runs in logarithmic
space. -/
theorem reachWithin_in_small_space (N D d : ℕ) (hD : 0 < D) :
    ∃ (S : Type) (inst : Fintype S)
      (M : SMachine ((Fin N × Fin D) ⊕ Fin N) (Fin N) (Fin N × Fin N) Bool S),
      @Fintype.card S inst = N * (N * (4 * (N * (N * (N * (D ^ d * ((d + 1) * 2))))))) ∧
      ∀ rot : Fin N → Fin D → Fin N,
        M.Computes (Sum.elim (fun q => rot q.1 q.2) id)
          (fun p => decide (ReachWithin rot d p.1 p.2)) :=
  ⟨SearchState N N D d, inferInstance, searchM N N D d hD (fun h => h),
    SearchState.card_eq N N D d, fun rot => searchM_computes N N D d hD (fun h => h) rot id⟩

/-!
## Reingold's theorem

The deep content of Reingold's theorem is the construction, using the zig-zag
product, of a logspace transformation taking an arbitrary undirected graph to a
constant-degree graph whose connected components have logarithmic diameter and
which preserves connectivity.  This is packaged in the structure
`ReingoldReduction` below; `reingold_sl_l` derives from it that undirected
`s`-`t` connectivity is decidable in logarithmic space, i.e. `SL = L`.
-/

/-- The data produced by Reingold's zig-zag transformation: a logspace machine
`redM n` which, given the adjacency matrix of an undirected graph on `n`
vertices as an oracle, computes the rotation map of a `D`-regular graph on
`N n` vertices together with an embedding of the original vertices, in such a
way that connectivity in the original graph corresponds to reachability within
`d n` steps in the new graph. -/
structure ReingoldReduction where
  /-- The (constant) degree of the transformed graph. -/
  D : ℕ
  /-- The degree is at least two. -/
  hD : 2 ≤ D
  /-- The number of vertices of the transformed graph. -/
  N : ℕ → ℕ
  /-- The diameter bound for the transformed graph. -/
  d : ℕ → ℕ
  /-- The polynomial bound exponent. -/
  c : ℕ
  /-- The state space of the transducer. -/
  S : ℕ → Type
  /-- The state space is finite. -/
  finS : ∀ n, Fintype (S n)
  /-- The transducer computing the transformed graph. -/
  redM : ∀ n, SMachine (Fin n × Fin n) Bool ((Fin (N n) × Fin D) ⊕ Fin n) (Fin (N n)) (S n)
  /-- The transducer uses logarithmic space. -/
  card_le : ∀ n, @Fintype.card (S n) (finS n) ≤ (n + 2) ^ c
  /-- The transformed graph has polynomially many vertices. -/
  N_le : ∀ n, N n ≤ (n + 2) ^ c
  /-- The diameter of the transformed graph is logarithmic. -/
  pow_le : ∀ n, D ^ d n ≤ (n + 2) ^ c
  /-- Correctness of the transformation. -/
  spec : ∀ (n : ℕ) (adj : Fin n → Fin n → Bool), (∀ u v, adj u v = adj v u) →
    ∃ (rot : Fin (N n) → Fin D → Fin (N n)) (emb : Fin n → Fin (N n)),
      (redM n).Computes (fun p => adj p.1 p.2) (Sum.elim (fun q => rot q.1 q.2) emb) ∧
      ∀ u v, AdjReach adj u v ↔ ReachWithin rot (d n) (emb u) (emb v)

/-- **Reingold's theorem** (`SL = L`): undirected `s`-`t` connectivity is
decidable in logarithmic space. -/
theorem reingold_sl_l (R : ReingoldReduction) : USTCON_in_L := by
  have hD0 : 0 < R.D := lt_of_lt_of_le (by norm_num) R.hD
  have hNpos : ∀ n : ℕ, 0 < n → 0 < R.N n := by
    intro n hn
    obtain ⟨_, emb, -, -⟩ := R.spec n (fun _ _ => false) (fun _ _ => rfl)
    exact lt_of_le_of_lt (Nat.zero_le _) (emb ⟨0, hn⟩).isLt
  refine ⟨6 * R.c + 5, fun n => SearchState n (R.N n) R.D (R.d n) × R.S n,
    fun n => letI := R.finS n; inferInstance,
    fun n => (searchM n (R.N n) R.D (R.d n) hD0 (hNpos n)).comp (R.redM n), ?_, ?_⟩
  · intro n
    letI := R.finS n
    have hcard : @Fintype.card (SearchState n (R.N n) R.D (R.d n) × R.S n) _ =
        Fintype.card (SearchState n (R.N n) R.D (R.d n)) * @Fintype.card (R.S n) (R.finS n) :=
      Fintype.card_prod _ _
    rw [hcard, SearchState.card_eq]
    have h2 : (2 : ℕ) ≤ n + 2 := by omega
    have hdd : R.d n + 1 ≤ R.D ^ R.d n :=
      le_trans (Nat.lt_two_pow_self) (Nat.pow_le_pow_left R.hD _)
    calc n * (n * (4 * (R.N n * (R.N n * (R.N n * (R.D ^ R.d n * ((R.d n + 1) * 2))))))) *
            @Fintype.card (R.S n) (R.finS n)
        ≤ (n + 2) ^ 1 * ((n + 2) ^ 1 * ((n + 2) ^ 2 * ((n + 2) ^ R.c * ((n + 2) ^ R.c *
            ((n + 2) ^ R.c * ((n + 2) ^ R.c * ((n + 2) ^ R.c * (n + 2) ^ 1))))))) *
            (n + 2) ^ R.c := by
          have e1 : n ≤ (n + 2) ^ 1 := by simp
          have e2 : (2 : ℕ) ≤ (n + 2) ^ 1 := by simp
          have e4 : (4 : ℕ) ≤ (n + 2) ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left h2 2)
          have eN : R.N n ≤ (n + 2) ^ R.c := R.N_le n
          have eP : R.D ^ R.d n ≤ (n + 2) ^ R.c := R.pow_le n
          have eI : R.d n + 1 ≤ (n + 2) ^ R.c := le_trans hdd (R.pow_le n)
          exact Nat.mul_le_mul (Nat.mul_le_mul e1 (Nat.mul_le_mul e1 (Nat.mul_le_mul e4
            (Nat.mul_le_mul eN (Nat.mul_le_mul eN (Nat.mul_le_mul eN
            (Nat.mul_le_mul eP (Nat.mul_le_mul eI e2)))))))) (R.card_le n)
      _ = (n + 2) ^ (6 * R.c + 5) := by
          rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
            ← pow_add, ← pow_add]
          ring_nf
  · intro n adj hsym
    obtain ⟨rot, emb, hred, hspec⟩ := R.spec n adj hsym
    have hsearch := searchM_computes n (R.N n) R.D (R.d n) hD0 (hNpos n) rot emb
    have hfun : (fun p : Fin n × Fin n => decide (ReachWithin rot (R.d n) (emb p.1) (emb p.2))) =
        fun p : Fin n × Fin n => decide (AdjReach adj p.1 p.2) := by
      funext p
      exact decide_eq_decide.mpr (hspec p.1 p.2).symm
    rw [hfun] at hsearch
    exact SMachine.comp_computes hred hsearch

/-- The `SL ⊆ L` direction in reduction form: if the adjacency matrix of an
undirected graph on `m` vertices is itself computed from some more primitive
oracle `f` by a space-bounded transducer `T`, then connectivity in that graph
is decidable from `f` by a machine whose state space is only
`(m + 2) ^ c` times larger than that of `T`.  Thus any problem that reduces to
undirected connectivity by a logarithmic-space reduction is itself decidable in
logarithmic space. -/
theorem ustcon_reduction_in_L (R : ReingoldReduction) :
    ∃ c : ℕ, ∀ (Q A S₂ : Type) (inst₂ : Fintype S₂) (m : ℕ) (f : Q → A)
      (adj : Fin m → Fin m → Bool) (_ : ∀ u v, adj u v = adj v u)
      (T : SMachine Q A (Fin m × Fin m) Bool S₂)
      (_ : T.Computes f (fun p => adj p.1 p.2)),
      ∃ (S : Type) (inst : Fintype S) (M : SMachine Q A (Fin m × Fin m) Bool S),
        @Fintype.card S inst ≤ (m + 2) ^ c * @Fintype.card S₂ inst₂ ∧
        M.Computes f (fun p => decide (AdjReach adj p.1 p.2)) := by
  obtain ⟨c, S, inst, M, hcard, hM⟩ := reingold_sl_l R
  refine ⟨c, fun Q A S₂ inst₂ m f adj hsym T hT => ?_⟩
  letI := inst m
  letI := inst₂
  exact ⟨S m × S₂, inferInstance, (M m).comp T,
    le_of_eq_of_le (Fintype.card_prod _ _) (Nat.mul_le_mul_right _ (hcard m)),
    SMachine.comp_computes hT (hM m adj hsym)⟩

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

