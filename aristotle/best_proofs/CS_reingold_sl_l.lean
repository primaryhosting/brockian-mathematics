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

We model space bounded computation by machines whose *memory* is a finite type `M`; the space
used is `log₂ (card M)`, so that "logarithmic space" means "polynomially many memory states".
A machine inspects, in each memory state, at most one position of its input, and updates its
memory state according to the bit read.

* `CS.DetMachine` is a deterministic such machine; it accepts an input when its (unique)
  computation reaches an accepting memory state.
* `CS.SymMachine` is a *symmetric* nondeterministic machine in the sense of Lewis and
  Papadimitriou: its transition relation is symmetric, so its configuration graph is an
  undirected graph, and it accepts an input when an accepting memory state is connected to
  the initial one in that graph.
* `CS.Lclass` and `CS.SLclass` are the corresponding classes of languages, a language being
  decided by a family of machines with polynomially many memory states, one for each input
  length.  (The families are not required to be uniformly generated.)
* `CS.UstconLogspace` is Reingold's theorem: undirected `s`-`t` connectivity, on graphs given
  by their adjacency matrix, is decided by deterministic machines with polynomially many
  memory states.  Its proof — the zig-zag construction of expanders — is *not* formalised
  here; it is taken as an explicit hypothesis of the main theorem.

The main theorem `CS.reingold_sl_l` derives `SL = L` from it.  Both inclusions are proved:

* `CS.inSL_of_inL` (`L ⊆ SL`, unconditional) simulates a deterministic machine by a symmetric
  one after adding a step counter, so that the configuration graph becomes a forest whose
  components are trees rooted at the final configurations;
* `CS.inL_of_inSL` (`SL ⊆ L`) runs the connectivity algorithm on the configuration graph of a
  symmetric machine, each adjacency query being answered by reading two bits of the input.

Finally `CS.ustconLogspace_iff_symSimDet` shows that the hypothesis is not stronger than what
is being proved: it is *equivalent* to the machine-level form of `SL = L`, because undirected
connectivity is itself decided by a symmetric machine with quadratically many memory states.
-/

namespace CS

/-- Reading the bit of the input `x` at an optional position: a machine state that queries no
position reads the default value `false`. -/
def readBit {I : Type} (x : I → Bool) : Option I → Bool
  | none => false
  | some i => x i

/-- A deterministic space bounded machine working on an input `x : I → Bool`.

The memory of the machine is the finite type `M`; the *space* used by the machine is
`log₂ (card M)`, so that "logarithmic space" means "polynomially many memory states".
At each step the machine reads (at most) one bit of the input, the position being determined
by the current memory state, and updates its memory state accordingly. It accepts if it ever
enters a memory state marked as accepting. -/
structure DetMachine (I : Type) where
  /-- The finite memory of the machine. -/
  M : Type
  [fintypeM : Fintype M]
  /-- The initial memory state. -/
  start : M
  /-- The input position inspected in a given memory state (`none` = no position). -/
  query : M → Option I
  /-- The memory update, as a function of the current state and of the bit just read. -/
  next : M → Bool → M
  /-- The accepting memory states. -/
  acc : M → Bool

attribute [instance] DetMachine.fintypeM

namespace DetMachine

variable {I : Type}

/-- One computation step of a deterministic machine on input `x`. -/
def stepFun (D : DetMachine I) (x : I → Bool) (p : D.M) : D.M :=
  D.next p (readBit x (D.query p))

/-- The memory state of `D` after `k` steps on input `x`. -/
def run (D : DetMachine I) (x : I → Bool) (k : ℕ) : D.M := (D.stepFun x)^[k] D.start

lemma run_succ (D : DetMachine I) (x : I → Bool) (k : ℕ) :
    D.run x (k + 1) = D.stepFun x (D.run x k) := Function.iterate_succ_apply' _ _ _

/-- `D` accepts `x` if it eventually enters an accepting memory state. -/
def Accepts (D : DetMachine I) (x : I → Bool) : Prop := ∃ k, D.acc (D.run x k) = true

end DetMachine

/-- A *symmetric* nondeterministic space bounded machine working on an input `x : I → Bool`.

As above the memory is the finite type `M` and each memory state inspects at most one input
position.  The transition relation `adj p a q b` (where `a`, `b` are the bits read in the
memory states `p`, `q`) is required to be symmetric: this is the defining feature of the
symmetric machines of Lewis and Papadimitriou, whose configuration graph is an *undirected*
graph.  The machine accepts if some accepting memory state is connected to the initial state
in the configuration graph. -/
structure SymMachine (I : Type) where
  /-- The finite memory of the machine. -/
  M : Type
  [fintypeM : Fintype M]
  /-- The initial memory state. -/
  start : M
  /-- The input position inspected in a given memory state (`none` = no position). -/
  query : M → Option I
  /-- The transition relation; `a` and `b` are the bits read at `p` and at `q`. -/
  adj : M → Bool → M → Bool → Prop
  /-- The accepting memory states. -/
  acc : M → Bool
  /-- Symmetry of the transition relation. -/
  adj_symm : ∀ p a q b, adj p a q b → adj q b p a

attribute [instance] SymMachine.fintypeM

namespace SymMachine

variable {I : Type}

/-- The configuration graph of a symmetric machine on the input `x`. -/
def rel (S : SymMachine I) (x : I → Bool) (p q : S.M) : Prop :=
  S.adj p (readBit x (S.query p)) q (readBit x (S.query q))

lemma rel_symm (S : SymMachine I) (x : I → Bool) {p q : S.M} (h : S.rel x p q) : S.rel x q p :=
  S.adj_symm _ _ _ _ h

/-- `S` accepts `x` if some accepting state is reachable from the initial state in the
(undirected) configuration graph. -/
def Accepts (S : SymMachine I) (x : I → Bool) : Prop :=
  ∃ q, Relation.ReflTransGen (S.rel x) S.start q ∧ S.acc q = true

end SymMachine

/-- A language: a family of predicates on bit strings, indexed by the length. -/
abbrev Lang : Type := (n : ℕ) → (Fin n → Bool) → Prop

/-- `P` is in `L`: it is decided by deterministic machines with polynomially many memory
states, i.e. with logarithmic space. -/
def inL (P : Lang) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, ∃ D : DetMachine (Fin n),
    Fintype.card D.M ≤ (n + 2) ^ c ∧ ∀ x, (D.Accepts x ↔ P n x)

/-- `P` is in `SL`: it is decided by symmetric machines with polynomially many memory
states, i.e. with logarithmic space. -/
def inSL (P : Lang) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, ∃ S : SymMachine (Fin n),
    Fintype.card S.M ≤ (n + 2) ^ c ∧ ∀ x, (S.Accepts x ↔ P n x)

/-- The class `L` of languages decidable in logarithmic space. -/
def Lclass : Set Lang := {P | inL P}

/-- The class `SL` of languages decidable by symmetric machines in logarithmic space. -/
def SLclass : Set Lang := {P | inSL P}

/-- **Reingold's theorem**, as an input to the present development: undirected `s`-`t`
connectivity on graphs with `N` vertices, presented by their adjacency matrix, is decided
by deterministic machines with polynomially many memory states in `N`, i.e. in logarithmic
space. -/
def UstconLogspace : Prop :=
  ∃ c : ℕ, ∀ (N : ℕ) (s t : Fin N), ∃ D : DetMachine (Fin N × Fin N),
    Fintype.card D.M ≤ (N + 2) ^ c ∧
      ∀ adj : Fin N → Fin N → Bool, (∀ i j, adj i j = adj j i) →
        (D.Accepts (fun p => adj p.1 p.2) ↔
          Relation.ReflTransGen (fun i j => adj i j = true) s t)

/-- Transport of reflexive transitive closures along an equivalence. -/
lemma reflTransGen_congr {V W : Type} (e : V ≃ W) (r : V → V → Prop) (u v : V) :
    Relation.ReflTransGen (fun i j => r (e.symm i) (e.symm j)) (e u) (e v) ↔
      Relation.ReflTransGen r u v := by
  constructor
  · intro h
    have := Relation.ReflTransGen.lift (r := fun i j => r (e.symm i) (e.symm j)) (p := r)
      e.symm (fun _ _ hab => hab) h
    simpa using this
  · intro h
    exact Relation.ReflTransGen.lift (r := r) (p := fun i j => r (e.symm i) (e.symm j))
      e (fun _ _ hab => by simpa using hab) h

/-- Pigeonhole: any value taken by the orbit of a point under iteration of `g` is already
taken at a time at most `card M`. -/
lemma exists_iterate_le_card {M : Type} [Fintype M] (g : M → M) (a : M) (k : ℕ) :
    ∃ k' ≤ Fintype.card M, g^[k'] a = g^[k] a := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k ≤ Fintype.card M
    · exact ⟨k, hk, rfl⟩
    push_neg at hk
    have hni : ¬ Function.Injective (fun i : Fin (Fintype.card M + 1) => g^[(i : ℕ)] a) := by
      intro hinj
      have := Fintype.card_le_of_injective _ hinj
      simp at this
    rw [Function.not_injective_iff] at hni
    obtain ⟨i, j, hij, hne⟩ := hni
    set p := min (i : ℕ) (j : ℕ) with hp
    set q := max (i : ℕ) (j : ℕ) with hq
    have hpq : p < q := by
      have : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
      omega
    have hqle : q ≤ Fintype.card M := by
      have hi := i.isLt
      have hj := j.isLt
      omega
    have hpqeq : g^[p] a = g^[q] a := by
      rcases le_total (i : ℕ) (j : ℕ) with h | h
      · simp only [hp, hq, min_eq_left h, max_eq_right h]
        exact hij
      · simp only [hp, hq, min_eq_right h, max_eq_left h]
        exact hij.symm
    have hkq : q ≤ k := le_of_lt (lt_of_le_of_lt hqle hk)
    have key : g^[k - (q - p)] a = g^[k] a := by
      have h1 : g^[k] a = g^[(k - q) + q] a := by
        congr 1
        omega
      have h2 : g^[(k - q) + q] a = g^[k - q] (g^[q] a) := by
        rw [Function.iterate_add_apply]
      have h3 : g^[k - q] (g^[p] a) = g^[(k - q) + p] a := by
        rw [Function.iterate_add_apply]
      have h4 : (k - q) + p = k - (q - p) := by omega
      rw [h1, h2, ← hpqeq, h3, h4]
    obtain ⟨k', hk', hk'eq⟩ := ih (k - (q - p)) (by omega)
    exact ⟨k', hk', by rw [hk'eq, key]⟩

/-!
## Pulling a machine back along a 2-local reduction

If the bits of the input of a machine `D` are each computable from at most two bits of another
input `x` (a "2-local reduction"), then `D` can be simulated on `x` at the cost of a constant
factor in the number of memory states: the simulating machine reads the two relevant bits of
`x` in two consecutive steps.
-/

section Pullback

variable {I J : Type} (D : DetMachine J) (f : J → Option I × Option I)
  (g : J → Bool → Bool → Bool) (x : I → Bool)

/-- The input of `D` obtained from `x` through a 2-local reduction. -/
def pullbackInput : J → Bool := fun j => g j (readBit x (f j).1) (readBit x (f j).2)

/-- The machine simulating `D` through a 2-local reduction of its input. -/
def pullbackMachine : DetMachine I where
  M := D.M × Option Bool
  start := (D.start, none)
  query := fun st => match st.2 with
    | none => (D.query st.1).elim none (fun j => (f j).1)
    | some _ => (D.query st.1).elim none (fun j => (f j).2)
  next := fun st b => match st.2, D.query st.1 with
    | _, none => (D.next st.1 false, none)
    | none, some _ => (st.1, some b)
    | some a, some j => (D.next st.1 (g j a b), none)
  acc := fun st => D.acc st.1

lemma pb_step_none (u : D.M) (hq : D.query u = none) :
    (pullbackMachine D f g).stepFun x ((u, none) : D.M × Option Bool)
      = ((D.stepFun (pullbackInput f g x) u, none) : D.M × Option Bool) := by
  simp [DetMachine.stepFun, pullbackMachine, hq, readBit]

lemma pb_step_phase1 (u : D.M) (j : J) (hq : D.query u = some j) :
    (pullbackMachine D f g).stepFun x ((u, none) : D.M × Option Bool)
      = ((u, some (readBit x (f j).1)) : D.M × Option Bool) := by
  simp [DetMachine.stepFun, pullbackMachine, hq, readBit]

lemma pb_step_phase2 (u : D.M) (j : J) (hq : D.query u = some j) :
    (pullbackMachine D f g).stepFun x ((u, some (readBit x (f j).1)) : D.M × Option Bool)
      = ((D.stepFun (pullbackInput f g x) u, none) : D.M × Option Bool) := by
  simp [DetMachine.stepFun, pullbackMachine, hq, readBit, pullbackInput]

lemma pullback_stepA (u : D.M) : ∃ i : ℕ,
    ((pullbackMachine D f g).stepFun x)^[i] ((u, none) : D.M × Option Bool)
      = ((D.stepFun (pullbackInput f g x) u, none) : D.M × Option Bool) := by
  cases hq : D.query u with
  | none => exact ⟨1, by simpa using pb_step_none D f g x u hq⟩
  | some j =>
    refine ⟨2, ?_⟩
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      pb_step_phase1 D f g x u j hq, pb_step_phase2 D f g x u j hq]
    simp

lemma pullback_reach (k : ℕ) : ∃ K : ℕ,
    ((pullbackMachine D f g).stepFun x)^[K] ((D.start, none) : D.M × Option Bool)
      = ((D.run (pullbackInput f g x) k, none) : D.M × Option Bool) := by
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨K, hK⟩ := ih
    obtain ⟨i, hi⟩ := pullback_stepA D f g x (D.run (pullbackInput f g x) k)
    refine ⟨i + K, ?_⟩
    rw [Function.iterate_add_apply, hK, hi, DetMachine.run_succ]

/-- The invariant satisfied by the memory states of the simulating machine. -/
def PBInv : (D.M × Option Bool) → Prop := fun st =>
  ∃ k : ℕ, st = (D.run (pullbackInput f g x) k, none) ∨
    (∃ j, D.query (D.run (pullbackInput f g x) k) = some j ∧
      st = (D.run (pullbackInput f g x) k, some (readBit x (f j).1)))

lemma pullback_inv_step {st : D.M × Option Bool} (h : PBInv D f g x st) :
    PBInv D f g x ((pullbackMachine D f g).stepFun x st) := by
  obtain ⟨k, h | ⟨j, hj, h⟩⟩ := h
  · subst h
    cases hq : D.query (D.run (pullbackInput f g x) k) with
    | none =>
      exact ⟨k + 1, Or.inl (by rw [pb_step_none D f g x _ hq, DetMachine.run_succ])⟩
    | some j =>
      exact ⟨k, Or.inr ⟨j, hq, by rw [pb_step_phase1 D f g x _ j hq]⟩⟩
  · subst h
    exact ⟨k + 1, Or.inl (by rw [pb_step_phase2 D f g x _ j hj, DetMachine.run_succ])⟩

lemma pullback_inv (K : ℕ) :
    PBInv D f g x (((pullbackMachine D f g).stepFun x)^[K]
      ((D.start, none) : D.M × Option Bool)) := by
  induction K with
  | zero => exact ⟨0, Or.inl rfl⟩
  | succ K ih =>
    rw [Function.iterate_succ_apply']
    exact pullback_inv_step D f g x ih

/-- Pulling a deterministic machine back along a "2-local" reduction of its input. -/
lemma DetMachine.pullback :
    ∃ D' : DetMachine I, Fintype.card D'.M ≤ 4 * Fintype.card D.M ∧
      ∀ x : I → Bool, (D'.Accepts x ↔ D.Accepts (pullbackInput f g x)) := by
  refine ⟨pullbackMachine D f g, ?_, ?_⟩
  · show Fintype.card (D.M × Option Bool) ≤ _
    simp [Fintype.card_prod]
    omega
  · intro x
    constructor
    · rintro ⟨K, hK⟩
      obtain ⟨k, h | ⟨j, hj, h⟩⟩ := pullback_inv D f g x K
      · exact ⟨k, by rw [show D.run (pullbackInput f g x) k
          = (((pullbackMachine D f g).stepFun x)^[K] ((D.start, none) : D.M × Option Bool)).1 from
          by rw [h]]; exact hK⟩
      · exact ⟨k, by rw [show D.run (pullbackInput f g x) k
          = (((pullbackMachine D f g).stepFun x)^[K] ((D.start, none) : D.M × Option Bool)).1 from
          by rw [h]]; exact hK⟩
    · rintro ⟨k, hk⟩
      obtain ⟨K, hK⟩ := pullback_reach D f g x k
      exact ⟨K, by
        show (pullbackMachine D f g).acc _ = true
        rw [show ((pullbackMachine D f g).run x K) = (((pullbackMachine D f g).stepFun x)^[K]
          ((D.start, none) : D.M × Option Bool)) from rfl, hK]
        exact hk⟩

end Pullback

/-!
## The configuration graph of a symmetric machine

The configuration graph of a symmetric machine `S` on an input `x` is an undirected graph on
the memory states of `S`; we add one extra vertex `none`, joined to all accepting states, so
that `S` accepts `x` exactly when the two distinguished vertices `some S.start` and `none`
are connected.
-/

section ConfGraph

variable {I : Type} (S : SymMachine I)

open scoped Classical in
/-- The adjacency of the configuration graph, as a function of the two bits read at its two
endpoints. -/
noncomputable def confAdj : Option S.M → Bool → Option S.M → Bool → Bool
  | some p, a, some q, b => decide (S.adj p a q b)
  | some p, _, none, _ => S.acc p
  | none, _, some q, _ => S.acc q
  | none, _, none, _ => false

lemma confAdj_symm (v : Option S.M) (a : Bool) (w : Option S.M) (b : Bool) :
    confAdj S v a w b = confAdj S w b v a := by
  cases v with
  | none => cases w <;> simp [confAdj]
  | some p =>
    cases w with
    | none => simp [confAdj]
    | some q =>
      simp only [confAdj]
      exact decide_eq_decide.mpr ⟨fun h => S.adj_symm _ _ _ _ h, fun h => S.adj_symm _ _ _ _ h⟩

/-- The input position inspected at a vertex of the configuration graph. -/
def confQuery : Option S.M → Option I
  | some p => S.query p
  | none => none

/-- The edge relation of the configuration graph on the input `x`. -/
noncomputable def confRel (x : I → Bool) (v w : Option S.M) : Prop :=
  confAdj S v (readBit x (confQuery S v)) w (readBit x (confQuery S w)) = true

variable (x : I → Bool)

lemma confRel_some_some (p q : S.M) : confRel S x (some p) (some q) ↔ S.rel x p q := by
  simp [confRel, confAdj, confQuery, SymMachine.rel]

lemma confRel_some_none (p : S.M) : confRel S x (some p) none ↔ S.acc p = true := by
  simp [confRel, confAdj]

lemma confRel_none_none : ¬ confRel S x none none := by
  simp [confRel, confAdj]

lemma confRel_some_cases (r : S.M) (c : Option S.M) (h : confRel S x (some r) c) :
    (c = none ∧ S.acc r = true) ∨ (∃ t, c = some t ∧ S.rel x r t) := by
  revert h
  cases c with
  | none => exact fun h => Or.inl ⟨rfl, (confRel_some_none S x r).1 h⟩
  | some t => exact fun h => Or.inr ⟨t, rfl, (confRel_some_some S x r t).1 h⟩

/-- `S` accepts `x` if and only if the two distinguished vertices of its configuration graph
are connected. -/
theorem confRel_reach_iff :
    Relation.ReflTransGen (confRel S x) (some S.start) none ↔ S.Accepts x := by
  constructor
  · intro h
    have key : ∀ v, Relation.ReflTransGen (confRel S x) (some S.start) v →
        (S.Accepts x ∨ ∃ r, v = some r ∧ Relation.ReflTransGen (S.rel x) S.start r) := by
      intro v hv
      induction hv with
      | refl => exact Or.inr ⟨S.start, rfl, Relation.ReflTransGen.refl⟩
      | @tail b c _ hbc ih =>
        rcases ih with hacc | ⟨r, hr, hrun⟩
        · exact Or.inl hacc
        · subst hr
          rcases confRel_some_cases S x r c hbc with ⟨hc, hacc⟩ | ⟨t, hc, hrt⟩
          · exact Or.inl ⟨r, hrun, hacc⟩
          · exact Or.inr ⟨t, hc, hrun.tail hrt⟩
    rcases key none h with h1 | ⟨r, hr, _⟩
    · exact h1
    · exact absurd hr (by simp)
  · rintro ⟨q, hq, hacc⟩
    have : Relation.ReflTransGen (confRel S x) (some S.start) (some q) :=
      Relation.ReflTransGen.lift (r := S.rel x) some
        (fun a b hab => (confRel_some_some S x a b).2 hab) hq
    exact this.tail ((confRel_some_none S x q).2 hacc)

end ConfGraph

/-!
## `L ⊆ SL`

A deterministic machine is simulated by a symmetric one by adding a step counter: the
configuration graph of the layered machine is a functional graph all of whose orbits reach a
fixed point (a configuration of the last layer), hence each of its connected components is a
tree rooted at such a fixed point.  Consequently, undirected reachability in the layered
graph coincides with the deterministic computation.
-/

section LtoSL

variable {I : Type} (D : DetMachine I) (x : I → Bool)

/-- The successor on layers, stationary on the last layer. -/
def layerSucc (T : ℕ) (t : Fin (T + 1)) : Fin (T + 1) :=
  if h : (t : ℕ) < T then ⟨t + 1, by omega⟩ else t

/-- One step of the layered version of a deterministic machine. -/
def layStep (P : (D.M × Bool) × Fin (Fintype.card D.M + 2)) (b : Bool) :
    (D.M × Bool) × Fin (Fintype.card D.M + 2) :=
  if (P.2 : ℕ) < Fintype.card D.M + 1 then
    ((D.next P.1.1 b, P.1.2 || D.acc P.1.1), layerSucc (Fintype.card D.M + 1) P.2)
  else P

/-- The symmetric machine simulating a deterministic machine. -/
def symOfDet : SymMachine I where
  M := (D.M × Bool) × Fin (Fintype.card D.M + 2)
  start := ((D.start, false), ⟨0, by omega⟩)
  query := fun P => D.query P.1.1
  adj := fun P a Q b => Q = layStep D P a ∨ P = layStep D Q b
  acc := fun P => decide ((P.2 : ℕ) = Fintype.card D.M + 1 ∧ P.1.2 = true)
  adj_symm := by
    intro p a q b h
    tauto

/-- One step of the layered machine on the input `x`. -/
def layRun (P : (D.M × Bool) × Fin (Fintype.card D.M + 2)) :
    (D.M × Bool) × Fin (Fintype.card D.M + 2) :=
  layStep D P (readBit x (D.query P.1.1))

lemma symOfDet_rel (P Q : (D.M × Bool) × Fin (Fintype.card D.M + 2)) :
    (symOfDet D).rel x P Q ↔ (Q = layRun D x P ∨ P = layRun D x Q) := Iff.rfl

lemma layRun_layer (P : (D.M × Bool) × Fin (Fintype.card D.M + 2)) :
    ((layRun D x P).2 : ℕ) = min ((P.2 : ℕ) + 1) (Fintype.card D.M + 1) := by
  have hP : (P.2 : ℕ) ≤ Fintype.card D.M + 1 := by
    have := P.2.isLt
    omega
  unfold layRun layStep
  split_ifs with h
  · simp only [layerSucc]
    rw [dif_pos h]
    simp
    omega
  · simp
    omega

lemma layRun_fixed (P : (D.M × Bool) × Fin (Fintype.card D.M + 2))
    (h : (P.2 : ℕ) = Fintype.card D.M + 1) : layRun D x P = P := by
  unfold layRun layStep
  rw [if_neg (by omega)]

lemma layerSucc_val (T : ℕ) (t : Fin (T + 1)) (h : (t : ℕ) < T) :
    ((layerSucc T t : Fin (T + 1)) : ℕ) = (t : ℕ) + 1 := by
  simp [layerSucc, dif_pos h]

lemma layRun_step_lt (P : (D.M × Bool) × Fin (Fintype.card D.M + 2))
    (h : (P.2 : ℕ) < Fintype.card D.M + 1) :
    layRun D x P
      = ((D.stepFun x P.1.1, P.1.2 || D.acc P.1.1), layerSucc (Fintype.card D.M + 1) P.2) := by
  unfold layRun layStep
  rw [if_pos h]
  rfl

lemma layRun_iterate_layer (k : ℕ) (P : (D.M × Bool) × Fin (Fintype.card D.M + 2)) :
    (((layRun D x)^[k] P).2 : ℕ) = min ((P.2 : ℕ) + k) (Fintype.card D.M + 1) := by
  induction k with
  | zero =>
    have := P.2.isLt
    simp only [Function.iterate_zero_apply]
    omega
  | succ k ih =>
    rw [Function.iterate_succ_apply', layRun_layer, ih]
    omega

/-- The root of a configuration: the fixed point its orbit reaches. -/
def layRoot (P : (D.M × Bool) × Fin (Fintype.card D.M + 2)) :
    (D.M × Bool) × Fin (Fintype.card D.M + 2) :=
  (layRun D x)^[Fintype.card D.M + 1] P

lemma layRoot_layer (P : (D.M × Bool) × Fin (Fintype.card D.M + 2)) :
    ((layRoot D x P).2 : ℕ) = Fintype.card D.M + 1 := by
  rw [layRoot, layRun_iterate_layer]
  omega

lemma layRoot_fixed (P : (D.M × Bool) × Fin (Fintype.card D.M + 2)) :
    layRun D x (layRoot D x P) = layRoot D x P :=
  layRun_fixed D x _ (layRoot_layer D x P)

lemma layRoot_step (P : (D.M × Bool) × Fin (Fintype.card D.M + 2)) :
    layRoot D x (layRun D x P) = layRoot D x P := by
  have h1 : (layRun D x)^[Fintype.card D.M + 1] (layRun D x P)
      = (layRun D x)^[Fintype.card D.M + 1 + 1] P := (Function.iterate_succ_apply _ _ _).symm
  have h2 : (layRun D x)^[Fintype.card D.M + 1 + 1] P
      = layRun D x ((layRun D x)^[Fintype.card D.M + 1] P) := Function.iterate_succ_apply' _ _ _
  rw [layRoot, h1, h2]
  exact layRoot_fixed D x P

lemma layRoot_of_rel {P Q : (D.M × Bool) × Fin (Fintype.card D.M + 2)}
    (h : (symOfDet D).rel x P Q) : layRoot D x P = layRoot D x Q := by
  rcases (symOfDet_rel D x P Q).1 h with h | h
  · rw [h, layRoot_step]
  · rw [h, layRoot_step]

lemma layRoot_of_reach {P Q : (D.M × Bool) × Fin (Fintype.card D.M + 2)}
    (h : Relation.ReflTransGen ((symOfDet D).rel x) P Q) : layRoot D x P = layRoot D x Q := by
  induction h with
  | refl => rfl
  | @tail b c _ hbc ih => rw [ih, layRoot_of_rel D x hbc]

lemma reach_layRun_iterate (k : ℕ) (P : (D.M × Bool) × Fin (Fintype.card D.M + 2)) :
    Relation.ReflTransGen ((symOfDet D).rel x) P ((layRun D x)^[k] P) := by
  induction k with
  | zero => exact Relation.ReflTransGen.refl
  | succ k ih =>
    refine ih.tail ?_
    rw [symOfDet_rel, Function.iterate_succ_apply']
    exact Or.inl rfl

lemma exists_lt_succ_iff (p : ℕ → Prop) (k : ℕ) :
    (∃ i, i < k + 1 ∧ p i) ↔ ((∃ i, i < k ∧ p i) ∨ p k) := by
  constructor
  · rintro ⟨i, hi, hp⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · exact Or.inl ⟨i, h, hp⟩
    · exact Or.inr (h ▸ hp)
  · rintro (⟨i, hi, hp⟩ | hp)
    · exact ⟨i, by omega, hp⟩
    · exact ⟨k, by omega, hp⟩

/-- The state of the layered machine after `k` steps, for `k` at most the number of layers. -/
lemma layRun_iterate_start (k : ℕ) (hk : k ≤ Fintype.card D.M + 1) :
    (((layRun D x)^[k] (symOfDet D).start).1.1 = D.run x k) ∧
      ((((layRun D x)^[k] (symOfDet D).start).2 : ℕ) = k) ∧
      ((((layRun D x)^[k] (symOfDet D).start).1.2 = true) ↔
        ∃ i, i < k ∧ D.acc (D.run x i) = true) := by
  induction k with
  | zero => exact ⟨rfl, rfl, by simp [symOfDet]⟩
  | succ k ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih (by omega)
    have hlt : (((layRun D x)^[k] (symOfDet D).start).2 : ℕ) < Fintype.card D.M + 1 := by
      omega
    rw [Function.iterate_succ_apply', layRun_step_lt D x _ hlt]
    refine ⟨?_, ?_, ?_⟩
    · simp only
      rw [ih1, ← DetMachine.run_succ]
    · simp only
      rw [layerSucc_val _ _ hlt, ih2]
    · simp only [Bool.or_eq_true, ih3, ih1]
      exact (exists_lt_succ_iff (fun i => D.acc (D.run x i) = true) k).symm

/-- The symmetric machine `symOfDet D` accepts exactly the inputs accepted by `D`. -/
theorem symOfDet_accepts_iff : (symOfDet D).Accepts x ↔ D.Accepts x := by
  classical
  obtain ⟨hr1, hr2, hr3⟩ := layRun_iterate_start D x (Fintype.card D.M + 1) le_rfl
  constructor
  · rintro ⟨Q, hQ, hacc⟩
    have haccQ : ((Q.2 : ℕ) = Fintype.card D.M + 1 ∧ Q.1.2 = true) := by
      simpa [symOfDet] using hacc
    have hfix : layRoot D x Q = Q := by
      have : layRun D x Q = Q := layRun_fixed D x Q haccQ.1
      simpa [layRoot] using Function.iterate_fixed this (Fintype.card D.M + 1)
    have hroot : layRoot D x (symOfDet D).start = Q := by
      rw [layRoot_of_reach D x hQ, hfix]
    have : ((layRun D x)^[Fintype.card D.M + 1] (symOfDet D).start).1.2 = true := by
      rw [show ((layRun D x)^[Fintype.card D.M + 1] (symOfDet D).start) = Q from hroot]
      exact haccQ.2
    obtain ⟨i, _, hi⟩ := hr3.1 this
    exact ⟨i, hi⟩
  · rintro ⟨k, hk⟩
    obtain ⟨k', hk', hk'eq⟩ :=
      exists_iterate_le_card (D.stepFun x) D.start k
    have hacc' : D.acc (D.run x k') = true := by
      rw [show D.run x k' = D.run x k from hk'eq]
      exact hk
    refine ⟨layRoot D x (symOfDet D).start, reach_layRun_iterate D x _ _, ?_⟩
    have hflag : ((layRun D x)^[Fintype.card D.M + 1] (symOfDet D).start).1.2 = true :=
      hr3.2 ⟨k', by omega, hacc'⟩
    have hlayer := layRoot_layer D x (symOfDet D).start
    simp only [symOfDet, decide_eq_true_eq]
    exact ⟨hlayer, hflag⟩

lemma symOfDet_card :
    Fintype.card (symOfDet D).M = Fintype.card D.M * 2 * (Fintype.card D.M + 2) := by
  show Fintype.card ((D.M × Bool) × Fin (Fintype.card D.M + 2)) = _
  simp [Fintype.card_prod]

end LtoSL

/-- `L ⊆ SL`. -/
theorem inSL_of_inL {P : Lang} (h : inL P) : inSL P := by
  obtain ⟨c, hc⟩ := h
  refine ⟨2 * c + 3, fun n => ?_⟩
  obtain ⟨D, hcard, hdec⟩ := hc n
  refine ⟨symOfDet D, ?_, fun x => (symOfDet_accepts_iff D x).trans (hdec x)⟩
  have hone : 1 ≤ (n + 2) ^ c := Nat.one_le_pow _ _ (by omega)
  have h8 : 8 ≤ (n + 2) ^ 3 := by
    have := Nat.pow_le_pow_left (show 2 ≤ n + 2 by omega) 3
    simpa using this
  calc Fintype.card (symOfDet D).M
      = Fintype.card D.M * 2 * (Fintype.card D.M + 2) := symOfDet_card D
    _ ≤ (n + 2) ^ c * 2 * ((n + 2) ^ c + 2) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul_right _ hcard) (by omega)
    _ ≤ 8 * ((n + 2) ^ c * (n + 2) ^ c) := by nlinarith
    _ ≤ (n + 2) ^ 3 * ((n + 2) ^ c * (n + 2) ^ c) := Nat.mul_le_mul_right _ h8
    _ = (n + 2) ^ (2 * c + 3) := by ring


/-- The machine-level form of `SL = L`: every symmetric machine can be simulated by a
deterministic machine with polynomially many memory states, i.e. with the same space up to a
constant factor. -/
def SymSimDet : Prop :=
  ∃ c : ℕ, ∀ (I : Type) (S : SymMachine I), ∃ D : DetMachine I,
    Fintype.card D.M ≤ (Fintype.card S.M + 2) ^ c ∧ ∀ x, (D.Accepts x ↔ S.Accepts x)

/-- Given Reingold's theorem, a deterministic machine simulates a symmetric machine: it
decides connectivity in the configuration graph, each adjacency query being answered by
reading two bits of the input. -/
theorem symSimDet_of_ustcon (hR : UstconLogspace) : SymSimDet := by
  classical
  obtain ⟨c, hc⟩ := hR
  refine ⟨2 * c + 2, fun I S => ?_⟩
  obtain ⟨DU, hDUcard, hDU⟩ :=
    hc (Fintype.card (Option S.M)) ((Fintype.equivFin (Option S.M)) (some S.start))
      ((Fintype.equivFin (Option S.M)) none)
  obtain ⟨D', hD'card, hD'⟩ := DetMachine.pullback DU
    (fun ij => (confQuery S ((Fintype.equivFin (Option S.M)).symm ij.1),
      confQuery S ((Fintype.equivFin (Option S.M)).symm ij.2)))
    (fun ij a b => confAdj S ((Fintype.equivFin (Option S.M)).symm ij.1) a
      ((Fintype.equivFin (Option S.M)).symm ij.2) b)
  refine ⟨D', ?_, ?_⟩
  · -- the size bound
    have hcardO : Fintype.card (Option S.M) = Fintype.card S.M + 1 := by
      simp [Fintype.card_option]
    have hsq : Fintype.card S.M + 3 ≤ (Fintype.card S.M + 2) ^ 2 := by nlinarith
    have hfour : 4 ≤ (Fintype.card S.M + 2) ^ 2 := by nlinarith
    calc Fintype.card D'.M ≤ 4 * Fintype.card DU.M := hD'card
      _ ≤ 4 * (Fintype.card (Option S.M) + 2) ^ c := Nat.mul_le_mul_left _ hDUcard
      _ = 4 * (Fintype.card S.M + 3) ^ c := by rw [hcardO]
      _ ≤ 4 * ((Fintype.card S.M + 2) ^ 2) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsq c)
      _ = 4 * (Fintype.card S.M + 2) ^ (2 * c) := by rw [← pow_mul]
      _ ≤ (Fintype.card S.M + 2) ^ 2 * (Fintype.card S.M + 2) ^ (2 * c) :=
          Nat.mul_le_mul_right _ hfour
      _ = (Fintype.card S.M + 2) ^ (2 * c + 2) := by ring
  · intro x
    rw [hD' x]
    have hsymm : ∀ i j : Fin (Fintype.card (Option S.M)),
        pullbackInput
          (fun ij => (confQuery S ((Fintype.equivFin (Option S.M)).symm ij.1),
            confQuery S ((Fintype.equivFin (Option S.M)).symm ij.2)))
          (fun ij a b => confAdj S ((Fintype.equivFin (Option S.M)).symm ij.1) a
            ((Fintype.equivFin (Option S.M)).symm ij.2) b) x (i, j)
        = pullbackInput
          (fun ij => (confQuery S ((Fintype.equivFin (Option S.M)).symm ij.1),
            confQuery S ((Fintype.equivFin (Option S.M)).symm ij.2)))
          (fun ij a b => confAdj S ((Fintype.equivFin (Option S.M)).symm ij.1) a
            ((Fintype.equivFin (Option S.M)).symm ij.2) b) x (j, i) := by
      intro i j
      exact confAdj_symm S _ _ _ _
    rw [hDU _ hsymm]
    exact (reflTransGen_congr (Fintype.equivFin (Option S.M)) (confRel S x) (some S.start)
      none).trans (confRel_reach_iff S x)

/-- `SL ⊆ L`, given Reingold's theorem. -/
theorem inL_of_inSL (hR : UstconLogspace) {P : Lang} (h : inSL P) : inL P := by
  obtain ⟨c, hc⟩ := symSimDet_of_ustcon hR
  obtain ⟨cS, hS⟩ := h
  refine ⟨(cS + 2) * c, fun n => ?_⟩
  obtain ⟨S, hcard, hdec⟩ := hS n
  obtain ⟨D, hDcard, hD⟩ := hc (Fin n) S
  refine ⟨D, ?_, fun x => (hD x).trans (hdec x)⟩
  have hone : 1 ≤ (n + 2) ^ cS := Nat.one_le_pow _ _ (by omega)
  have hfour : 4 ≤ (n + 2) ^ 2 := by
    have := Nat.pow_le_pow_left (show 2 ≤ n + 2 by omega) 2
    simpa using this
  have h1 : Fintype.card S.M + 2 ≤ (n + 2) ^ (cS + 2) := by
    calc Fintype.card S.M + 2 ≤ (n + 2) ^ cS + 2 := by omega
      _ ≤ 4 * (n + 2) ^ cS := by omega
      _ ≤ (n + 2) ^ 2 * (n + 2) ^ cS := Nat.mul_le_mul_right _ hfour
      _ = (n + 2) ^ (cS + 2) := by ring
  calc Fintype.card D.M ≤ (Fintype.card S.M + 2) ^ c := hDcard
    _ ≤ ((n + 2) ^ (cS + 2)) ^ c := Nat.pow_le_pow_left h1 c
    _ = (n + 2) ^ ((cS + 2) * c) := by rw [← pow_mul]

/-!
## Undirected connectivity is a symmetric-logspace problem

Conversely, undirected `s`-`t` connectivity is decided by a symmetric machine whose memory
stores a current vertex together with a candidate neighbour, hence with quadratically many
memory states.  Consequently Reingold's theorem is not merely sufficient but also necessary
for the simulation of symmetric machines by deterministic ones.
-/

section UstconSym

/-- A symmetric machine deciding undirected `s`-`t` connectivity: its memory stores the
current vertex and a candidate neighbour, it may change the candidate freely, and it may
move to the candidate along an edge. -/
def ustconSym (N : ℕ) (t s : Fin N) : SymMachine (Fin N × Fin N) where
  M := Fin N × Fin N
  start := (s, s)
  query := fun P => some P
  adj := fun P a Q b => P.1 = Q.1 ∨ (Q.1 = P.2 ∧ Q.2 = P.1 ∧ a = true ∧ b = true)
  acc := fun P => decide (P.1 = t)
  adj_symm := by
    rintro p a q b (h | ⟨h1, h2, h3, h4⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨h2.symm, h1.symm, h4, h3⟩

variable (N : ℕ) (s t : Fin N) (adjB : Fin N → Fin N → Bool)

lemma ustconSym_rel (P Q : Fin N × Fin N) :
    (ustconSym N t s).rel (fun p => adjB p.1 p.2) P Q ↔
      (P.1 = Q.1 ∨ (Q.1 = P.2 ∧ Q.2 = P.1 ∧ adjB P.1 P.2 = true ∧ adjB Q.1 Q.2 = true)) :=
  Iff.rfl

lemma ustconSym_reach_of_graph (hsym : ∀ i j, adjB i j = adjB j i) (u : Fin N)
    (h : Relation.ReflTransGen (fun i j => adjB i j = true) s u) :
    Relation.ReflTransGen ((ustconSym N t s).rel (fun p => adjB p.1 p.2))
      ((s, s) : Fin N × Fin N) ((u, u) : Fin N × Fin N) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail v w _ hvw ih =>
    have e1 : (ustconSym N t s).rel (fun p => adjB p.1 p.2) ((v, v) : Fin N × Fin N)
        ((v, w) : Fin N × Fin N) := (ustconSym_rel N s t adjB _ _).2 (Or.inl rfl)
    have e2 : (ustconSym N t s).rel (fun p => adjB p.1 p.2) ((v, w) : Fin N × Fin N)
        ((w, v) : Fin N × Fin N) :=
      (ustconSym_rel N s t adjB _ _).2 (Or.inr ⟨rfl, rfl, hvw, by rw [hsym]; exact hvw⟩)
    have e3 : (ustconSym N t s).rel (fun p => adjB p.1 p.2) ((w, v) : Fin N × Fin N)
        ((w, w) : Fin N × Fin N) := (ustconSym_rel N s t adjB _ _).2 (Or.inl rfl)
    exact ((ih.tail e1).tail e2).tail e3

lemma ustconSym_graph_of_reach (Q : Fin N × Fin N)
    (h : Relation.ReflTransGen ((ustconSym N t s).rel (fun p => adjB p.1 p.2))
      ((s, s) : Fin N × Fin N) Q) :
    Relation.ReflTransGen (fun i j => adjB i j = true) s Q.1 := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    rcases (ustconSym_rel N s t adjB b c).1 hbc with h1 | ⟨h1, _, h3, _⟩
    · rw [← h1]
      exact ih
    · exact ih.tail (by rw [h1]; exact h3)

/-- The symmetric machine `ustconSym` decides undirected `s`-`t` connectivity. -/
theorem ustconSym_accepts_iff (hsym : ∀ i j, adjB i j = adjB j i) :
    (ustconSym N t s).Accepts (fun p => adjB p.1 p.2) ↔
      Relation.ReflTransGen (fun i j => adjB i j = true) s t := by
  constructor
  · rintro ⟨Q, hQ, hacc⟩
    have h1 : Q.1 = t := by simpa [ustconSym] using hacc
    have := ustconSym_graph_of_reach N s t adjB Q hQ
    rwa [h1] at this
  · intro h
    refine ⟨(t, t), ustconSym_reach_of_graph N s t adjB hsym t h, ?_⟩
    simp [ustconSym]

end UstconSym

/-- Reingold's theorem is *equivalent* to the machine-level statement `SL = L`: undirected
connectivity is itself decided by symmetric machines in logarithmic space. -/
theorem ustcon_of_symSimDet (h : SymSimDet) : UstconLogspace := by
  obtain ⟨c, hc⟩ := h
  refine ⟨2 * c, fun N s t => ?_⟩
  obtain ⟨D, hcard, hD⟩ := hc (Fin N × Fin N) (ustconSym N t s)
  refine ⟨D, ?_, fun adjB hsym => (hD _).trans (ustconSym_accepts_iff N s t adjB hsym)⟩
  have hM : Fintype.card (ustconSym N t s).M = N * N := by
    show Fintype.card (Fin N × Fin N) = N * N
    simp
  have h1 : Fintype.card (ustconSym N t s).M + 2 ≤ (N + 2) ^ 2 := by
    rw [hM]
    nlinarith
  calc Fintype.card D.M ≤ (Fintype.card (ustconSym N t s).M + 2) ^ c := hcard
    _ ≤ ((N + 2) ^ 2) ^ c := Nat.pow_le_pow_left h1 c
    _ = (N + 2) ^ (2 * c) := by rw [← pow_mul]

/-- Reingold's theorem, in the form used here, is equivalent to the machine-level form of
`SL = L`. -/
theorem ustconLogspace_iff_symSimDet : UstconLogspace ↔ SymSimDet :=
  ⟨symSimDet_of_ustcon, ustcon_of_symSimDet⟩

/-- **`SL = L` (Reingold)**: given that undirected `s`-`t` connectivity is decidable in
logarithmic space (`UstconLogspace`, Reingold's theorem, which is equivalent to the
machine-level form of the conclusion by `ustconLogspace_iff_symSimDet`), the class of
languages decided by symmetric machines in logarithmic space coincides with the class of
languages decided deterministically in logarithmic space. -/
theorem reingold_sl_l (hR : UstconLogspace) : SLclass = Lclass := by
  ext P
  exact ⟨fun h => inL_of_inSL hR h, fun h => inSL_of_inL h⟩

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

