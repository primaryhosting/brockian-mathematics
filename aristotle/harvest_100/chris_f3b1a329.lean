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

import Mathlib
import RequestProject.Savitch.Enc

/-!
# The Savitch simulator and its correctness

We build, from a nondeterministic machine `M` and a recursion depth `K`, a
deterministic machine `savitchDM M K` which decides, by Savitch's recursive midpoint
search, whether the sink vertex `none` of the configuration graph of `M` is reachable
from the start vertex within `2 ^ K` steps.  If `cV M ≤ 2 ^ K` this is exactly
acceptance by `M`.
-/

namespace CS
namespace Savitch

variable {Sigma : Type}

theorem toBool_congr {p q : Prop} (h : p ↔ q) : toBool p = toBool q := by rw [propext h]

/-- The input position inspected by a raw state. -/
def rawAddr (M : NMachine Sigma) : Raw M → ℕ
  | (Mode.call u _ _, _) => addrV M u
  | (Mode.ret _, _) => 0
  | (Mode.done _, _) => 0

/-- One step of the simulator on the input `x`. -/
noncomputable def rawNext (M : NMachine Sigma) (x : List Sigma) (s : Raw M) : Raw M :=
  rawStep M x[rawAddr M s]? s

variable (M : NMachine Sigma) (x : List Sigma)

theorem rawNext_call_zero (u v : Vert M) (st : List (Frame M)) :
    rawNext M x (Mode.call u v 0, st)
      = (Mode.ret (toBool (reachIn (edgeX M x) 0 u v)), st) := rfl

theorem rawNext_call_succ (u v : Vert M) (i : ℕ) (st : List (Frame M)) :
    rawNext M x (Mode.call u v (i + 1), st)
      = (Mode.call u (mid M 0) i, (u, v, i, 0, false) :: st) := rfl

theorem rawNext_ret_nil (b : Bool) :
    rawNext M x (Mode.ret b, ([] : List (Frame M))) = (Mode.done b, []) := rfl

theorem rawNext_ret_cons (b : Bool) (u v : Vert M) (i j : ℕ) (ph : Bool)
    (st : List (Frame M)) :
    rawNext M x (Mode.ret b, (u, v, i, j, ph) :: st) =
      (if ph then (if b then (Mode.ret true, st) else advance M u v i j st)
        else (if b then (Mode.call (mid M j) v i, (u, v, i, j, true) :: st)
          else advance M u v i j st)) := rfl

theorem rawNext_done (b : Bool) (st : List (Frame M)) :
    rawNext M x (Mode.done b, st) = (Mode.done b, st) := rfl

theorem iterate_done (t : ℕ) (b : Bool) (st : List (Frame M)) :
    (rawNext M x)^[t] (Mode.done b, st) = (Mode.done b, st) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply, rawNext_done, ih]

theorem iterate_trans {k1 k2 : ℕ} {a b c : Raw M} (h1 : (rawNext M x)^[k1] a = b)
    (h2 : (rawNext M x)^[k2] b = c) : (rawNext M x)^[k1 + k2] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, h1, h2]

/-- The inner loop of Savitch's algorithm: starting from the state that is about to
compute `reach i u (mid j)` with the frame `(u, v, i, j, false)` on the stack, the
simulator eventually returns whether some midpoint of index `≥ j` works. -/
theorem trace_loop (i : ℕ)
    (hA : ∀ (u v : Vert M) (st : List (Frame M)), ∃ k, (rawNext M x)^[k] (Mode.call u v i, st)
      = (Mode.ret (toBool (reachIn (edgeX M x) i u v)), st)) :
    ∀ (d j : ℕ), cV M - j ≤ d → j < cV M → ∀ (u v : Vert M) (st : List (Frame M)),
      ∃ k, (rawNext M x)^[k] (Mode.call u (mid M j) i, (u, v, i, j, false) :: st)
        = (Mode.ret (toBool (∃ j', j ≤ j' ∧ j' < cV M ∧
            reachIn (edgeX M x) i u (mid M j') ∧ reachIn (edgeX M x) i (mid M j') v)), st) := by
  intro d
  induction d with
  | zero => intro j hd hj; omega
  | succ d ih =>
    intro j hd hj u v st
    -- the continuation which tries the next midpoint
    have hadv : ¬ (reachIn (edgeX M x) i u (mid M j) ∧ reachIn (edgeX M x) i (mid M j) v) →
        ∃ k, (rawNext M x)^[k] (advance M u v i j st)
          = (Mode.ret (toBool (∃ j', j ≤ j' ∧ j' < cV M ∧
              reachIn (edgeX M x) i u (mid M j') ∧ reachIn (edgeX M x) i (mid M j') v)), st) := by
      intro hfail
      unfold advance
      by_cases hnext : j + 1 < cV M
      · rw [if_pos hnext]
        obtain ⟨k, hk⟩ := ih (j + 1) (by omega) hnext u v st
        refine ⟨k, ?_⟩
        rw [hk]
        congr 1
        refine congrArg Mode.ret (toBool_congr ⟨?_, ?_⟩)
        · rintro ⟨j', hj1, hj2, hj3, hj4⟩
          exact ⟨j', by omega, hj2, hj3, hj4⟩
        · rintro ⟨j', hj1, hj2, hj3, hj4⟩
          rcases Nat.eq_or_lt_of_le hj1 with heq | hlt
          · subst heq
            exact absurd ⟨hj3, hj4⟩ hfail
          · exact ⟨j', by omega, hj2, hj3, hj4⟩
      · rw [if_neg hnext]
        refine ⟨0, ?_⟩
        simp only [Function.iterate_zero, id_eq]
        congr 1
        refine congrArg Mode.ret ?_
        symm
        rw [toBool_eq_false]
        rintro ⟨j', hj1, hj2, hj3, hj4⟩
        have : j' = j := by omega
        exact hfail (this ▸ ⟨hj3, hj4⟩)
    -- first recursive call: is `mid j` reachable from `u`?
    obtain ⟨k1, hk1⟩ := hA u (mid M j) ((u, v, i, j, false) :: st)
    by_cases h1 : reachIn (edgeX M x) i u (mid M j)
    · -- yes; now check the second half
      obtain ⟨k2, hk2⟩ := hA (mid M j) v ((u, v, i, j, true) :: st)
      by_cases h2 : reachIn (edgeX M x) i (mid M j) v
      · refine ⟨k1 + 1 + k2 + 1, ?_⟩
        refine iterate_trans M x (iterate_trans M x (iterate_trans M x hk1 ?_) hk2) ?_
        · rw [Function.iterate_one, rawNext_ret_cons]
          rw [if_neg (by simp), if_pos (by simp [h1])]
        · rw [Function.iterate_one, rawNext_ret_cons]
          rw [if_pos (by simp), if_pos (by simp [h2])]
          congr 1
          exact congrArg Mode.ret (by
            symm
            rw [toBool_eq_true]
            exact ⟨j, le_rfl, hj, h1, h2⟩)
      · obtain ⟨k3, hk3⟩ := hadv (by tauto)
        refine ⟨k1 + 1 + k2 + 1 + k3, ?_⟩
        refine iterate_trans M x (iterate_trans M x (iterate_trans M x
          (iterate_trans M x hk1 ?_) hk2) ?_) hk3
        · rw [Function.iterate_one, rawNext_ret_cons]
          rw [if_neg (by simp), if_pos (by simp [h1])]
        · rw [Function.iterate_one, rawNext_ret_cons]
          rw [if_pos (by simp), if_neg (by simp [h2])]
    · obtain ⟨k3, hk3⟩ := hadv (by tauto)
      refine ⟨k1 + 1 + k3, ?_⟩
      refine iterate_trans M x (iterate_trans M x hk1 ?_) hk3
      rw [Function.iterate_one, rawNext_ret_cons]
      rw [if_neg (by simp), if_neg (by simp [h1])]

/-- Correctness of the recursive procedure: a `call u v i` returns exactly whether `v`
is reachable from `u` within `2 ^ i` steps, leaving the stack unchanged. -/
theorem trace_call : ∀ (i : ℕ) (u v : Vert M) (st : List (Frame M)),
    ∃ k, (rawNext M x)^[k] (Mode.call u v i, st)
      = (Mode.ret (toBool (reachIn (edgeX M x) i u v)), st) := by
  intro i
  induction i with
  | zero => intro u v st; exact ⟨1, by rw [Function.iterate_one, rawNext_call_zero]⟩
  | succ i ih =>
    intro u v st
    obtain ⟨k, hk⟩ := trace_loop M x i ih (cV M) 0 (by omega) (cV_pos M) u v st
    have heq : (∃ j', 0 ≤ j' ∧ j' < cV M ∧ reachIn (edgeX M x) i u (mid M j') ∧
        reachIn (edgeX M x) i (mid M j') v) ↔ reachIn (edgeX M x) (i + 1) u v := by
      constructor
      · rintro ⟨j', -, -, h1, h2⟩
        exact ⟨mid M j', h1, h2⟩
      · rintro ⟨w, h1, h2⟩
        obtain ⟨j', hj', hmid⟩ := mid_surj M w
        refine ⟨j', Nat.zero_le _, hj', ?_, ?_⟩
        · rw [hmid]; exact h1
        · rw [hmid]; exact h2
    rw [toBool_congr heq] at hk
    exact ⟨1 + k, iterate_trans M x (by rw [Function.iterate_one, rawNext_call_succ]) hk⟩

/-! ### The deterministic machine -/

/-- The Savitch simulator of `M` with recursion depth `K`. -/
noncomputable def savitchDM (M : NMachine Sigma) (K : ℕ) : DMachine Sigma where
  S := {s : Raw M // WFraw M K s}
  fintypeS := instFintypeWF M K
  start := ⟨(Mode.call (some M.start) none K, []), ⟨by simp, trivial⟩⟩
  addr := fun s => rawAddr M s.1
  acc := fun s => s.1.1 = Mode.done true
  step := fun s o => ⟨rawStep M o s.1, wf_rawStep o s.2⟩

theorem savitchDM_move (K : ℕ) (s : (savitchDM M K).S) :
    (((savitchDM M K).move x s) : (savitchDM M K).S).1 = rawNext M x s.1 := rfl

theorem savitchDM_iterate (K : ℕ) (k : ℕ) (s : (savitchDM M K).S) :
    ((((savitchDM M K).move x)^[k] s) : (savitchDM M K).S).1 = (rawNext M x)^[k] s.1 := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, savitchDM_move]

/-- The simulator accepts exactly when the sink is reachable within `2 ^ K` steps. -/
theorem savitchDM_accepts_iff (K : ℕ) :
    (savitchDM M K).Accepts x ↔ reachIn (edgeX M x) K (some M.start) none := by
  obtain ⟨k, hk⟩ := trace_call M x K (some M.start) none []
  have hfin : (rawNext M x)^[k + 1] (Mode.call (some M.start) none K, [])
      = (Mode.done (toBool (reachIn (edgeX M x) K (some M.start) none)), []) := by
    refine iterate_trans M x hk ?_
    rw [Function.iterate_one, rawNext_ret_nil]
  constructor
  · rintro ⟨m, hm⟩
    -- compare the states at time `max m (k+1)`
    have h1 : ((((savitchDM M K).move x)^[m] (savitchDM M K).start)).1.1 = Mode.done true := hm
    have hstart : ((savitchDM M K).start).1 = (Mode.call (some M.start) none K, []) := rfl
    set T := max m (k + 1) with hT
    have hA : (rawNext M x)^[T] (Mode.call (some M.start) none K, [])
        = (Mode.done (toBool (reachIn (edgeX M x) K (some M.start) none)), []) := by
      have : T = (k + 1) + (T - (k + 1)) := by omega
      rw [this, Function.iterate_add_apply, ← show (T - (k+1)) + (k+1) = (k+1) + (T - (k+1)) by
        omega]
      rw [show (rawNext M x)^[k+1] (Mode.call (some M.start) none K, []) = _ from hfin]
      exact iterate_done M x _ _ _
    have hB : ((rawNext M x)^[T] (Mode.call (some M.start) none K, [])).1 = Mode.done true := by
      have : T = m + (T - m) := by omega
      rw [this, Function.iterate_add_apply]
      have hm' : (rawNext M x)^[m] (Mode.call (some M.start) none K, []) =
          (((savitchDM M K).move x)^[m] (savitchDM M K).start).1 := by
        rw [savitchDM_iterate, hstart]
      rw [show (T - m) + m = m + (T - m) by omega] at *
      rw [hm']
      rcases hs : (((savitchDM M K).move x)^[m] (savitchDM M K).start).1 with ⟨md, sst⟩
      have : md = Mode.done true := by rw [← h1, hs]
      subst this
      rw [iterate_done]
    rw [hA] at hB
    simpa using hB
  · intro hreach
    refine ⟨k + 1, ?_⟩
    show ((((savitchDM M K).move x)^[k + 1] (savitchDM M K).start)).1.1 = Mode.done true
    rw [savitchDM_iterate]
    have hstart : ((savitchDM M K).start).1 = (Mode.call (some M.start) none K, []) := rfl
    rw [hstart, hfin]
    simp [hreach]

/-! ### Acceptance of `M` in terms of the configuration graph -/

theorem reflTransGen_some_of {a b : Vert M} (h : Relation.ReflTransGen (edgeX M x) a b) :
    ∀ s, a = some s → (b = none ∨ ∃ t, b = some t ∧ Relation.ReflTransGen (M.edge x) s t) := by
  induction h with
  | refl => intro s hs; exact Or.inr ⟨s, hs, Relation.ReflTransGen.refl⟩
  | @tail c b _ hcb ih =>
    intro s hs
    rcases ih s hs with hc | ⟨t, ht, hst⟩
    · subst hc
      exact absurd hcb (by cases b <;> exact id)
    · subst ht
      cases b with
      | none => exact Or.inl rfl
      | some w => exact Or.inr ⟨w, rfl, hst.tail hcb⟩

theorem accepts_iff_reachable :
    M.Accepts x ↔ Relation.ReflTransGen (edgeX M x) (some M.start) none := by
  constructor
  · rintro ⟨s, hs, hacc⟩
    have hlift : ∀ a b : M.S, Relation.ReflTransGen (M.edge x) a b →
        Relation.ReflTransGen (edgeX M x) (some a) (some b) := by
      intro a b h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih => exact ih.tail hstep
    exact (hlift _ _ hs).tail hacc
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with hnone | ⟨c, hc, hcn⟩
    · exact absurd hnone.symm (by simp)
    · cases c with
      | none => exact absurd hcn id
      | some t =>
        rcases reflTransGen_some_of M x hc M.start rfl with h' | ⟨t', ht', hst'⟩
        · exact absurd h' (by simp)
        · refine ⟨t, ?_, hcn⟩
          rw [Option.some_inj.mp ht'] at hst'
          exact hst'

/-- Savitch's simulation, for a single machine: if the recursion depth `K` is large
enough, the simulator accepts exactly the same inputs as `M`. -/
theorem savitchDM_accepts_iff_accepts (K : ℕ) (hK : cV M ≤ 2 ^ K) :
    (savitchDM M K).Accepts x ↔ M.Accepts x := by
  rw [savitchDM_accepts_iff, accepts_iff_reachable]
  exact reachIn_iff_reflTransGen hK _ _

end Savitch
end CS

import Mathlib

/-!
# A space-bounded machine model

We use the standard "read-only random access input + bounded work memory" model of
space-bounded computation.

A machine has a finite set of internal states `S` (the *work memory*: a machine with
`|S| ≤ 2^s` states is a machine using `s` bits of work space).  The input `x` is
read-only and does *not* count towards the space; the machine can inspect it only one
symbol at a time: the current state `s` determines an address `addr s`, and the
transition may depend on the symbol of the input found at that address (or `none`, if
the address is out of range).

Deterministic machines have a transition *function*, nondeterministic ones a transition
*relation*, and a nondeterministic machine accepts iff some accepting state is
reachable from the start state.

`DSPACE f` / `NSPACE f` are then the classes of languages decided by (families of)
such machines with `2^(c * f n + c)` states on inputs of length `n`.
-/

namespace CS

/-- A nondeterministic space-bounded machine over the input alphabet `Sigma`. -/
structure NMachine (Sigma : Type) where
  /-- The finite set of internal (work-memory) states. -/
  S : Type
  /-- Finiteness of the state set: `Fintype.card S` measures the space used. -/
  fintypeS : Fintype S
  /-- The initial state. -/
  start : S
  /-- The position of the read-only input head, determined by the current state. -/
  addr : S → ℕ
  /-- The accepting states. -/
  acc : S → Prop
  /-- The transition relation: it may depend on the symbol currently scanned. -/
  next : S → Option Sigma → S → Prop

attribute [instance] NMachine.fintypeS

/-- A deterministic space-bounded machine over the input alphabet `Sigma`. -/
structure DMachine (Sigma : Type) where
  /-- The finite set of internal (work-memory) states. -/
  S : Type
  /-- Finiteness of the state set: `Fintype.card S` measures the space used. -/
  fintypeS : Fintype S
  /-- The initial state. -/
  start : S
  /-- The position of the read-only input head, determined by the current state. -/
  addr : S → ℕ
  /-- The accepting states. -/
  acc : S → Prop
  /-- The transition function: it may depend on the symbol currently scanned. -/
  step : S → Option Sigma → S

attribute [instance] DMachine.fintypeS

variable {Sigma : Type}

/-- One nondeterministic step on the input `x`. -/
def NMachine.edge (M : NMachine Sigma) (x : List Sigma) (a b : M.S) : Prop :=
  M.next a x[M.addr a]? b

/-- A nondeterministic machine accepts `x` iff some accepting state is reachable. -/
def NMachine.Accepts (M : NMachine Sigma) (x : List Sigma) : Prop :=
  ∃ s, Relation.ReflTransGen (M.edge x) M.start s ∧ M.acc s

/-- One deterministic step on the input `x`. -/
def DMachine.move (D : DMachine Sigma) (x : List Sigma) (s : D.S) : D.S :=
  D.step s x[D.addr s]?

/-- A deterministic machine accepts `x` iff it eventually enters an accepting state. -/
def DMachine.Accepts (D : DMachine Sigma) (x : List Sigma) : Prop :=
  ∃ k, D.acc ((D.move x)^[k] D.start)

/-- The deterministic space class `DSPACE f`: languages decided, on inputs of length
`n`, by a deterministic machine with at most `2 ^ (c * f n + c)` states, i.e. using
`O(f n)` bits of work space. -/
def DSPACE (Sigma : Type) (f : ℕ → ℕ) : Set (List Sigma → Prop) :=
  {L | ∃ c : ℕ, ∀ n : ℕ, ∃ D : DMachine Sigma, Fintype.card D.S ≤ 2 ^ (c * f n + c) ∧
        ∀ x : List Sigma, x.length = n → (D.Accepts x ↔ L x)}

/-- The nondeterministic space class `NSPACE f`. -/
def NSPACE (Sigma : Type) (f : ℕ → ℕ) : Set (List Sigma → Prop) :=
  {L | ∃ c : ℕ, ∀ n : ℕ, ∃ M : NMachine Sigma, Fintype.card M.S ≤ 2 ^ (c * f n + c) ∧
        ∀ x : List Sigma, x.length = n → (M.Accepts x ↔ L x)}

/-- Every deterministic machine is a nondeterministic machine. -/
def DMachine.toNMachine (D : DMachine Sigma) : NMachine Sigma where
  S := D.S
  fintypeS := D.fintypeS
  start := D.start
  addr := D.addr
  acc := D.acc
  next := fun a o b => b = D.step a o

theorem DMachine.toNMachine_accepts (D : DMachine Sigma) (x : List Sigma) :
    D.toNMachine.Accepts x ↔ D.Accepts x := by
  constructor
  · rintro ⟨s, hs, hacc⟩
    have key : ∀ a b : D.S, Relation.ReflTransGen (D.toNMachine.edge x) a b →
        ∃ k, (D.move x)^[k] a = b := by
      intro a b h
      induction h with
      | refl => exact ⟨0, rfl⟩
      | tail _ hstep ih =>
        obtain ⟨k, hk⟩ := ih
        refine ⟨k + 1, ?_⟩
        rw [Function.iterate_succ_apply', hk]
        exact hstep.symm
    obtain ⟨k, hk⟩ := key _ _ hs
    refine ⟨k, ?_⟩
    have hk' : (D.move x)^[k] D.start = s := hk
    rw [hk']
    exact hacc
  · rintro ⟨k, hk⟩
    refine ⟨(D.move x)^[k] D.start, ?_, hk⟩
    clear hk
    induction k with
    | zero => exact Relation.ReflTransGen.refl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.tail rfl

theorem DSPACE_subset_NSPACE (f : ℕ → ℕ) : DSPACE Sigma f ⊆ NSPACE Sigma f := by
  rintro L ⟨c, hc⟩
  refine ⟨c, fun n => ?_⟩
  obtain ⟨D, hcard, hD⟩ := hc n
  exact ⟨D.toNMachine, hcard, fun x hx => (D.toNMachine_accepts x).trans (hD x hx)⟩

end CS

import Mathlib

/-!
# Bounded reachability and the Savitch doubling relation

`CS.reachIn E i u v` says that `v` can be reached from `u` by a path of length at most
`2 ^ i`.  It satisfies the Savitch recursion `reachIn E (i+1) u v ↔ ∃ w, reachIn E i u w
∧ reachIn E i w v` *by definition*, and on a finite vertex set `V` it coincides with
reachability as soon as `card V ≤ 2 ^ i`.
-/

namespace CS

variable {V : Type} {E : V → V → Prop}

/-- `PathOf E l u v`: there is a walk of length exactly `l` from `u` to `v`. -/
def PathOf (E : V → V → Prop) (l : ℕ) (u v : V) : Prop :=
  ∃ p : ℕ → V, p 0 = u ∧ p l = v ∧ ∀ j < l, E (p j) (p (j + 1))

/-- `reachIn E i u v`: `v` is reachable from `u` by a walk of length at most `2 ^ i`. -/
def reachIn (E : V → V → Prop) : ℕ → V → V → Prop
  | 0 => fun u v => u = v ∨ E u v
  | i + 1 => fun u v => ∃ w, reachIn E i u w ∧ reachIn E i w v

@[simp] theorem reachIn_zero (u v : V) : reachIn E 0 u v ↔ (u = v ∨ E u v) := Iff.rfl

@[simp] theorem reachIn_succ (i : ℕ) (u v : V) :
    reachIn E (i + 1) u v ↔ ∃ w, reachIn E i u w ∧ reachIn E i w v := Iff.rfl

theorem reachIn_refl (i : ℕ) (u : V) : reachIn E i u u := by
  induction i with
  | zero => exact Or.inl rfl
  | succ i ih => exact ⟨u, ih, ih⟩

theorem reachIn_succ_of (i : ℕ) {u v : V} (h : reachIn E i u v) : reachIn E (i + 1) u v :=
  ⟨v, h, reachIn_refl i v⟩

theorem reachIn_mono {i j : ℕ} (hij : i ≤ j) {u v : V} (h : reachIn E i u v) :
    reachIn E j u v := by
  induction j with
  | zero =>
    have : i = 0 := Nat.le_zero.mp hij
    exact this ▸ h
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · exact reachIn_succ_of j (ih (by omega))
    · have : i = j + 1 := le_antisymm hij h'
      exact this ▸ h

theorem reachIn_imp_reflTransGen {i : ℕ} {u v : V} (h : reachIn E i u v) :
    Relation.ReflTransGen E u v := by
  induction i generalizing u v with
  | zero =>
    rcases h with rfl | h
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single h
  | succ i ih =>
    obtain ⟨w, h1, h2⟩ := h
    exact (ih h1).trans (ih h2)

/-- A walk of length at most `2 ^ i` witnesses `reachIn E i`. -/
theorem reachIn_of_pathOf : ∀ (i l : ℕ) (u v : V), PathOf E l u v → l ≤ 2 ^ i →
    reachIn E i u v := by
  intro i
  induction i with
  | zero =>
    rintro l u v ⟨p, hp0, hpl, hstep⟩ hl
    simp only [pow_zero] at hl
    interval_cases l
    · exact Or.inl (by rw [← hp0, ← hpl])
    · refine Or.inr ?_
      have := hstep 0 (by norm_num)
      rw [hp0] at this
      simpa [hpl] using this
  | succ i ih =>
    rintro l u v ⟨p, hp0, hpl, hstep⟩ hl
    by_cases hle : l ≤ 2 ^ i
    · exact reachIn_succ_of i (ih l u v ⟨p, hp0, hpl, hstep⟩ hle)
    · have hgt : 2 ^ i < l := by omega
      refine ⟨p (2 ^ i), ?_, ?_⟩
      · exact ih (2 ^ i) u (p (2 ^ i)) ⟨p, hp0, rfl, fun j hj => hstep j (by omega)⟩ le_rfl
      · refine ih (l - 2 ^ i) (p (2 ^ i)) v
          ⟨fun j => p (2 ^ i + j), rfl, ?_, fun j hj => ?_⟩ ?_
        · have h1 : 2 ^ i + (l - 2 ^ i) = l := by omega
          simp only [h1, hpl]
        · have := hstep (2 ^ i + j) (by omega)
          simpa [Nat.add_assoc] using this
        · have h2 : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by ring
          omega

/-- Reachability yields a walk. -/
theorem pathOf_of_reflTransGen {u v : V} (h : Relation.ReflTransGen E u v) :
    ∃ l, PathOf E l u v := by
  induction h with
  | refl => exact ⟨0, fun _ => u, rfl, rfl, by omega⟩
  | @tail b c _ hbc ih =>
    obtain ⟨l, p, hp0, hpl, hstep⟩ := ih
    refine ⟨l + 1, fun j => if j ≤ l then p j else c, by simp [hp0], by simp, fun j hj => ?_⟩
    rcases Nat.lt_or_ge j l with h' | h'
    · have h1 : j ≤ l := by omega
      have h2 : j + 1 ≤ l := by omega
      simp only [h1, h2, if_pos]
      exact hstep j h'
    · have hj' : j = l := by omega
      subst hj'
      show E (if j ≤ j then p j else c) (if j + 1 ≤ j then p (j + 1) else c)
      rw [if_pos (le_refl j), if_neg (by omega : ¬ j + 1 ≤ j), hpl]
      exact hbc

/-- A walk with a repeated vertex can be shortened. -/
theorem exists_shorter_pathOf {u v : V} {l a b : ℕ} {p : ℕ → V}
    (hp0 : p 0 = u) (hpl : p l = v) (hstep : ∀ j < l, E (p j) (p (j + 1)))
    (hab : a < b) (hbl : b ≤ l) (heq : p a = p b) : ∃ l' < l, PathOf E l' u v := by
  refine ⟨l - (b - a), by omega, fun j => if j ≤ a then p j else p (j + (b - a)), ?_, ?_, ?_⟩
  · simp [hp0]
  · show (if l - (b - a) ≤ a then p (l - (b - a)) else p (l - (b - a) + (b - a))) = v
    rcases Nat.eq_or_lt_of_le (show a ≤ l - (b - a) by omega) with hcase | hcase
    · rw [if_pos (by omega), ← hcase, heq]
      have hb : b = l := by omega
      rw [hb, hpl]
    · rw [if_neg (by omega)]
      have h3 : l - (b - a) + (b - a) = l := by omega
      rw [h3, hpl]
  · intro j hj
    show E (if j ≤ a then p j else p (j + (b - a)))
      (if j + 1 ≤ a then p (j + 1) else p (j + 1 + (b - a)))
    rcases Nat.lt_or_ge j a with h1 | h1
    · rw [if_pos (by omega), if_pos (by omega)]
      exact hstep j (by omega)
    rcases Nat.eq_or_lt_of_le h1 with h2 | h2
    · -- j = a : we jump from `p a = p b` to `p (b+1)`
      rw [if_pos (by omega), if_neg (by omega)]
      have hpj : p j = p b := by rw [← h2]; exact heq
      have hbj : j + 1 + (b - a) = b + 1 := by omega
      rw [hpj, hbj]
      exact hstep b (by omega)
    · rw [if_neg (by omega), if_neg (by omega)]
      have h4 : j + 1 + (b - a) = (j + (b - a)) + 1 := by omega
      rw [h4]
      exact hstep (j + (b - a)) (by omega)

/-- In a finite vertex set, reachability is witnessed by a walk of length at most
`card V`. -/
theorem pathOf_short_of_reflTransGen [Fintype V] {u v : V}
    (h : Relation.ReflTransGen E u v) :
    ∃ l ≤ Fintype.card V, PathOf E l u v := by
  classical
  have hex : ∃ l, PathOf E l u v := pathOf_of_reflTransGen h
  set l := Nat.find hex with hlk
  have hl : PathOf E l u v := Nat.find_spec hex
  have hmin : ∀ l' < l, ¬ PathOf E l' u v := fun l' hl' => Nat.find_min hex hl'
  refine ⟨l, ?_, hl⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨p, hp0, hpl, hstep⟩ := hl
  have hnotinj : ¬ Function.Injective (fun j : Fin (l + 1) => p j) := by
    intro hinj
    have := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin] at this
    omega
  rw [Function.not_injective_iff] at hnotinj
  obtain ⟨a, b, hab, hne'⟩ := hnotinj
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · obtain ⟨l', hl', hp'⟩ :=
      exists_shorter_pathOf hp0 hpl hstep (a := (a : ℕ)) (b := (b : ℕ))
        (by exact_mod_cast hlt) (by omega) hab
    exact hmin l' hl' hp'
  · obtain ⟨l', hl', hp'⟩ :=
      exists_shorter_pathOf hp0 hpl hstep (a := (b : ℕ)) (b := (a : ℕ))
        (by exact_mod_cast hlt) (by omega) hab.symm
    exact hmin l' hl' hp'

/-- On a finite vertex set, `reachIn E i` is exactly reachability, provided
`card V ≤ 2 ^ i`. -/
theorem reachIn_iff_reflTransGen [Fintype V] {i : ℕ} (hi : Fintype.card V ≤ 2 ^ i)
    (u v : V) : reachIn E i u v ↔ Relation.ReflTransGen E u v := by
  refine ⟨reachIn_imp_reflTransGen, fun h => ?_⟩
  obtain ⟨l, hl, hp⟩ := pathOf_short_of_reflTransGen h
  exact reachIn_of_pathOf i l u v hp (le_trans hl hi)

end CS

import Mathlib
import RequestProject.Savitch.Model
import RequestProject.Savitch.Reach

/-!
# The state space of the Savitch simulator

Given a nondeterministic machine `M`, Savitch's algorithm explores the configuration
graph of `M` by the recursion

`reach (i+1) u v  ↔  ∃ w, reach i u w ∧ reach i w v`.

Implemented iteratively, its memory consists of a *mode* (a pending call, a returned
Boolean, or the final answer) together with a *stack* of at most `K` frames, each frame
recording `(u, v, i, j, ph)`: the endpoints of the pending call, its level, the index
`j` of the midpoint currently being tried, and a phase bit telling which of the two
halves is being computed.

This file sets up these raw states, the well-formedness predicate bounding the stack,
and the resulting cardinality bound (the states are encoded into a fixed finite type).
-/

namespace CS
namespace Savitch

variable {Sigma : Type}

/-- A `Bool`-valued classical decision procedure. -/
noncomputable def toBool (p : Prop) : Bool := @decide p (Classical.propDecidable p)

@[simp] theorem toBool_eq_true {p : Prop} : toBool p = true ↔ p := by
  unfold toBool
  exact @decide_eq_true_iff p (Classical.propDecidable p)

@[simp] theorem toBool_eq_false {p : Prop} : toBool p = false ↔ ¬ p := by
  unfold toBool
  simp [@decide_eq_false_iff_not p (Classical.propDecidable p)]

/-- Vertices of the configuration graph of `M`: the states of `M` together with an
extra sink `none`, which is reachable exactly from the accepting states. -/
abbrev Vert (M : NMachine Sigma) : Type := Option M.S

/-- The edge relation of the configuration graph, as a function of the input symbol
currently scanned. -/
def edgeSym (M : NMachine Sigma) (o : Option Sigma) : Vert M → Vert M → Prop
  | some u, some v => M.next u o v
  | some u, none => M.acc u
  | none, _ => False

/-- The input position that a vertex looks at. -/
def addrV (M : NMachine Sigma) : Vert M → ℕ
  | some u => M.addr u
  | none => 0

/-- The configuration graph of `M` on the input `x`. -/
def edgeX (M : NMachine Sigma) (x : List Sigma) (a b : Vert M) : Prop :=
  edgeSym M x[addrV M a]? a b

/-- The number of vertices of the configuration graph. -/
def cV (M : NMachine Sigma) : ℕ := Fintype.card (Vert M)

theorem cV_pos (M : NMachine Sigma) : 0 < cV M :=
  Fintype.card_pos_iff.mpr ⟨none⟩

theorem cV_eq (M : NMachine Sigma) : cV M = Fintype.card M.S + 1 := by
  simp [cV, Fintype.card_option]

/-- An enumeration of the vertices. -/
noncomputable def mid (M : NMachine Sigma) (j : ℕ) : Vert M :=
  if h : j < cV M then (Fintype.equivFin (Vert M)).symm ⟨j, h⟩ else none

theorem mid_surj (M : NMachine Sigma) (w : Vert M) : ∃ j, j < cV M ∧ mid M j = w := by
  refine ⟨(Fintype.equivFin (Vert M) w).val, (Fintype.equivFin (Vert M) w).isLt, ?_⟩
  unfold mid
  rw [dif_pos (show ((Fintype.equivFin (Vert M)) w).val < cV M from
    (Fintype.equivFin (Vert M) w).isLt)]
  simp

/-- The mode of the simulator. -/
inductive Mode (M : NMachine Sigma) where
  /-- `call u v i`: compute whether `v` is reachable from `u` within `2 ^ i` steps. -/
  | call (u v : Vert M) (i : ℕ)
  /-- `ret b`: return the value `b` to the caller. -/
  | ret (b : Bool)
  /-- `done b`: the computation has finished with answer `b`. -/
  | done (b : Bool)

/-- A stack frame `(u, v, i, j, ph)`. -/
abbrev Frame (M : NMachine Sigma) : Type := Vert M × Vert M × ℕ × ℕ × Bool

/-- A raw state of the simulator. -/
abbrev Raw (M : NMachine Sigma) : Type := Mode M × List (Frame M)

/-- Move on to the next candidate midpoint (or give up and return `false`). -/
noncomputable def advance (M : NMachine Sigma) (u v : Vert M) (i j : ℕ)
    (st : List (Frame M)) : Raw M :=
  if j + 1 < cV M then (Mode.call u (mid M (j + 1)) i, (u, v, i, j + 1, false) :: st)
  else (Mode.ret false, st)

/-- One step of the simulator, as a function of the input symbol currently scanned. -/
noncomputable def rawStep (M : NMachine Sigma) (o : Option Sigma) : Raw M → Raw M
  | (Mode.call u v 0, st) => (Mode.ret (toBool (u = v ∨ edgeSym M o u v)), st)
  | (Mode.call u v (i + 1), st) =>
      (Mode.call u (mid M 0) i, (u, v, i, 0, false) :: st)
  | (Mode.ret b, []) => (Mode.done b, [])
  | (Mode.ret b, (u, v, i, j, ph) :: st) =>
      if ph then
        (if b then (Mode.ret true, st) else advance M u v i j st)
      else
        (if b then (Mode.call (mid M j) v i, (u, v, i, j, true) :: st)
          else advance M u v i j st)
  | (Mode.done b, st) => (Mode.done b, st)

@[simp] theorem rawStep_call_zero (M : NMachine Sigma) (o : Option Sigma) (u v : Vert M)
    (st : List (Frame M)) :
    rawStep M o (Mode.call u v 0, st) = (Mode.ret (toBool (u = v ∨ edgeSym M o u v)), st) :=
  rfl

@[simp] theorem rawStep_call_succ (M : NMachine Sigma) (o : Option Sigma) (u v : Vert M)
    (i : ℕ) (st : List (Frame M)) :
    rawStep M o (Mode.call u v (i + 1), st) =
      (Mode.call u (mid M 0) i, (u, v, i, 0, false) :: st) := rfl

@[simp] theorem rawStep_ret_nil (M : NMachine Sigma) (o : Option Sigma) (b : Bool) :
    rawStep M o (Mode.ret b, ([] : List (Frame M))) = (Mode.done b, []) := rfl

@[simp] theorem rawStep_ret_cons (M : NMachine Sigma) (o : Option Sigma) (b : Bool)
    (u v : Vert M) (i j : ℕ) (ph : Bool) (st : List (Frame M)) :
    rawStep M o (Mode.ret b, (u, v, i, j, ph) :: st) =
      (if ph then (if b then (Mode.ret true, st) else advance M u v i j st)
        else (if b then (Mode.call (mid M j) v i, (u, v, i, j, true) :: st)
          else advance M u v i j st)) := rfl

@[simp] theorem rawStep_done (M : NMachine Sigma) (o : Option Sigma) (b : Bool)
    (st : List (Frame M)) : rawStep M o (Mode.done b, st) = (Mode.done b, st) := rfl

/-- Well-formedness of a stack: levels decrease fast enough that the stack has depth at
most `K`, and midpoint indices are in range. -/
def WFstack (M : NMachine Sigma) (K : ℕ) : List (Frame M) → Prop
  | [] => True
  | (_, _, i, j, _) :: st => i + st.length + 1 ≤ K ∧ j < cV M ∧ WFstack M K st

/-- Well-formedness of a raw state. -/
def WFraw (M : NMachine Sigma) (K : ℕ) : Raw M → Prop
  | (Mode.call _ _ i, st) => i + st.length ≤ K ∧ WFstack M K st
  | (Mode.ret _, st) => WFstack M K st
  | (Mode.done _, st) => WFstack M K st

theorem WFstack.length_le {M : NMachine Sigma} {K : ℕ} :
    ∀ {st : List (Frame M)}, WFstack M K st → st.length ≤ K
  | [], _ => Nat.zero_le _
  | (_, _, _, _, _) :: st, h => by
      simp only [List.length_cons]
      exact le_trans (by omega) h.1

theorem WFstack.tail {M : NMachine Sigma} {K : ℕ} {f : Frame M} {st : List (Frame M)}
    (h : WFstack M K (f :: st)) : WFstack M K st := by
  obtain ⟨u, v, i, j, ph⟩ := f
  exact h.2.2

theorem wf_advance {M : NMachine Sigma} {K : ℕ} {u v : Vert M} {i j : ℕ}
    {st : List (Frame M)} (hf : i + st.length + 1 ≤ K) (hst : WFstack M K st) :
    WFraw M K (advance M u v i j st) := by
  unfold advance
  split
  · exact ⟨by simp only [List.length_cons]; omega, by exact ⟨by omega, by omega, hst⟩⟩
  · exact hst

theorem wf_rawStep {M : NMachine Sigma} {K : ℕ} (o : Option Sigma) {s : Raw M}
    (h : WFraw M K s) : WFraw M K (rawStep M o s) := by
  obtain ⟨m, st⟩ := s
  match m, st with
  | Mode.call u v 0, st => exact h.2
  | Mode.call u v (i + 1), st =>
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, ?_, cV_pos M, h2⟩
      · show i + (st.length + 1) ≤ K
        omega
      · show i + st.length + 1 ≤ K
        omega
  | Mode.ret b, [] => exact trivial
  | Mode.ret b, (u, v, i, j, ph) :: st =>
      obtain ⟨h1, h2, h3⟩ := h
      simp only [rawStep_ret_cons]
      split
      · split
        · exact h3
        · exact wf_advance h1 h3
      · split
        · exact ⟨by simp only [List.length_cons]; omega, by exact ⟨h1, h2, h3⟩⟩
        · exact wf_advance h1 h3
  | Mode.done b, st => exact h

/-! ### Encoding the well-formed states into a fixed finite type -/

/-- Encoded frames. -/
abbrev FrameE (M : NMachine Sigma) (K : ℕ) : Type :=
  Vert M × Vert M × Fin (K + 1) × Fin (cV M) × Bool

/-- Encoded modes. -/
abbrev ModeE (M : NMachine Sigma) (K : ℕ) : Type :=
  (Vert M × Vert M × Fin (K + 1)) ⊕ Bool ⊕ Bool

/-- The finite type into which well-formed raw states are encoded. -/
abbrev RawE (M : NMachine Sigma) (K : ℕ) : Type :=
  ModeE M K × (Fin (K + 1) → Option (FrameE M K))

/-- Encoding of frames. -/
def encFrame (M : NMachine Sigma) (K : ℕ) (f : Frame M) : FrameE M K :=
  (f.1, f.2.1, ⟨min f.2.2.1 K, by omega⟩,
    ⟨min f.2.2.2.1 (cV M - 1), by have := cV_pos M; omega⟩, f.2.2.2.2)

theorem encFrame_inj {M : NMachine Sigma} {K : ℕ} {f g : Frame M}
    (hf : f.2.2.1 ≤ K ∧ f.2.2.2.1 < cV M) (hg : g.2.2.1 ≤ K ∧ g.2.2.2.1 < cV M)
    (h : encFrame M K f = encFrame M K g) : f = g := by
  obtain ⟨u, v, i, j, ph⟩ := f
  obtain ⟨u', v', i', j', ph'⟩ := g
  simp only [encFrame, Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only at hf hg
  have : i = i' := by omega
  have : j = j' := by omega
  simp_all

/-- Encoding of modes. -/
def encMode (M : NMachine Sigma) (K : ℕ) : Mode M → ModeE M K
  | Mode.call u v i => Sum.inl (u, v, ⟨min i K, by omega⟩)
  | Mode.ret b => Sum.inr (Sum.inl b)
  | Mode.done b => Sum.inr (Sum.inr b)

/-- Encoding of raw states. -/
def encRaw (M : NMachine Sigma) (K : ℕ) (s : Raw M) : RawE M K :=
  (encMode M K s.1, fun idx => (s.2[idx.val]?).map (encFrame M K))

theorem wfstack_mem_bounds {M : NMachine Sigma} {K : ℕ} :
    ∀ {st : List (Frame M)}, WFstack M K st →
      ∀ (n : ℕ) (f : Frame M), f ∈ st[n]? → f.2.2.1 ≤ K ∧ f.2.2.2.1 < cV M
  | [], _, n, f, hf => by simp at hf
  | (u, v, i, j, ph) :: st, h, n, f, hf => by
      match n with
      | 0 =>
        simp only [List.getElem?_cons_zero, Option.mem_def, Option.some.injEq] at hf
        subst hf
        refine ⟨?_, h.2.1⟩
        show i ≤ K
        have := h.1
        omega
      | (n + 1) =>
        simp only [List.getElem?_cons_succ] at hf
        exact wfstack_mem_bounds h.2.2 n f hf

theorem encRaw_inj {M : NMachine Sigma} {K : ℕ} {s t : Raw M}
    (hs : WFraw M K s) (ht : WFraw M K t) (h : encRaw M K s = encRaw M K t) : s = t := by
  obtain ⟨m, st⟩ := s
  obtain ⟨m', st'⟩ := t
  have hm : encMode M K m = encMode M K m' := congrArg Prod.fst h
  have hst : (fun idx : Fin (K + 1) => (st[idx.val]?).map (encFrame M K))
      = (fun idx : Fin (K + 1) => (st'[idx.val]?).map (encFrame M K)) := congrArg Prod.snd h
  have hstacks : st = st' := by
    have hlen : st.length ≤ K := by
      cases m <;> exact WFstack.length_le (by first | exact hs.2 | exact hs)
    have hlen' : st'.length ≤ K := by
      cases m' <;> exact WFstack.length_le (by first | exact ht.2 | exact ht)
    have hwf : WFstack M K st := by cases m <;> first | exact hs.2 | exact hs
    have hwf' : WFstack M K st' := by cases m' <;> first | exact ht.2 | exact ht
    apply List.ext_getElem?
    intro n
    by_cases hn : n ≤ K
    · have := congrFun hst ⟨n, by omega⟩
      simp only at this
      rcases hx : st[n]? with _ | f <;> rcases hy : st'[n]? with _ | g <;>
        rw [hx, hy] at this
      · simp at this
      · simp at this
      · simp only [Option.map_some, Option.some.injEq] at this
        exact congrArg some (encFrame_inj (wfstack_mem_bounds hwf n f hx)
          (wfstack_mem_bounds hwf' n g hy) this)
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  subst hstacks
  have : m = m' := by
    cases m with
    | call u v i =>
      cases m' with
      | call u' v' i' =>
        simp only [encMode, Sum.inl.injEq, Prod.mk.injEq, Fin.mk.injEq] at hm
        obtain ⟨h1, h2, h3⟩ := hm
        have hi : i ≤ K := by have := hs.1; omega
        have hi' : i' ≤ K := by have := ht.1; omega
        have : i = i' := by omega
        simp_all
      | ret b => simp [encMode] at hm
      | done b => simp [encMode] at hm
    | ret b =>
      cases m' with
      | call u' v' i' => simp [encMode] at hm
      | ret b' => simpa [encMode] using hm
      | done b' => simp [encMode] at hm
    | done b =>
      cases m' with
      | call u' v' i' => simp [encMode] at hm
      | ret b' => simp [encMode] at hm
      | done b' => simpa [encMode] using hm
  rw [this]

/-- The (finite) state space of the Savitch simulator. -/
noncomputable instance instFintypeWF (M : NMachine Sigma) (K : ℕ) :
    Fintype {s : Raw M // WFraw M K s} :=
  Fintype.ofInjective (fun s => encRaw M K s.1)
    (fun s t h => Subtype.ext (encRaw_inj s.2 t.2 h))

theorem card_WF_le (M : NMachine Sigma) (K : ℕ) :
    Fintype.card {s : Raw M // WFraw M K s} ≤
      ((Fintype.card M.S + 1) * (Fintype.card M.S + 1) * (K + 1) + 2 + 2) *
        ((Fintype.card M.S + 1) * (Fintype.card M.S + 1) * (K + 1) *
          (Fintype.card M.S + 1) * 2 + 1) ^ (K + 1) := by
  have h := Fintype.card_le_of_injective (fun s : {s : Raw M // WFraw M K s} => encRaw M K s.1)
    (fun s t h => Subtype.ext (encRaw_inj s.2 t.2 h))
  refine le_trans h (le_of_eq ?_)
  simp only [RawE, Fintype.card_prod, Fintype.card_sum, Fintype.card_bool, Fintype.card_fun,
    Fintype.card_option, Fintype.card_fin, cV]
  ring

end Savitch
end CS

