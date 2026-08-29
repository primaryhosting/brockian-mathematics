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
import RequestProject.Savitch.Reach

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The deterministic simulator

This file defines the deterministic machine used in Savitch's theorem: an explicit
iterative (stack based) implementation of the recursive procedure

```
REACH d u v  =  if d = 0 then (u = v ∨ u → v)
                else ∃ m, REACH (d-1) u m ∧ REACH (d-1) m v
```

together with its encoding into bit strings and the space accounting: a well-formed
state occupies `O((f n)²)` bits, because the stack holds at most `f n + 2` frames of
`O(f n)` bits each.
-/

namespace CS
namespace Savitch

/-- Classical truth value of a proposition. -/
noncomputable def toBool (P : Prop) : Bool := @decide P (Classical.propDecidable P)

@[simp] lemma toBool_eq_true {P : Prop} : toBool P = true ↔ P := by
  simp [toBool, @decide_eq_true_iff P (Classical.propDecidable P)]

/-- A frame of the recursion stack: the recursion depth `level`, the endpoints `u`, `v`
of the subproblem, the `phase` of the frame (0: freshly entered, 1: waiting for the
first recursive call, 2: waiting for the second one) and the index `idx` of the
midpoint candidate currently being tried. -/
structure Frame where
  /-- Recursion depth of this subproblem. -/
  level : ℕ
  /-- Source configuration. -/
  u : Word
  /-- Target configuration. -/
  v : Word
  /-- Phase of the frame. -/
  phase : ℕ
  /-- Index of the midpoint candidate currently tried. -/
  idx : ℕ

/-- States of the deterministic simulator. -/
inductive SavState where
  /-- Measuring the length of the input; the head is at position `k`. -/
  | count (k : ℕ)
  /-- Looking for an accepting configuration; `j` is the index of the candidate. -/
  | scan (n j : ℕ)
  /-- Running the recursion for the target candidate `j` with the given stack and the
  boolean returned by the last completed call. -/
  | main (n j : ℕ) (st : List Frame) (ret : Bool)
  /-- Halted with output `b`. -/
  | done (b : Bool)

/-- Position of the input head in a given state. -/
def shead (N : NDetMachine) : SavState → ℕ
  | .count k => k
  | .main _ _ (F :: _) _ => N.head F.u
  | _ => 0

/-- Move to the next midpoint candidate of the top frame, or return `false` if the
candidates are exhausted. -/
def advance (n j : ℕ) (F : Frame) (rest : List Frame) (ret : Bool) (s : ℕ) : SavState :=
  if F.idx + 1 < (cands s).length then
    .main n j (⟨F.level - 1, F.u, (cands s).getD (F.idx + 1) [], 0, 0⟩ ::
      ⟨F.level, F.u, F.v, 1, F.idx + 1⟩ :: rest) ret
  else .main n j rest false

/-- One step of the deterministic simulator of `N` (whose space bound is `f`). -/
noncomputable def sstep (N : NDetMachine) (f : ℕ → ℕ) : SavState → Option Bool → SavState
  | .count k, none => .scan k 0
  | .count k, some _ => .count (k + 1)
  | .scan n j, _ =>
      if j < (cands (f n)).length then
        (if toBool (N.accept ((cands (f n)).getD j [])) then
          .main n j [⟨f n + 1, N.init, (cands (f n)).getD j [], 0, 0⟩] false
        else .scan n (j + 1))
      else .done false
  | .main n j [] ret, _ => if ret then .done true else .scan n (j + 1)
  | .main n j (F :: rest) ret, b =>
      if F.phase = 0 then
        (if F.level = 0 then .main n j rest (toBool (F.u = F.v ∨ N.step F.u b F.v))
        else .main n j (⟨F.level - 1, F.u, (cands (f n)).getD 0 [], 0, 0⟩ ::
          ⟨F.level, F.u, F.v, 1, 0⟩ :: rest) ret)
      else if F.phase = 1 then
        (if ret then .main n j (⟨F.level - 1, (cands (f n)).getD F.idx [], F.v, 0, 0⟩ ::
            ⟨F.level, F.u, F.v, 2, F.idx⟩ :: rest) ret
        else advance n j F rest ret (f n))
      else
        (if ret then .main n j rest true else advance n j F rest ret (f n))
  | .done b, _ => .done b

/-- Halting states. -/
def shalt : SavState → Bool
  | .done _ => true
  | _ => false

/-- Output bit. -/
def sout : SavState → Bool
  | .done b => b
  | _ => false

/-! ### Encoding of states as bit strings -/

/-- The registers of a stack frame. -/
def frameRegs (F : Frame) : List Word :=
  [natBits F.level, F.u, F.v, natBits F.phase, natBits F.idx]

/-- The registers of a state. -/
def stateRegs : SavState → List Word
  | .count k => [[false, false], natBits k]
  | .scan n j => [[false, true], natBits n, natBits j]
  | .main n j st ret => [[true, false], natBits n, natBits j, [ret]] ++ st.flatMap frameRegs
  | .done b => [[true, true], [b]]

/-- The encoding of a state as a bit string. -/
def encSav (st : SavState) : Word := encRegs (stateRegs st)

lemma frameRegs_length (F : Frame) : (frameRegs F).length = 5 := rfl

lemma frameRegs_inj : Function.Injective frameRegs := by
  intro F G h
  simp only [frameRegs, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e1 := natBits_injective h1
  have e4 := natBits_injective h4
  have e5 := natBits_injective h5
  cases F; cases G
  simp_all

lemma flatMap_frameRegs_length (st : List Frame) :
    (st.flatMap frameRegs).length = 5 * st.length := by
  induction st with
  | nil => simp
  | cons F st ih =>
    simp only [List.flatMap_cons, List.length_append, ih, frameRegs_length, List.length_cons]
    ring

lemma flatMap_frameRegs_inj : ∀ (st st' : List Frame),
    st.flatMap frameRegs = st'.flatMap frameRegs → st = st' := by
  intro st
  induction st with
  | nil =>
    intro st' h
    cases st' with
    | nil => rfl
    | cons G r => exfalso; simp [frameRegs] at h
  | cons F st ih =>
    intro st' h
    cases st' with
    | nil => exfalso; simp [frameRegs] at h
    | cons G r =>
      simp only [List.flatMap_cons] at h
      obtain ⟨h1, h2⟩ := List.append_inj h (by simp [frameRegs_length])
      rw [frameRegs_inj h1, ih r h2]

lemma stateRegs_inj : Function.Injective stateRegs := by
  intro a b h
  cases a with
  | count k =>
    cases b with
    | count k' =>
      simp only [stateRegs, List.cons.injEq, and_true, true_and] at h
      rw [natBits_injective h]
    | scan n j => exfalso; simp [stateRegs] at h
    | main n j st r => exfalso; simp [stateRegs] at h
    | done c => exfalso; simp [stateRegs] at h
  | scan n j =>
    cases b with
    | count k' => exfalso; simp [stateRegs] at h
    | scan n' j' =>
      simp only [stateRegs, List.cons.injEq, and_true, true_and] at h
      rw [natBits_injective h.1, natBits_injective h.2]
    | main n' j' st r => exfalso; simp [stateRegs] at h
    | done c => exfalso; simp [stateRegs] at h
  | main n j st r =>
    cases b with
    | count k' => exfalso; simp [stateRegs] at h
    | scan n' j' => exfalso; simp [stateRegs] at h
    | main n' j' st' r' =>
      simp only [stateRegs, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      rw [natBits_injective h1, natBits_injective h2,
        show r = r' from by simpa using h3, flatMap_frameRegs_inj st st' h4]
    | done c => exfalso; simp [stateRegs] at h
  | done c =>
    cases b with
    | count k' => exfalso; simp [stateRegs] at h
    | scan n' j' => exfalso; simp [stateRegs] at h
    | main n' j' st' r' => exfalso; simp [stateRegs] at h
    | done c' =>
      simp only [stateRegs, List.cons.injEq, and_true, true_and] at h
      rw [show c = c' from by simpa using h]

lemma encSav_injective : Function.Injective encSav := fun _ _ h =>
  stateRegs_inj (encRegs_injective h)

/-! ### Well-formed states -/

/-- Well-formedness of a single frame relative to the space bound `s`. -/
def WFframe (s : ℕ) (F : Frame) : Prop :=
  F.u.length ≤ s ∧ F.v.length ≤ s ∧ F.phase ≤ 2 ∧ F.idx < (cands s).length ∧
    (F.phase = 0 ∨ 1 ≤ F.level)

/-- Well-formedness of the recursion stack: the levels decrease by one from the bottom
frame (of level `s+1`) to the top. -/
def WFstack (s : ℕ) : List Frame → Prop
  | [] => True
  | F :: rest => WFframe s F ∧ F.level + rest.length = s + 1 ∧ WFstack s rest

lemma WFstack_length_le {s : ℕ} : ∀ {st : List Frame}, WFstack s st → st.length ≤ s + 2 := by
  intro st h
  cases st with
  | nil => simp
  | cons F rest =>
    obtain ⟨-, hlev, -⟩ := h
    simp only [List.length_cons]
    omega

lemma WFstack_mem {s : ℕ} : ∀ {st : List Frame}, WFstack s st →
    ∀ F ∈ st, WFframe s F ∧ F.level ≤ s + 1 := by
  intro st
  induction st with
  | nil => intro _ F hF; exact absurd hF (by simp)
  | cons G rest ih =>
    intro h F hF
    obtain ⟨hG, hlev, hrest⟩ := h
    rcases List.mem_cons.1 hF with rfl | hF'
    · exact ⟨hG, by omega⟩
    · exact ih hrest F hF'

/-- Well-formedness of a state of the simulator, relative to the input `x`. -/
def WFstate (N : NDetMachine) (f : ℕ → ℕ) (x : Word) : SavState → Prop
  | .count k => k ≤ x.length
  | .scan n j => n = x.length ∧ j ≤ (cands (f x.length)).length
  | .main n j st _ =>
      n = x.length ∧ j < (cands (f x.length)).length ∧ WFstack (f x.length) st
  | .done _ => True

end Savitch
end CS

import Mathlib
import RequestProject.Savitch.Encoding

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Space-bounded machines and the classes `DSPACE` / `NSPACE`

A machine has a read-only input `x : Word`, accessed one symbol at a time through an
input head whose position is determined by the current memory, and a *work memory*
which is itself a bit string.  The **space** used by the machine on an input is the
length of its work memory; this is the only resource that is measured.

Both the deterministic and the nondeterministic model are formalised in this way, so
that Savitch's theorem is a statement purely about memory usage.
-/

namespace CS

/-- A language is a set of bit strings. -/
abbrev Language := Word → Prop

/-- A deterministic space-bounded machine: the work memory is a bit string, the input
head position is a function of the memory, and one step reads the input symbol under the
head (`none` if the head is past the end of the input) and updates the memory. -/
structure DetMachine where
  /-- Position of the (read-only) input head, as a function of the work memory. -/
  head : Word → ℕ
  /-- One computation step: new memory from the old memory and the scanned input symbol. -/
  step : Word → Option Bool → Word
  /-- Halting memory configurations. -/
  halt : Word → Bool
  /-- Output bit of a memory configuration. -/
  out : Word → Bool
  /-- Initial memory. -/
  init : Word
  /-- Halting configurations do not change any more. -/
  halt_fix : ∀ w b, halt w = true → step w b = w

namespace DetMachine

/-- The memory configuration after `t` steps on input `x`. -/
def run (M : DetMachine) (x : Word) : ℕ → Word
  | 0 => M.init
  | t + 1 => M.step (M.run x t) x[M.head (M.run x t)]?

/-- `M` decides `L`: on every input it halts with the correct output bit. -/
def Decides (M : DetMachine) (L : Language) : Prop :=
  ∀ x, ∃ t, M.halt (M.run x t) = true ∧ (M.out (M.run x t) = true ↔ L x)

/-- `M` runs in space `f`: on every input `x`, the memory never exceeds `f |x|` bits. -/
def SpaceBounded (M : DetMachine) (f : ℕ → ℕ) : Prop :=
  ∀ x t, (M.run x t).length ≤ f x.length

lemma run_stable_of_halt (M : DetMachine) (x : Word) {t : ℕ}
    (h : M.halt (M.run x t) = true) : ∀ t', t ≤ t' → M.run x t' = M.run x t := by
  intro t'
  induction t' with
  | zero =>
    intro ht
    have : t = 0 := Nat.le_zero.mp ht
    subst this
    rfl
  | succ t' ih =>
    intro ht
    rcases Nat.lt_or_ge t (t' + 1) with hlt | hge
    · have ht' : t ≤ t' := by omega
      rw [run, ih ht', M.halt_fix _ _ h]
    · have ht2 : t = t' + 1 := by omega
      rw [ht2]

end DetMachine

/-- A nondeterministic space-bounded machine, with the same memory conventions as
`DetMachine` but a transition *relation* and a set of accepting configurations. -/
structure NDetMachine where
  /-- Position of the (read-only) input head, as a function of the work memory. -/
  head : Word → ℕ
  /-- Transition relation: from a memory and the scanned input symbol to a new memory. -/
  step : Word → Option Bool → Word → Prop
  /-- Accepting memory configurations. -/
  accept : Word → Prop
  /-- Initial memory. -/
  init : Word

namespace NDetMachine

/-- One nondeterministic step on input `x`. -/
def stepOn (N : NDetMachine) (x : Word) (w w' : Word) : Prop := N.step w x[N.head w]? w'

/-- Reachability in the configuration graph of `N` on input `x`. -/
def Reach (N : NDetMachine) (x : Word) : Word → Word → Prop :=
  Relation.ReflTransGen (N.stepOn x)

/-- `N` accepts `x` if some accepting configuration is reachable. -/
def Accepts (N : NDetMachine) (x : Word) : Prop :=
  ∃ w, N.Reach x N.init w ∧ N.accept w

/-- `N` runs in space `f`: every reachable configuration has at most `f |x|` bits. -/
def SpaceBounded (N : NDetMachine) (f : ℕ → ℕ) : Prop :=
  ∀ x w, N.Reach x N.init w → w.length ≤ f x.length

end NDetMachine

/-- Deterministic space complexity class. -/
def DSPACE (f : ℕ → ℕ) : Set Language :=
  {L | ∃ M : DetMachine, M.Decides L ∧ M.SpaceBounded f}

/-- Nondeterministic space complexity class. -/
def NSPACE (f : ℕ → ℕ) : Set Language :=
  {L | ∃ N : NDetMachine, (∀ x, N.Accepts x ↔ L x) ∧ N.SpaceBounded f}

lemma DSPACE_mono {f g : ℕ → ℕ} (h : ∀ n, f n ≤ g n) : DSPACE f ⊆ DSPACE g := by
  rintro L ⟨M, hM, hs⟩
  exact ⟨M, hM, fun x t => le_trans (hs x t) (h _)⟩

lemma NSPACE_mono {f g : ℕ → ℕ} (h : ∀ n, f n ≤ g n) : NSPACE f ⊆ NSPACE g := by
  rintro L ⟨N, hN, hs⟩
  exact ⟨N, hN, fun x w hw => le_trans (hs x w hw) (h _)⟩

/-- Every deterministic machine is a nondeterministic machine. -/
def DetMachine.toNDet (M : DetMachine) : NDetMachine where
  head := M.head
  step w b w' := w' = M.step w b
  accept w := M.halt w = true ∧ M.out w = true
  init := M.init

lemma DetMachine.toNDet_reach (M : DetMachine) (x w : Word) :
    M.toNDet.Reach x M.init w ↔ ∃ t, w = M.run x t := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail hab hbc ih =>
      obtain ⟨t, rfl⟩ := ih
      exact ⟨t + 1, hbc⟩
  · rintro ⟨t, rfl⟩
    induction t with
    | zero => exact Relation.ReflTransGen.refl
    | succ t ih => exact ih.tail rfl

lemma DSPACE_subset_NSPACE (f : ℕ → ℕ) : DSPACE f ⊆ NSPACE f := by
  rintro L ⟨M, hdec, hsp⟩
  refine ⟨M.toNDet, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨w, hw, hacc⟩
      obtain ⟨t, rfl⟩ := (M.toNDet_reach x w).1 hw
      obtain ⟨t₀, ht₀, hout⟩ := hdec x
      have h1 : M.halt (M.run x t) = true := hacc.1
      have hmax : M.run x (max t t₀) = M.run x t :=
        M.run_stable_of_halt x h1 _ (le_max_left _ _)
      have hmax0 : M.run x (max t t₀) = M.run x t₀ :=
        M.run_stable_of_halt x ht₀ _ (le_max_right _ _)
      have : M.run x t = M.run x t₀ := by rw [← hmax, hmax0]
      exact hout.1 (this ▸ hacc.2)
    · intro hx
      obtain ⟨t, ht, hout⟩ := hdec x
      exact ⟨M.run x t, (M.toNDet_reach x _).2 ⟨t, rfl⟩, ht, hout.2 hx⟩
  · intro x w hw
    obtain ⟨t, rfl⟩ := (M.toNDet_reach x w).1 hw
    exact hsp x t

/-!
### Abstract machines

It is convenient to describe a deterministic machine by an abstract (structured) memory
type together with an injective encoding into bit strings.
-/

/-- A deterministic machine whose memory is an arbitrary type `S`, together with an
injective encoding of `S` into bit strings. -/
structure AbsMachine (S : Type) where
  /-- Input head position. -/
  head : S → ℕ
  /-- Transition function. -/
  step : S → Option Bool → S
  /-- Halting states. -/
  halt : S → Bool
  /-- Output bit. -/
  out : S → Bool
  /-- Initial state. -/
  init : S
  /-- Encoding of the abstract memory as a bit string. -/
  enc : S → Word
  /-- The encoding is injective. -/
  enc_inj : Function.Injective enc
  /-- Halting states do not change any more. -/
  halt_fix : ∀ s b, halt s = true → step s b = s

namespace AbsMachine

variable {S : Type} (A : AbsMachine S)

/-- The abstract state after `t` steps on input `x`. -/
def run (A : AbsMachine S) (x : Word) : ℕ → S
  | 0 => A.init
  | t + 1 => A.step (A.run x t) x[A.head (A.run x t)]?

lemma run_eq_iterate (x : Word) (t : ℕ) :
    A.run x t = (fun s => A.step s x[A.head s]?)^[t] A.init := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ← ih]; rfl

/-- Decoding a bit string back to an abstract state (junk value off the image). -/
noncomputable def dec (A : AbsMachine S) (w : Word) : S :=
  haveI : Nonempty S := ⟨A.init⟩
  Function.invFun A.enc w

@[simp] lemma dec_enc (s : S) : A.dec (A.enc s) = s := by
  haveI : Nonempty S := ⟨A.init⟩
  exact Function.leftInverse_invFun A.enc_inj s

/-- The deterministic bit-string machine obtained by transporting an abstract machine
along its encoding. -/
noncomputable def toDet (A : AbsMachine S) : DetMachine where
  head w := if A.enc (A.dec w) = w then A.head (A.dec w) else 0
  step w b := if A.enc (A.dec w) = w then A.enc (A.step (A.dec w) b) else w
  halt w := if A.enc (A.dec w) = w then A.halt (A.dec w) else true
  out w := if A.enc (A.dec w) = w then A.out (A.dec w) else false
  init := A.enc A.init
  halt_fix := by
    intro w b hw
    by_cases h : A.enc (A.dec w) = w
    · simp only [if_pos h] at hw ⊢
      rw [A.halt_fix _ _ hw, h]
    · simp only [if_neg h]

@[simp] lemma toDet_head_enc (s : S) : A.toDet.head (A.enc s) = A.head s := by
  simp [toDet]

@[simp] lemma toDet_step_enc (s : S) (b : Option Bool) :
    A.toDet.step (A.enc s) b = A.enc (A.step s b) := by
  simp [toDet]

@[simp] lemma toDet_halt_enc (s : S) : A.toDet.halt (A.enc s) = A.halt s := by
  simp [toDet]

@[simp] lemma toDet_out_enc (s : S) : A.toDet.out (A.enc s) = A.out s := by
  simp [toDet]

lemma toDet_run (x : Word) (t : ℕ) : A.toDet.run x t = A.enc (A.run x t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [DetMachine.run, ih, toDet_head_enc, toDet_step_enc, run]

lemma toDet_decides (L : Language)
    (h : ∀ x, ∃ t, A.halt (A.run x t) = true ∧ (A.out (A.run x t) = true ↔ L x)) :
    A.toDet.Decides L := by
  intro x
  obtain ⟨t, ht, hout⟩ := h x
  exact ⟨t, by rw [toDet_run, toDet_halt_enc]; exact ht,
    by rw [toDet_run, toDet_out_enc]; exact hout⟩

lemma toDet_spaceBounded (f : ℕ → ℕ)
    (h : ∀ x t, (A.enc (A.run x t)).length ≤ f x.length) : A.toDet.SpaceBounded f := by
  intro x t
  rw [toDet_run]
  exact h x t

end AbsMachine

end CS

import Mathlib

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Self-delimiting binary encodings

This file provides the elementary encoding machinery used to store structured data
(natural numbers, lists of bit strings) inside a single bit string, together with the
length estimates needed for the space accounting in Savitch's theorem.
-/

namespace CS

/-- A word is a finite bit string. -/
abbrev Word := List Bool

/-- Binary representation of a natural number, least significant bit first,
with no leading zeros. -/
def natBits (n : ℕ) : Word := (List.range (Nat.size n)).map n.testBit

@[simp] lemma natBits_length (n : ℕ) : (natBits n).length = Nat.size n := by
  simp [natBits]

lemma natBits_injective : Function.Injective natBits := by
  intro m n h
  have hl : Nat.size m = Nat.size n := by
    have := congrArg List.length h; simpa using this
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < Nat.size m
  · have := congrArg (fun l => l[i]?) h
    simp [natBits, hi, hl ▸ hi] at this
    simpa using this
  · have h1 : m < 2 ^ i :=
      lt_of_lt_of_le (Nat.lt_size_self m) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : n < 2 ^ i :=
      lt_of_lt_of_le (Nat.lt_size_self n) (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt h1, Nat.testBit_eq_false_of_lt h2]

/-- Self-delimiting code of a single word: every bit is doubled and the code word
`[true, false]` is used as a terminator. -/
def dbl (w : Word) : Word := (w.flatMap fun b => [b, b]) ++ [true, false]

@[simp] lemma dbl_nil : dbl [] = [true, false] := rfl

@[simp] lemma dbl_cons (b : Bool) (w : Word) : dbl (b :: w) = b :: b :: dbl w := by
  simp [dbl]

@[simp] lemma dbl_length (w : Word) : (dbl w).length = 2 * w.length + 2 := by
  induction w with
  | nil => simp
  | cons b w ih => simp [ih]; omega

lemma dbl_app_inj : ∀ (w₁ w₂ r₁ r₂ : Word), dbl w₁ ++ r₁ = dbl w₂ ++ r₂ → w₁ = w₂ ∧ r₁ = r₂ := by
  intro w₁
  induction w₁ with
  | nil =>
    intro w₂ r₁ r₂ h
    cases w₂ with
    | nil => simpa using h
    | cons b w =>
      exfalso
      rw [dbl_nil, dbl_cons] at h
      cases b <;> simp at h
  | cons b₁ w₁ ih =>
    intro w₂ r₁ r₂ h
    cases w₂ with
    | nil =>
      exfalso
      rw [dbl_nil, dbl_cons] at h
      cases b₁ <;> simp at h
    | cons b₂ w₂ =>
      rw [dbl_cons, dbl_cons] at h
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hb, -, h⟩ := h
      obtain ⟨hw, hr⟩ := ih w₂ r₁ r₂ h
      exact ⟨by rw [hb, hw], hr⟩

/-- Encoding of a list of "registers" (words) into a single word. -/
def encRegs (l : List Word) : Word := (l.flatMap dbl) ++ [false, true]

lemma encRegs_aux : ∀ (l₁ l₂ : List Word) (r₁ r₂ : Word),
    (l₁.flatMap dbl) ++ ([false, true] ++ r₁) = (l₂.flatMap dbl) ++ ([false, true] ++ r₂) →
    l₁ = l₂ ∧ r₁ = r₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ r₁ r₂ h
    cases l₂ with
    | nil => simpa using h
    | cons w l =>
      exfalso
      simp only [List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_assoc] at h
      cases w with
      | nil => rw [dbl_nil] at h; simp at h
      | cons b w =>
        rw [dbl_cons] at h
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨h1, h2, -⟩ := h
        simp [← h1] at h2
  | cons w₁ l₁ ih =>
    intro l₂ r₁ r₂ h
    cases l₂ with
    | nil =>
      exfalso
      simp only [List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_assoc] at h
      cases w₁ with
      | nil => rw [dbl_nil] at h; simp at h
      | cons b w =>
        rw [dbl_cons] at h
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨h1, h2, -⟩ := h
        simp [h1] at h2
    | cons w₂ l₂ =>
      simp only [List.flatMap_cons, List.append_assoc] at h
      obtain ⟨hw, h⟩ := dbl_app_inj _ _ _ _ h
      obtain ⟨hl, hr⟩ := ih l₂ r₁ r₂ h
      exact ⟨by rw [hw, hl], hr⟩

lemma encRegs_injective : Function.Injective encRegs := by
  intro l₁ l₂ h
  have h' : (l₁.flatMap dbl) ++ ([false, true] ++ ([] : Word)) =
      (l₂.flatMap dbl) ++ ([false, true] ++ ([] : Word)) := by
    simpa [encRegs] using h
  exact (encRegs_aux l₁ l₂ [] [] h').1

lemma encRegs_length_le (l : List Word) (c : ℕ) (h : ∀ w ∈ l, w.length ≤ c) :
    (encRegs l).length ≤ 2 * l.length * (c + 1) + 2 := by
  have hflat : (l.flatMap dbl).length ≤ 2 * l.length * (c + 1) := by
    induction l with
    | nil => simp
    | cons w l ih =>
      have hw : w.length ≤ c := h w (by simp)
      have ih' := ih (fun v hv => h v (by simp [hv]))
      simp only [List.flatMap_cons, List.length_append, dbl_length, List.length_cons]
      have : 2 * (l.length + 1) * (c + 1) = 2 * l.length * (c + 1) + 2 * (c + 1) := by ring
      omega
  have : (encRegs l).length = (l.flatMap dbl).length + 2 := by
    simp [encRegs]
  omega

end CS

import Mathlib
import RequestProject.Savitch.Machines

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Bounded reachability in configuration graphs

Fix a nondeterministic machine `N` and an input `x`.  We study reachability in the
configuration graph of `N` on `x`, restricted to configurations of length at most `s`.

* `stepsTo N x k u v` : `v` is reached from `u` in exactly `k` steps;
* `ReachIn N x k u v` : `v` is reached from `u` in at most `k` steps;
* `R N x s d u v`     : the *Savitch predicate*, the doubling recursion which unfolds
  to "`v` is reachable from `u` in at most `2 ^ d` steps".

The two main results are `reach_bounded` (reachability implies reachability within
`#configurations` steps) and `reach_iff_R` (reachability is exactly `R` at depth `s+1`).
-/

namespace CS
namespace Savitch

/-! ### The list of all configurations of bounded length -/

/-- All bit strings of a given length. -/
def wordsOfLen : ℕ → List Word
  | 0 => [[]]
  | k + 1 => (wordsOfLen k).flatMap (fun w => [false :: w, true :: w])

lemma mem_wordsOfLen : ∀ (k : ℕ) (w : Word), w ∈ wordsOfLen k ↔ w.length = k := by
  intro k
  induction k with
  | zero => intro w; cases w <;> simp [wordsOfLen]
  | succ k ih =>
    intro w
    cases w with
    | nil => simp [wordsOfLen]
    | cons b w =>
      simp only [wordsOfLen, List.mem_flatMap, List.length_cons, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨v, hv, hmem⟩
        simp only [List.mem_cons] at hmem
        rcases hmem with h | h | h
        · rw [(List.cons.injEq _ _ _ _ ▸ h : b = false ∧ w = v).2]; exact (ih v).1 hv
        · rw [(List.cons.injEq _ _ _ _ ▸ h : b = true ∧ w = v).2]; exact (ih v).1 hv
        · exact absurd h (by simp)
      · intro hw
        exact ⟨w, (ih w).2 hw, by cases b <;> simp⟩

lemma wordsOfLen_length : ∀ k : ℕ, (wordsOfLen k).length = 2 ^ k := by
  intro k
  induction k with
  | zero => simp [wordsOfLen]
  | succ k ih =>
    simp only [wordsOfLen, List.length_flatMap, pow_succ]
    simp [ih]

/-- All configurations (bit strings) of length at most `s`. -/
def cands (s : ℕ) : List Word := (List.range (s + 1)).flatMap wordsOfLen

lemma mem_cands {s : ℕ} {w : Word} : w ∈ cands s ↔ w.length ≤ s := by
  simp only [cands, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨k, hk, hw⟩
    rw [(mem_wordsOfLen k w).1 hw]; omega
  · intro hw
    exact ⟨w.length, by omega, (mem_wordsOfLen _ _).2 rfl⟩

lemma cands_length_lt (s : ℕ) : (cands s).length < 2 ^ (s + 1) := by
  induction s with
  | zero => simp [cands, wordsOfLen]
  | succ s ih =>
    have h : cands (s + 1) = cands s ++ wordsOfLen (s + 1) := by
      simp [cands, List.range_succ]
    rw [h, List.length_append, wordsOfLen_length]
    have : 2 ^ (s + 1 + 1) = 2 ^ (s + 1) + 2 ^ (s + 1) := by ring
    omega

lemma cands_length_le (s : ℕ) : (cands s).length ≤ 2 ^ (s + 1) :=
  le_of_lt (cands_length_lt s)

lemma cands_pos (s : ℕ) : 0 < (cands s).length := by
  have : ([] : Word) ∈ cands s := mem_cands.2 (by simp)
  exact List.length_pos_of_mem this

lemma cands_getD_length_le (s i : ℕ) : ((cands s).getD i []).length ≤ s := by
  by_cases h : i < (cands s).length
  · have : (cands s).getD i [] ∈ cands s := by
      rw [List.getD_eq_getElem _ _ h]
      exact List.getElem_mem h
    exact mem_cands.1 this
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

/-! ### Bounded reachability -/

/-- `stepsTo N x k u v`: `v` is reached from `u` in exactly `k` steps. -/
def stepsTo (N : NDetMachine) (x : Word) : ℕ → Word → Word → Prop
  | 0, u, v => u = v
  | k + 1, u, v => ∃ m, stepsTo N x k u m ∧ N.stepOn x m v

/-- `ReachIn N x k u v`: `v` is reached from `u` in at most `k` steps. -/
def ReachIn (N : NDetMachine) (x : Word) (k : ℕ) (u v : Word) : Prop :=
  ∃ j ≤ k, stepsTo N x j u v

variable (N : NDetMachine) (x : Word)

lemma stepsTo_reach : ∀ (k : ℕ) (u v : Word), stepsTo N x k u v → N.Reach x u v := by
  intro k
  induction k with
  | zero =>
    intro u v h
    rw [show u = v from h]
    exact Relation.ReflTransGen.refl
  | succ k ih =>
    rintro u v ⟨m, hm, hmv⟩
    exact (ih u m hm).tail hmv

lemma reach_iff_stepsTo (u v : Word) : N.Reach x u v ↔ ∃ k, stepsTo N x k u v := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hbc ih => obtain ⟨k, hk⟩ := ih; exact ⟨k + 1, _, hk, hbc⟩
  · rintro ⟨k, hk⟩; exact stepsTo_reach N x k u v hk

lemma ReachIn_reach {k : ℕ} {u v : Word} (h : ReachIn N x k u v) : N.Reach x u v := by
  obtain ⟨j, -, hj⟩ := h
  exact stepsTo_reach N x j u v hj

lemma ReachIn_mono {k k' : ℕ} (h : k ≤ k') {u v : Word} (huv : ReachIn N x k u v) :
    ReachIn N x k' u v := by
  obtain ⟨j, hj, hs⟩ := huv
  exact ⟨j, by omega, hs⟩

lemma stepsTo_add : ∀ (a b : ℕ) (u v : Word), stepsTo N x (a + b) u v →
    ∃ m, stepsTo N x a u m ∧ stepsTo N x b m v := by
  intro a b
  induction b with
  | zero => intro u v h; exact ⟨v, h, rfl⟩
  | succ b ih =>
    rintro u v ⟨m, hm, hmv⟩
    obtain ⟨p, hp, hpm⟩ := ih u m hm
    exact ⟨p, hp, m, hpm, hmv⟩

lemma ReachIn_split (a b : ℕ) (u v : Word) (h : ReachIn N x (a + b) u v) :
    ∃ m, ReachIn N x a u m ∧ ReachIn N x b m v := by
  obtain ⟨j, hj, hs⟩ := h
  by_cases hja : j ≤ a
  · exact ⟨v, ⟨j, hja, hs⟩, ⟨0, by omega, rfl⟩⟩
  · have hsplit : j = a + (j - a) := by omega
    rw [hsplit] at hs
    obtain ⟨m, hm1, hm2⟩ := stepsTo_add N x a (j - a) u v hs
    exact ⟨m, ⟨a, le_rfl, hm1⟩, ⟨j - a, by omega, hm2⟩⟩

/-- **BFS bound.** If every reachable configuration has length at most `s`, then every
reachable configuration is reachable within `#(configurations of length ≤ s)` steps. -/
lemma reach_bounded (s : ℕ) (hsp : ∀ w, N.Reach x N.init w → w.length ≤ s) {v : Word}
    (hv : N.Reach x N.init v) : ReachIn N x ((cands s).length) N.init v := by
  classical
  set C : Finset Word := (cands s).toFinset with hC
  set B : ℕ → Finset Word := fun k => C.filter (fun w => ReachIn N x k N.init w) with hB
  have hBsub : ∀ k, B k ⊆ C := fun k => Finset.filter_subset _ _
  have hmem : ∀ (k : ℕ) (w : Word), w ∈ B k ↔ (w ∈ cands s ∧ ReachIn N x k N.init w) := by
    intro k w
    simp [hB, hC]
  have hmono : ∀ (k k' : ℕ), k ≤ k' → B k ⊆ B k' := by
    intro k k' hkk' w hw
    rw [hmem] at hw ⊢
    exact ⟨hw.1, ReachIn_mono N x hkk' hw.2⟩
  have hstep : ∀ k, B (k + 1) = B k → B (k + 2) = B (k + 1) := by
    intro k hk
    apply Finset.Subset.antisymm _ (hmono _ _ (by omega))
    intro w hw
    rw [hmem] at hw ⊢
    refine ⟨hw.1, ?_⟩
    obtain ⟨j, hj, hs⟩ := hw.2
    by_cases hjk : j ≤ k + 1
    · exact ⟨j, hjk, hs⟩
    · have hj2 : j = k + 2 := by omega
      subst hj2
      obtain ⟨m, hm, hmw⟩ := hs
      have hmreach : N.Reach x N.init m := stepsTo_reach N x (k + 1) _ _ hm
      have hmB : m ∈ B (k + 1) := by
        rw [hmem]
        exact ⟨mem_cands.2 (hsp m hmreach), ⟨k + 1, le_rfl, hm⟩⟩
      rw [hk, hmem] at hmB
      obtain ⟨j', hj', hs'⟩ := hmB.2
      exact ⟨j' + 1, by omega, m, hs', hmw⟩
  have hstab : ∀ k, B (k + 1) = B k → ∀ j, k ≤ j → B j = B k := by
    intro k hk j hj
    induction j with
    | zero =>
      have : k = 0 := by omega
      rw [this]
    | succ j ih =>
      rcases Nat.lt_or_ge k (j + 1) with hlt | hge
      · have hjk : k ≤ j := by omega
        have hBj : B j = B k := ih hjk
        -- from stabilisation at `k` we propagate one more step
        have key : ∀ i, k ≤ i → B (i + 1) = B i := by
          intro i hi
          induction i with
          | zero =>
            have : k = 0 := by omega
            rw [← this]; exact hk
          | succ i ih2 =>
            rcases Nat.lt_or_ge k (i + 1) with h1 | h2
            · exact hstep i (ih2 (by omega))
            · have : k = i + 1 := by omega
              rw [this] at hk; exact hk
        rw [key j hjk, hBj]
      · have : k = j + 1 := by omega
        rw [this]
  have hex : ∃ k ≤ C.card, B (k + 1) = B k := by
    by_contra hcon
    push_neg at hcon
    have hcard : ∀ k, k ≤ C.card + 1 → k ≤ (B k).card := by
      intro k
      induction k with
      | zero => intro _; omega
      | succ k ih =>
        intro hk
        have hk' : k ≤ C.card := by omega
        have hne : B (k + 1) ≠ B k := hcon k hk'
        have hss : B k ⊂ B (k + 1) :=
          lt_of_le_of_ne (hmono k (k + 1) (by omega)) (fun h => hne h.symm)
        have := Finset.card_lt_card hss
        have := ih (by omega)
        omega
    have h1 := hcard (C.card + 1) le_rfl
    have h2 : (B (C.card + 1)).card ≤ C.card := Finset.card_le_card (hBsub _)
    omega
  obtain ⟨k, hkC, hk⟩ := hex
  obtain ⟨n, hn⟩ := (reach_iff_stepsTo N x N.init v).1 hv
  have hvC : v ∈ cands s := mem_cands.2 (hsp v hv)
  have hvB : v ∈ B (max n k) := by
    rw [hmem]
    exact ⟨hvC, ⟨n, le_max_left _ _, hn⟩⟩
  rw [hstab k hk (max n k) (le_max_right _ _), hmem] at hvB
  have hCcard : C.card ≤ (cands s).length := List.toFinset_card_le _
  exact ReachIn_mono N x (le_trans hkC hCcard) hvB.2

/-! ### The Savitch predicate -/

/-- The Savitch doubling predicate: `R N x s d u v` says that `v` can be reached from `u`
in at most `2 ^ d` steps, using only intermediate configurations of length at most `s`. -/
def R (N : NDetMachine) (x : Word) (s : ℕ) : ℕ → Word → Word → Prop
  | 0, u, v => u = v ∨ N.stepOn x u v
  | d + 1, u, v => ∃ m ∈ cands s, R N x s d u m ∧ R N x s d m v

lemma R_sound (s : ℕ) : ∀ (d : ℕ) (u v : Word), R N x s d u v → N.Reach x u v := by
  intro d
  induction d with
  | zero =>
    intro u v h
    rcases h with h | h
    · rw [h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single h
  | succ d ih =>
    rintro u v ⟨m, -, h1, h2⟩
    exact (ih u m h1).trans (ih m v h2)

lemma R_complete (s : ℕ) (hsp : ∀ w, N.Reach x N.init w → w.length ≤ s) :
    ∀ (d : ℕ) (u v : Word), N.Reach x N.init u → ReachIn N x (2 ^ d) u v → R N x s d u v := by
  intro d
  induction d with
  | zero =>
    intro u v _ h
    obtain ⟨j, hj, hs⟩ := h
    interval_cases j
    · exact Or.inl hs
    · obtain ⟨m, hm, hmv⟩ := hs
      rw [show u = m from hm]
      exact Or.inr hmv
  | succ d ih =>
    intro u v hu h
    have hsplit : (2 : ℕ) ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
    rw [hsplit] at h
    obtain ⟨m, h1, h2⟩ := ReachIn_split N x _ _ u v h
    have hm : N.Reach x N.init m := hu.trans (ReachIn_reach N x h1)
    exact ⟨m, mem_cands.2 (hsp m hm), ih u m hu h1, ih m v hm h2⟩

/-- Reachability from the initial configuration is exactly the Savitch predicate at
depth `s + 1`, for machines all of whose reachable configurations have length ≤ `s`. -/
lemma reach_iff_R (s : ℕ) (hsp : ∀ w, N.Reach x N.init w → w.length ≤ s) (v : Word) :
    N.Reach x N.init v ↔ R N x s (s + 1) N.init v := by
  constructor
  · intro h
    have h1 : ReachIn N x ((cands s).length) N.init v := reach_bounded N x s hsp h
    have h2 : ReachIn N x (2 ^ (s + 1)) N.init v :=
      ReachIn_mono N x (cands_length_le s) h1
    exact R_complete N x s hsp (s + 1) N.init v Relation.ReflTransGen.refl h2
  · intro h
    exact R_sound N x s (s + 1) N.init v h

end Savitch
end CS

