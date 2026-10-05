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

/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## An oracle machine model

This file develops a small but genuine model of *oracle computation*: a structured
imperative language over string-valued registers, with a cost model in which every
executed instruction costs `1 + (length of the value it writes)`.  Machines are
finite syntactic objects, hence the set of machines is countable (this is what makes
diagonalisation possible), and the cost model is polynomially equivalent to the usual
multitape Turing machine model.
-/

set_option autoImplicit false

namespace CS.BGS

/-- Binary strings. -/
abbrev Str := List Bool

/-- An oracle is a set of strings, presented by its characteristic function. -/
abbrev Oracle := Str → Bool

/-- A store assigns a string to each register index. -/
abbrev Store := ℕ → Str

/-- Branching conditions. -/
inductive Cond where
  | isNil : ℕ → Cond
  | headTrue : ℕ → Cond
  | eq : ℕ → ℕ → Cond

/-- Evaluation of a branching condition in a store. -/
def Cond.ev : Cond → Store → Bool
  | .isNil i, st => (st i).isEmpty
  | .headTrue i, st => (st i).head? == some true
  | .eq i j, st => (st i) == (st j)

/-- Programs.  `lit i s` writes the constant `s`; `cat i j k` writes `v j ++ v k`;
`rep i j k` writes the all-ones string of length `|v j| * |v k|`; `tl i j` writes the
tail of `v j`; `cns i b j` writes `b :: v j`; `qry i j` writes `[true]` or `[]`
according to whether the oracle contains `v j`. -/
inductive Stmt where
  | skip : Stmt
  | seq : Stmt → Stmt → Stmt
  | ifte : Cond → Stmt → Stmt → Stmt
  | wh : Cond → Stmt → Stmt
  | lit : ℕ → Str → Stmt
  | cat : ℕ → ℕ → ℕ → Stmt
  | rep : ℕ → ℕ → ℕ → Stmt
  | tl : ℕ → ℕ → Stmt
  | cns : ℕ → Bool → ℕ → Stmt
  | qry : ℕ → ℕ → Stmt

/-- A configuration: a control stack, a store, the cost accumulated so far, and the
list of strings queried so far (most recent first). -/
structure Cfg where
  stk : List Stmt
  st : Store
  cost : ℕ
  log : List Str

/-- Register update. -/
def upd (st : Store) (i : ℕ) (v : Str) : Store := fun j => if j = i then v else st j

@[simp] theorem upd_self (st : Store) (i : ℕ) (v : Str) : upd st i v i = v := by
  simp [upd]

theorem upd_other (st : Store) (i j : ℕ) (v : Str) (h : j ≠ i) : upd st i v j = st j := by
  simp [upd, h]

/-- One computation step. -/
def step (O : Oracle) (c : Cfg) : Cfg :=
  match c.stk with
  | [] => c
  | s :: rest =>
    match s with
    | .skip => ⟨rest, c.st, c.cost + 1, c.log⟩
    | .seq a b => ⟨a :: b :: rest, c.st, c.cost + 1, c.log⟩
    | .ifte cd a b => ⟨(if cd.ev c.st then a else b) :: rest, c.st, c.cost + 1, c.log⟩
    | .wh cd a =>
        if cd.ev c.st then ⟨a :: .wh cd a :: rest, c.st, c.cost + 1, c.log⟩
        else ⟨rest, c.st, c.cost + 1, c.log⟩
    | .lit i v => ⟨rest, upd c.st i v, c.cost + 1 + v.length, c.log⟩
    | .cat i j k => ⟨rest, upd c.st i (c.st j ++ c.st k),
        c.cost + 1 + (c.st j ++ c.st k).length, c.log⟩
    | .rep i j k =>
        ⟨rest, upd c.st i (List.replicate ((c.st j).length * (c.st k).length) true),
          c.cost + 1 + (c.st j).length * (c.st k).length, c.log⟩
    | .tl i j => ⟨rest, upd c.st i (c.st j).tail, c.cost + 1 + (c.st j).tail.length, c.log⟩
    | .cns i b j => ⟨rest, upd c.st i (b :: c.st j), c.cost + 1 + (b :: c.st j).length, c.log⟩
    | .qry i j => ⟨rest, upd c.st i (if O (c.st j) then [true] else []),
        c.cost + 1, c.st j :: c.log⟩

section StepEq
variable (O : Oracle) (st : Store) (cst : ℕ) (lg : List Str) (rest : List Stmt)

@[simp] theorem step_nil' : step O ⟨[], st, cst, lg⟩ = ⟨[], st, cst, lg⟩ := rfl

@[simp] theorem step_skip : step O ⟨.skip :: rest, st, cst, lg⟩ = ⟨rest, st, cst + 1, lg⟩ := rfl

@[simp] theorem step_seq (a b : Stmt) :
    step O ⟨.seq a b :: rest, st, cst, lg⟩ = ⟨a :: b :: rest, st, cst + 1, lg⟩ := rfl

@[simp] theorem step_ifte (cd : Cond) (a b : Stmt) :
    step O ⟨.ifte cd a b :: rest, st, cst, lg⟩ =
      ⟨(if cd.ev st then a else b) :: rest, st, cst + 1, lg⟩ := rfl

@[simp] theorem step_wh (cd : Cond) (a : Stmt) :
    step O ⟨.wh cd a :: rest, st, cst, lg⟩ =
      (if cd.ev st then ⟨a :: .wh cd a :: rest, st, cst + 1, lg⟩
        else ⟨rest, st, cst + 1, lg⟩) := rfl

@[simp] theorem step_lit (i : ℕ) (v : Str) :
    step O ⟨.lit i v :: rest, st, cst, lg⟩ = ⟨rest, upd st i v, cst + 1 + v.length, lg⟩ := rfl

@[simp] theorem step_cat (i j k : ℕ) :
    step O ⟨.cat i j k :: rest, st, cst, lg⟩ =
      ⟨rest, upd st i (st j ++ st k), cst + 1 + (st j ++ st k).length, lg⟩ := rfl

@[simp] theorem step_rep (i j k : ℕ) :
    step O ⟨.rep i j k :: rest, st, cst, lg⟩ =
      ⟨rest, upd st i (List.replicate ((st j).length * (st k).length) true),
        cst + 1 + (st j).length * (st k).length, lg⟩ := rfl

@[simp] theorem step_tl (i j : ℕ) :
    step O ⟨.tl i j :: rest, st, cst, lg⟩ =
      ⟨rest, upd st i (st j).tail, cst + 1 + (st j).tail.length, lg⟩ := rfl

@[simp] theorem step_cns (i : ℕ) (b : Bool) (j : ℕ) :
    step O ⟨.cns i b j :: rest, st, cst, lg⟩ =
      ⟨rest, upd st i (b :: st j), cst + 1 + (b :: st j).length, lg⟩ := rfl

@[simp] theorem step_qry (i j : ℕ) :
    step O ⟨.qry i j :: rest, st, cst, lg⟩ =
      ⟨rest, upd st i (if O (st j) then [true] else []), cst + 1, st j :: lg⟩ := rfl

end StepEq

theorem step_of_stk_nil (O : Oracle) (c : Cfg) (h : c.stk = []) : step O c = c := by
  obtain ⟨stk, st, cst, lg⟩ := c
  cases stk with
  | nil => simp
  | cons a r => simp at h

theorem step_stk_nil_iterate (O : Oracle) (c : Cfg) (h : c.stk = []) (n : ℕ) :
    (step O)^[n] c = c := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, step_of_stk_nil O c h]

/-- The initial store: input in register `0`, witness in register `1`. -/
def initSt (x w : Str) : Store := fun i => if i = 0 then x else if i = 1 then w else []

/-- The initial configuration. -/
def initCfg (s : Stmt) (x w : Str) : Cfg := ⟨[s], initSt x w, 0, []⟩

/-- The configuration after `n` steps. -/
def run (O : Oracle) (s : Stmt) (x w : Str) (n : ℕ) : Cfg := (step O)^[n] (initCfg s x w)

/-! ### Basic monotonicity facts -/

theorem cost_step_le (O : Oracle) (c : Cfg) : c.cost ≤ (step O c).cost := by
  obtain ⟨stk, st, cst, lg⟩ := c
  cases stk with
  | nil => simp
  | cons a r =>
    cases a <;> simp <;> first | omega | (split <;> simp)

theorem cost_step_lt (O : Oracle) (c : Cfg) (h : c.stk ≠ []) : c.cost < (step O c).cost := by
  obtain ⟨stk, st, cst, lg⟩ := c
  cases stk with
  | nil => simp at h
  | cons a r =>
    cases a <;> simp <;> first | omega | (split <;> simp)

theorem cost_mono (O : Oracle) (c : Cfg) {m n : ℕ} (h : m ≤ n) :
    ((step O)^[m] c).cost ≤ ((step O)^[n] c).cost := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => simp
  | succ d ih =>
    have he : (step O)^[m + (d+1)] c = step O ((step O)^[m+d] c) := by
      rw [show m + (d+1) = (m+d) + 1 by ring, Function.iterate_succ_apply']
    rw [he]
    exact le_trans ih (cost_step_le O _)

/-- The number of steps performed is at most the cost accumulated. -/
theorem steps_le_cost (O : Oracle) (c : Cfg) (n : ℕ)
    (h : ∀ m < n, ((step O)^[m] c).stk ≠ []) : n ≤ ((step O)^[n] c).cost := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : n ≤ ((step O)^[n] c).cost := ih (fun m hm => h m (by omega))
    have h2 : ((step O)^[n] c).cost < ((step O)^[n+1] c).cost := by
      rw [Function.iterate_succ_apply']
      exact cost_step_lt O _ (h n (by omega))
    omega

/-! ### The log grows by prepending -/

theorem log_step_suffix (O : Oracle) (c : Cfg) : c.log <:+ (step O c).log := by
  obtain ⟨stk, st, cst, lg⟩ := c
  cases stk with
  | nil => simp
  | cons a r =>
    cases a <;> simp
    · split <;> simp

theorem log_suffix_mono (O : Oracle) (c : Cfg) {m n : ℕ} (h : m ≤ n) :
    ((step O)^[m] c).log <:+ ((step O)^[n] c).log := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => simp
  | succ d ih =>
    have he : (step O)^[m + (d+1)] c = step O ((step O)^[m+d] c) := by
      rw [show m + (d+1) = (m+d) + 1 by ring, Function.iterate_succ_apply']
    rw [he]
    exact List.IsSuffix.trans ih (log_step_suffix O _)

theorem log_mem_mono (O : Oracle) (c : Cfg) {m n : ℕ} (h : m ≤ n) {s : Str}
    (hs : s ∈ ((step O)^[m] c).log) : s ∈ ((step O)^[n] c).log :=
  (log_suffix_mono O c h).mem hs

/-! ### Locality: computations depend on the oracle only through queried strings -/

theorem locality (O₁ O₂ : Oracle) (c : Cfg) (n : ℕ)
    (h : ∀ s ∈ ((step O₁)^[n] c).log, O₁ s = O₂ s) :
    (step O₁)^[n] c = (step O₂)^[n] c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsuf : ((step O₁)^[n] c).log <:+ ((step O₁)^[n+1] c).log :=
      log_suffix_mono O₁ c (Nat.le_succ n)
    have ih' : (step O₁)^[n] c = (step O₂)^[n] c :=
      ih (fun s hs => h s (hsuf.mem hs))
    have h' : ∀ s ∈ (step O₁ ((step O₁)^[n] c)).log, O₁ s = O₂ s := by
      intro s hs
      exact h s (by rw [Function.iterate_succ_apply']; exact hs)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih']
    revert h'
    generalize (step O₁)^[n] c = d
    obtain ⟨stk, st, cst, lg⟩ := d
    intro h'
    cases stk with
    | nil => simp
    | cons a r =>
      cases a with
      | qry i j =>
        have hq : O₁ (st j) = O₂ (st j) := by
          apply h'
          simp
        simp [hq]
      | skip => simp
      | seq a b => simp
      | ifte cd a b => simp
      | wh cd a => simp
      | lit i v => simp
      | cat i j k => simp
      | rep i j k => simp
      | tl i j => simp
      | cns i b j => simp

/-! ### Length invariant -/

theorem upd_len_bound {st : Store} {m cst c' : ℕ} (hall : ∀ j, (st j).length ≤ m + cst)
    (k : ℕ) (v : Str) (hv : v.length ≤ m + c') (hc : cst ≤ c') (i : ℕ) :
    (upd st k v i).length ≤ m + c' := by
  by_cases h : i = k
  · subst h; rw [upd_self]; exact hv
  · rw [upd_other _ _ _ _ h]; have := hall i; omega

theorem length_invariant (O : Oracle) (c : Cfg) (m : ℕ)
    (h0 : ∀ i, (c.st i).length ≤ m + c.cost) (n : ℕ) :
    ∀ i, (((step O)^[n] c).st i).length ≤ m + ((step O)^[n] c).cost := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    revert ih
    generalize (step O)^[n] c = d
    obtain ⟨stk, st, cst, lg⟩ := d
    intro ih
    simp only [] at ih ⊢
    cases stk with
    | nil => simpa using ih
    | cons a r =>
      cases a with
      | skip => intro i; simpa using le_trans (ih i) (by omega)
      | seq a b => intro i; simpa using le_trans (ih i) (by omega)
      | ifte cd a b => intro i; simpa using le_trans (ih i) (by omega)
      | wh cd a =>
        intro i
        by_cases hc : cd.ev st <;> simp [hc] <;> exact le_trans (ih i) (by omega)
      | lit k v =>
        intro i; simp only [step_lit]
        exact upd_len_bound ih k v (by omega) (by omega) i
      | cat k j l =>
        intro i; simp only [step_cat]
        exact upd_len_bound ih k _ (by omega) (by omega) i
      | rep k j l =>
        intro i; simp only [step_rep]
        exact upd_len_bound ih k _ (by simp; omega) (by omega) i
      | tl k j =>
        intro i; simp only [step_tl]
        exact upd_len_bound ih k _ (by omega) (by omega) i
      | cns k b j =>
        intro i; simp only [step_cns]
        exact upd_len_bound ih k _ (by omega) (by omega) i
      | qry k j =>
        intro i; simp only [step_qry]
        refine upd_len_bound ih k _ ?_ (by omega) i
        have : ((if O (st j) then [true] else []) : Str).length ≤ 1 := by
          split <;> simp
        omega

/-- Every queried string is short: at most the initial maximal length plus the cost. -/
theorem query_length_bound (O : Oracle) (c : Cfg) (m : ℕ)
    (h0 : ∀ i, (c.st i).length ≤ m + c.cost) (hlog : ∀ s ∈ c.log, s.length ≤ m + c.cost)
    (n : ℕ) : ∀ s ∈ ((step O)^[n] c).log, s.length ≤ m + ((step O)^[n] c).cost := by
  induction n with
  | zero => simpa using hlog
  | succ n ih =>
    have hst : ∀ i, (((step O)^[n] c).st i).length ≤ m + ((step O)^[n] c).cost :=
      length_invariant O c m h0 n
    rw [Function.iterate_succ_apply']
    revert ih hst
    generalize (step O)^[n] c = d
    obtain ⟨stk, st, cst, lg⟩ := d
    intro ih hst
    simp only [] at ih hst ⊢
    cases stk with
    | nil => simpa using ih
    | cons a r =>
      cases a with
      | skip => intro s hs; simp at hs ⊢; exact le_trans (ih s hs) (by omega)
      | seq a b => intro s hs; simp at hs ⊢; exact le_trans (ih s hs) (by omega)
      | ifte cd a b => intro s hs; simp at hs ⊢; exact le_trans (ih s hs) (by omega)
      | wh cd a =>
        intro s hs
        by_cases hc : cd.ev st <;> simp [hc] at hs ⊢ <;> exact le_trans (ih s hs) (by omega)
      | lit k v => intro s hs; simp at hs ⊢; exact le_trans (ih s hs) (by omega)
      | cat k j l => intro s hs; simp at hs ⊢; exact le_trans (ih s hs) (by omega)
      | rep k j l => intro s hs; simp at hs ⊢; exact le_trans (ih s hs) (by omega)
      | tl k j => intro s hs; simp at hs ⊢; exact le_trans (ih s hs) (by omega)
      | cns k b j => intro s hs; simp at hs ⊢; exact le_trans (ih s hs) (by omega)
      | qry k j =>
        intro s hs
        simp only [step_qry, List.mem_cons] at hs ⊢
        rcases hs with h | h
        · subst h; exact le_trans (hst j) (by omega)
        · exact le_trans (ih s h) (by omega)

/-! ### The number of queries is at most the number of steps -/

theorem log_step_length (O : Oracle) (c : Cfg) : (step O c).log.length ≤ c.log.length + 1 := by
  obtain ⟨stk, st, cst, lg⟩ := c
  cases stk with
  | nil => simp
  | cons a r =>
    cases a <;> simp <;> first | omega | (split <;> simp)

theorem log_length_le (O : Oracle) (c : Cfg) (n : ℕ) :
    ((step O)^[n] c).log.length ≤ c.log.length + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact le_trans (log_step_length O _) (by omega)

end CS.BGS

/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.BGS.Machine

/-!
## Big-step semantics, determinism, and countability of programs
-/

set_option autoImplicit false

namespace CS.BGS

/-! ### Countability of the set of programs -/

/-- Codes for branching conditions. -/
def Cond.code : Cond → ℕ
  | .isNil i => Nat.pair 0 i
  | .headTrue i => Nat.pair 1 i
  | .eq i j => Nat.pair 2 (Nat.pair i j)

theorem Cond.code_inj : Function.Injective Cond.code := by
  intro a b h
  cases a <;> cases b <;> simp_all [Cond.code, Nat.pair_eq_pair]

/-- Codes for programs. -/
def Stmt.code : Stmt → ℕ
  | .skip => Nat.pair 0 0
  | .seq a b => Nat.pair 1 (Nat.pair a.code b.code)
  | .ifte c a b => Nat.pair 2 (Nat.pair c.code (Nat.pair a.code b.code))
  | .wh c a => Nat.pair 3 (Nat.pair c.code a.code)
  | .lit i s => Nat.pair 4 (Nat.pair i (Encodable.encode s))
  | .cat i j k => Nat.pair 5 (Nat.pair i (Nat.pair j k))
  | .rep i j k => Nat.pair 6 (Nat.pair i (Nat.pair j k))
  | .tl i j => Nat.pair 7 (Nat.pair i j)
  | .cns i b j => Nat.pair 8 (Nat.pair i (Nat.pair (if b then 1 else 0) j))
  | .qry i j => Nat.pair 9 (Nat.pair i j)

theorem Stmt.code_inj : Function.Injective Stmt.code := by
  intro a
  induction a with
  | skip => intro b h; cases b <;> simp [Stmt.code, Nat.pair_eq_pair] at h ⊢
  | seq x y ihx ihy =>
    intro b h
    cases b <;> simp [Stmt.code, Nat.pair_eq_pair] at h
    rw [ihx h.1, ihy h.2]
  | ifte c x y ihx ihy =>
    intro b h
    cases b <;> simp [Stmt.code, Nat.pair_eq_pair] at h
    rw [Cond.code_inj h.1, ihx h.2.1, ihy h.2.2]
  | wh c x ihx =>
    intro b h
    cases b <;> simp [Stmt.code, Nat.pair_eq_pair] at h
    rw [Cond.code_inj h.1, ihx h.2]
  | lit i s =>
    intro b h
    cases b <;> simp [Stmt.code, Nat.pair_eq_pair] at h
    simp_all
  | cat i j k => intro b h; cases b <;> simp [Stmt.code, Nat.pair_eq_pair] at h ⊢; tauto
  | rep i j k => intro b h; cases b <;> simp [Stmt.code, Nat.pair_eq_pair] at h ⊢; tauto
  | tl i j => intro b h; cases b <;> simp [Stmt.code, Nat.pair_eq_pair] at h ⊢; tauto
  | cns i b j =>
    intro b' h
    cases b' <;> simp [Stmt.code, Nat.pair_eq_pair] at h ⊢
    refine ⟨h.1, ?_, h.2.2⟩
    rcases b with _ | _ <;> simp_all
  | qry i j => intro b h; cases b <;> simp [Stmt.code, Nat.pair_eq_pair] at h ⊢; tauto

instance : Countable Stmt := Stmt.code_inj.countable

instance : Inhabited Stmt := ⟨.skip⟩

/-! ### Halting is stable -/

theorem halt_stable (O : Oracle) (c : Cfg) {n : ℕ} (h : ((step O)^[n] c).stk = [])
    {m : ℕ} (hm : n ≤ m) : (step O)^[m] c = (step O)^[n] c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact step_stk_nil_iterate O _ h d

/-! ### Shifting a configuration (framing) -/

/-- Push extra work `rest` under the stack, add `d` to the cost and `lg0` under the log. -/
def shift (rest : List Stmt) (d : ℕ) (lg0 : List Str) (c : Cfg) : Cfg :=
  ⟨c.stk ++ rest, c.st, c.cost + d, c.log ++ lg0⟩

theorem step_shift (O : Oracle) (c : Cfg) (h : c.stk ≠ []) (rest : List Stmt) (d : ℕ)
    (lg0 : List Str) : step O (shift rest d lg0 c) = shift rest d lg0 (step O c) := by
  obtain ⟨stk, st, cst, lg⟩ := c
  cases stk with
  | nil => simp at h
  | cons a r =>
    cases a <;> simp [shift] <;> first | omega | (split <;> simp <;> omega)

theorem iterate_shift (O : Oracle) (c : Cfg) (n : ℕ)
    (h : ∀ m < n, ((step O)^[m] c).stk ≠ []) (rest : List Stmt) (d : ℕ) (lg0 : List Str) :
    (step O)^[n] (shift rest d lg0 c) = shift rest d lg0 ((step O)^[n] c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun m hm => h m (by omega)), step_shift O _ (h n (by omega))]

/-! ### The big-step relation -/

/-- `Exec O s st st' c lg`: run from store `st` with program `s`; it halts with final
store `st'`, total cost `c`, and query log `lg`. -/
def Exec (O : Oracle) (s : Stmt) (st st' : Store) (c : ℕ) (lg : List Str) : Prop :=
  ∃ n, (step O)^[n] ⟨[s], st, 0, []⟩ = ⟨[], st', c, lg⟩

/-- Any halting run reaches the `Exec` result. -/
theorem exec_run_eq {O : Oracle} {s : Stmt} {st st' : Store} {c : ℕ} {lg : List Str}
    (h : Exec O s st st' c lg) {n : ℕ} (hn : ((step O)^[n] (⟨[s], st, 0, []⟩ : Cfg)).stk = []) :
    (step O)^[n] (⟨[s], st, 0, []⟩ : Cfg) = ⟨[], st', c, lg⟩ := by
  obtain ⟨n₁, h1⟩ := h
  have e1 : (step O)^[max n₁ n] (⟨[s], st, 0, []⟩ : Cfg) = ⟨[], st', c, lg⟩ := by
    rw [halt_stable O _ (by rw [h1]) (le_max_left n₁ n), h1]
  rw [← e1, halt_stable O _ hn (le_max_right n₁ n)]

theorem exec_unique {O : Oracle} {s : Stmt} {st st₁ st₂ : Store} {c₁ c₂ : ℕ}
    {lg₁ lg₂ : List Str} (h1 : Exec O s st st₁ c₁ lg₁) (h2 : Exec O s st st₂ c₂ lg₂) :
    st₁ = st₂ ∧ c₁ = c₂ ∧ lg₁ = lg₂ := by
  obtain ⟨n₂, h2'⟩ := h2
  have := exec_run_eq h1 (n := n₂) (by rw [h2'])
  rw [h2'] at this
  simp at this
  exact ⟨this.1.symm, this.2.1.symm, this.2.2.symm⟩

/-- The execution can be taken with the least halting time. -/
theorem exec_min {O : Oracle} {s : Stmt} {st st' : Store} {c : ℕ} {lg : List Str}
    (h : Exec O s st st' c lg) :
    ∃ n, (step O)^[n] (⟨[s], st, 0, []⟩ : Cfg) = ⟨[], st', c, lg⟩ ∧
      ∀ m < n, ((step O)^[m] (⟨[s], st, 0, []⟩ : Cfg)).stk ≠ [] := by
  classical
  obtain ⟨n, hn⟩ := h
  have hP : ∃ k, ((step O)^[k] (⟨[s], st, 0, []⟩ : Cfg)).stk = [] := ⟨n, by rw [hn]⟩
  refine ⟨Nat.find hP, exec_run_eq ⟨n, hn⟩ (Nat.find_spec hP), ?_⟩
  intro m hm hc
  exact Nat.find_min hP hm hc

/-! ### Big-step rules -/

theorem exec_skip (O : Oracle) (st : Store) : Exec O .skip st st 1 [] := ⟨1, by simp⟩

theorem exec_lit (O : Oracle) (st : Store) (i : ℕ) (v : Str) :
    Exec O (.lit i v) st (upd st i v) (1 + v.length) [] :=
  ⟨1, by simp⟩

theorem exec_cat (O : Oracle) (st : Store) (i j k : ℕ) :
    Exec O (.cat i j k) st (upd st i (st j ++ st k)) (1 + (st j ++ st k).length) [] :=
  ⟨1, by simp⟩

theorem exec_rep (O : Oracle) (st : Store) (i j k : ℕ) :
    Exec O (.rep i j k) st (upd st i (List.replicate ((st j).length * (st k).length) true))
      (1 + (st j).length * (st k).length) [] :=
  ⟨1, by simp⟩

theorem exec_tl (O : Oracle) (st : Store) (i j : ℕ) :
    Exec O (.tl i j) st (upd st i (st j).tail) (1 + (st j).tail.length) [] :=
  ⟨1, by simp⟩

theorem exec_cns (O : Oracle) (st : Store) (i : ℕ) (b : Bool) (j : ℕ) :
    Exec O (.cns i b j) st (upd st i (b :: st j)) (1 + (b :: st j).length) [] :=
  ⟨1, by simp⟩

theorem exec_qry (O : Oracle) (st : Store) (i j : ℕ) :
    Exec O (.qry i j) st (upd st i (if O (st j) then [true] else [])) 1 [st j] := ⟨1, by simp⟩

theorem exec_ifte {O : Oracle} {cd : Cond} {a b : Stmt} {st st' : Store} {c : ℕ}
    {lg : List Str} (h : Exec O (if cd.ev st then a else b) st st' c lg) :
    Exec O (.ifte cd a b) st st' (c + 1) lg := by
  obtain ⟨n, hn, hne⟩ := exec_min h
  refine ⟨n + 1, ?_⟩
  rw [Function.iterate_succ_apply]
  have hstep : step O (⟨[Stmt.ifte cd a b], st, 0, []⟩ : Cfg)
      = ⟨[if cd.ev st then a else b], st, 1, []⟩ := by simp
  rw [hstep, show (⟨[if cd.ev st then a else b], st, 1, []⟩ : Cfg)
      = shift [] 1 [] ⟨[if cd.ev st then a else b], st, 0, []⟩ from by simp [shift],
    iterate_shift O _ n hne [] 1 [], hn]
  simp [shift]

theorem exec_seq {O : Oracle} {a b : Stmt} {st st₁ st₂ : Store} {c₁ c₂ : ℕ}
    {lg₁ lg₂ : List Str} (h1 : Exec O a st st₁ c₁ lg₁) (h2 : Exec O b st₁ st₂ c₂ lg₂) :
    Exec O (.seq a b) st st₂ (c₁ + c₂ + 1) (lg₂ ++ lg₁) := by
  obtain ⟨n₁, hn₁, hne₁⟩ := exec_min h1
  obtain ⟨n₂, hn₂, hne₂⟩ := exec_min h2
  refine ⟨n₂ + (n₁ + 1), ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_add_apply]
  have hstep : (step O)^[1] (⟨[Stmt.seq a b], st, 0, []⟩ : Cfg) = ⟨[a, b], st, 1, []⟩ := by simp
  rw [hstep, show (⟨[a, b], st, 1, []⟩ : Cfg) = shift [b] 1 [] ⟨[a], st, 0, []⟩ from by simp [shift],
    iterate_shift O _ n₁ hne₁ [b] 1 [], hn₁]
  simp only [shift, List.nil_append, List.append_nil]
  rw [show (⟨[b], st₁, c₁ + 1, lg₁⟩ : Cfg) = shift [] (c₁ + 1) lg₁ ⟨[b], st₁, 0, []⟩ from by
    simp [shift], iterate_shift O _ n₂ hne₂ [] (c₁ + 1) lg₁, hn₂]
  simp only [shift, List.append_nil, Cfg.mk.injEq]
  exact ⟨trivial, trivial, by omega, trivial⟩

theorem exec_wh_false {O : Oracle} {cd : Cond} {a : Stmt} {st : Store}
    (h : cd.ev st = false) : Exec O (.wh cd a) st st 1 [] := ⟨1, by simp [h]⟩

theorem exec_wh_true {O : Oracle} {cd : Cond} {a : Stmt} {st st₁ st₂ : Store} {c₁ c₂ : ℕ}
    {lg₁ lg₂ : List Str} (h : cd.ev st = true) (h1 : Exec O a st st₁ c₁ lg₁)
    (h2 : Exec O (.wh cd a) st₁ st₂ c₂ lg₂) :
    Exec O (.wh cd a) st st₂ (c₁ + c₂ + 1) (lg₂ ++ lg₁) := by
  obtain ⟨n₁, hn₁, hne₁⟩ := exec_min h1
  obtain ⟨n₂, hn₂, hne₂⟩ := exec_min h2
  refine ⟨n₂ + (n₁ + 1), ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_add_apply]
  have hstep : (step O)^[1] (⟨[Stmt.wh cd a], st, 0, []⟩ : Cfg)
      = ⟨[a, Stmt.wh cd a], st, 1, []⟩ := by simp [h]
  rw [hstep, show (⟨[a, Stmt.wh cd a], st, 1, []⟩ : Cfg)
      = shift [Stmt.wh cd a] 1 [] ⟨[a], st, 0, []⟩ from by simp [shift],
    iterate_shift O _ n₁ hne₁ _ 1 [], hn₁]
  simp only [shift, List.nil_append, List.append_nil]
  rw [show (⟨[Stmt.wh cd a], st₁, c₁ + 1, lg₁⟩ : Cfg)
      = shift [] (c₁ + 1) lg₁ ⟨[Stmt.wh cd a], st₁, 0, []⟩ from by simp [shift],
    iterate_shift O _ n₂ hne₂ [] (c₁ + 1) lg₁, hn₂]
  simp only [shift, List.append_nil, Cfg.mk.injEq]
  exact ⟨trivial, trivial, by omega, trivial⟩

end CS.BGS

/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.BGS.Exec

/-!
## The relativised classes `P^O` and `N P^O`
-/

set_option autoImplicit false

namespace CS.BGS

open Filter Asymptotics

/-- The polynomial time bounds we quantify over: `tb k n = (n+2)^k`.
Every polynomial is dominated by one of these, and each of these is a polynomial. -/
def tb (k n : ℕ) : ℕ := (n + 2) ^ k

theorem tb_pos (k n : ℕ) : 0 < tb k n := pow_pos (by omega) k

theorem tb_le_tb {k k' : ℕ} (h : k ≤ k') (n : ℕ) : tb k n ≤ tb k' n :=
  Nat.pow_le_pow_right (by omega) h

theorem tb_add_two (k n : ℕ) : tb k n + 2 ≤ tb (k + 2) n := by
  have h1 : tb (k + 2) n = (n + 2) ^ 2 * tb k n := by
    unfold tb; rw [← pow_add]; ring_nf
  have hsq : (n + 2) ^ 2 = n * n + 4 * n + 4 := by ring
  have h2 : 4 ≤ (n + 2) ^ 2 := by omega
  have h3 : 1 ≤ tb k n := tb_pos k n
  calc tb k n + 2 ≤ 4 * tb k n := by omega
    _ ≤ (n + 2) ^ 2 * tb k n := Nat.mul_le_mul_right _ h2
    _ = tb (k + 2) n := h1.symm

/-- `Accepts O s x w t`: with oracle `O`, the program `s` on input `x` and witness `w`
halts within cost `t` and leaves `[true]` in register `0`. -/
def Accepts (O : Oracle) (s : Stmt) (x w : Str) (t : ℕ) : Prop :=
  ∃ st c lg, Exec O s (initSt x w) st c lg ∧ c ≤ t ∧ st 0 = [true]

theorem Accepts.mono {O : Oracle} {s : Stmt} {x w : Str} {t t' : ℕ} (h : Accepts O s x w t)
    (ht : t ≤ t') : Accepts O s x w t' := by
  obtain ⟨st, c, lg, hex, hc, ha⟩ := h
  exact ⟨st, c, lg, hex, le_trans hc ht, ha⟩

/-- `Decides O s k L`: with oracle `O`, the program `s` decides the language `L`
within cost `tb k |x|` on every input `x`. -/
def Decides (O : Oracle) (s : Stmt) (k : ℕ) (L : Set Str) : Prop :=
  ∀ x : Str, ∃ st c lg, Exec O s (initSt x []) st c lg ∧ c ≤ tb k x.length ∧
    (st 0 = [true] ↔ x ∈ L)

/-- The class `P^O`. -/
def PClass (O : Oracle) : Set (Set Str) := {L | ∃ s k, Decides O s k L}

/-- The class `NP^O`, defined through polynomial-time verifiers. -/
def NPClass (O : Oracle) : Set (Set Str) :=
  {L | ∃ s k, ∀ x : Str, x ∈ L ↔
    ∃ w : Str, w.length ≤ tb k x.length ∧ Accepts O s x w (tb k x.length)}

/-! ### Basic facts about the initial store -/

theorem initSt_len (x w : Str) (i : ℕ) : (initSt x w i).length ≤ max x.length w.length := by
  unfold initSt
  by_cases h0 : i = 0
  · simp [h0]
  · by_cases h1 : i = 1 <;> simp [h0, h1]

/-! ### Transfer of computations between oracles -/

theorem exec_congr {O₁ O₂ : Oracle} {s : Stmt} {st st' : Store} {c : ℕ} {lg : List Str}
    (h : Exec O₁ s st st' c lg) (hag : ∀ y ∈ lg, O₁ y = O₂ y) : Exec O₂ s st st' c lg := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [← locality O₁ O₂ _ n (by rw [hn]; exact hag), hn]

/-- Queried strings are short. -/
theorem exec_query_len {O : Oracle} {s : Stmt} {x w : Str} {st' : Store} {c : ℕ}
    {lg : List Str} (h : Exec O s (initSt x w) st' c lg) :
    ∀ y ∈ lg, y.length ≤ max x.length w.length + c := by
  obtain ⟨n, hn⟩ := h
  have := query_length_bound O (initCfg s x w) (max x.length w.length)
    (by intro i; simpa [initCfg] using initSt_len x w i) (by simp [initCfg]) n
  simpa [initCfg, hn] using this

/-- The number of queries is at most the cost. -/
theorem exec_log_card {O : Oracle} {s : Stmt} {st st' : Store} {c : ℕ} {lg : List Str}
    (h : Exec O s st st' c lg) : lg.length ≤ c := by
  obtain ⟨n, hn, hne⟩ := exec_min h
  have h1 : n ≤ ((step O)^[n] (⟨[s], st, 0, []⟩ : Cfg)).cost := steps_le_cost O _ n hne
  have h2 : ((step O)^[n] (⟨[s], st, 0, []⟩ : Cfg)).log.length ≤ 0 + n :=
    log_length_le O _ n
  rw [hn] at h1 h2
  simp at h1 h2
  omega

/-! ### `P^O ⊆ NP^O` -/

theorem upd_initSt_one (x w : Str) : upd (initSt x w) 1 [] = initSt x [] := by
  funext i
  unfold upd initSt
  by_cases h1 : i = 1
  · simp [h1]
  · by_cases h0 : i = 0 <;> simp [h0, h1]

theorem P_subset_NP (O : Oracle) : PClass O ⊆ NPClass O := by
  rintro L ⟨s, k, hs⟩
  refine ⟨.seq (.lit 1 []) s, k + 2, ?_⟩
  intro x
  obtain ⟨st, c, lg, hex, hc, hiff⟩ := hs x
  have hkey : ∀ w : Str, Exec O (.seq (.lit 1 []) s) (initSt x w) st (1 + ([] : Str).length + c + 1)
      (lg ++ []) := by
    intro w
    have h1 : Exec O (.lit 1 []) (initSt x w) (initSt x []) (1 + ([] : Str).length) [] := by
      have := exec_lit O (initSt x w) 1 ([] : Str)
      rwa [upd_initSt_one x w] at this
    exact exec_seq h1 hex
  have hcost : c + 2 ≤ tb (k + 2) x.length := by
    have := tb_add_two k x.length
    omega
  constructor
  · intro hx
    refine ⟨[], by simp, st, 1 + ([] : Str).length + c + 1, lg ++ [], hkey [], ?_, hiff.mpr hx⟩
    simp only [List.length_nil]
    omega
  · rintro ⟨w, -, st', c', lg', hex', -, hacc⟩
    have := exec_unique hex' (hkey w)
    rw [this.1] at hacc
    exact hiff.mp hacc

/-! ### Polynomials are dominated by exponentials -/

theorem poly_lt_exp (k : ℕ) : ∀ᶠ n : ℕ in atTop, (n + 2) ^ k < 2 ^ n := by
  have h := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k (r := 2) (by norm_num)
  have hc : (0:ℝ) < 1 / ((2:ℝ) ^ k * 2) := by positivity
  have h2 := h.def hc
  have h3 : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 2) ^ k < 2 ^ n := by
    filter_upwards [h2, eventually_ge_atTop 2] with n hn hn2
    have hnn : ((n : ℝ) + 2) ≤ 2 * (n : ℝ) := by
      have : (2:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith
    have h4 : ((n : ℝ) + 2) ^ k ≤ 2 ^ k * (n : ℝ) ^ k := by
      calc ((n : ℝ) + 2) ^ k ≤ (2 * (n : ℝ)) ^ k := pow_le_pow_left₀ (by positivity) hnn k
        _ = 2 ^ k * (n : ℝ) ^ k := by rw [mul_pow]
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hn
    have h5 : (n : ℝ) ^ k ≤ (1 / ((2:ℝ) ^ k * 2)) * 2 ^ n := by
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hn
      exact hn
    have h6 : (2:ℝ) ^ k * ((1 / ((2:ℝ) ^ k * 2)) * 2 ^ n) = 2 ^ n / 2 := by field_simp
    have h7 : (2:ℝ) ^ n / 2 < 2 ^ n := by
      have : (0:ℝ) < 2 ^ n := by positivity
      linarith
    calc ((n : ℝ) + 2) ^ k ≤ 2 ^ k * (n : ℝ) ^ k := h4
      _ ≤ 2 ^ k * ((1 / ((2:ℝ) ^ k * 2)) * 2 ^ n) := by
          exact mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = 2 ^ n / 2 := h6
      _ < 2 ^ n := h7
  filter_upwards [h3] with n hn
  have hcast : ((n + 2 : ℕ) : ℝ) ^ k < ((2 ^ n : ℕ) : ℝ) := by push_cast; exact_mod_cast hn
  exact_mod_cast hcast

/-- For every `k` and every bound `m` there is a length `n ≥ m` with `tb k n < 2 ^ n`. -/
theorem exists_diag_length (k m : ℕ) : ∃ n, m ≤ n ∧ tb k n < 2 ^ n := by
  obtain ⟨N, hN⟩ := (poly_lt_exp k).exists_forall_of_atTop
  exact ⟨max N m, le_max_right _ _, hN _ (le_max_left _ _)⟩

/-! ### Acceptance in terms of the configuration after `t` steps -/

theorem accepts_iff_at (O : Oracle) (s : Stmt) (x w : Str) (t : ℕ) :
    Accepts O s x w t ↔
      (((step O)^[t] (initCfg s x w)).stk = [] ∧ ((step O)^[t] (initCfg s x w)).cost ≤ t ∧
        ((step O)^[t] (initCfg s x w)).st 0 = [true]) := by
  unfold initCfg
  constructor
  · rintro ⟨st, c, lg, hex, hc, ha⟩
    obtain ⟨n, hn, hne⟩ := exec_min hex
    have h1 : n ≤ ((step O)^[n] (⟨[s], initSt x w, 0, []⟩ : Cfg)).cost := steps_le_cost O _ n hne
    rw [hn] at h1
    simp only [] at h1
    have h2 : (step O)^[t] (⟨[s], initSt x w, 0, []⟩ : Cfg)
        = (step O)^[n] (⟨[s], initSt x w, 0, []⟩ : Cfg) :=
      halt_stable O _ (by rw [hn]) (le_trans h1 hc)
    rw [h2, hn]
    exact ⟨rfl, hc, ha⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨((step O)^[t] (⟨[s], initSt x w, 0, []⟩ : Cfg)).st,
      ((step O)^[t] (⟨[s], initSt x w, 0, []⟩ : Cfg)).cost,
      ((step O)^[t] (⟨[s], initSt x w, 0, []⟩ : Cfg)).log, ⟨t, ?_⟩, h2, h3⟩
    generalize hc : (step O)^[t] (⟨[s], initSt x w, 0, []⟩ : Cfg) = d at h1 ⊢
    obtain ⟨stk, st', cst, lg⟩ := d
    simp only [] at h1 ⊢
    rw [h1]

/-! ### Runs with a cost bound -/

/-- `Runs O s st st' b`: the program halts, ending in store `st'`, at cost at most `b`. -/
def Runs (O : Oracle) (s : Stmt) (st st' : Store) (b : ℕ) : Prop :=
  ∃ c lg, Exec O s st st' c lg ∧ c ≤ b

theorem Runs.mono {O : Oracle} {s : Stmt} {st st' : Store} {b b' : ℕ} (h : Runs O s st st' b)
    (hb : b ≤ b') : Runs O s st st' b' := by
  obtain ⟨c, lg, hex, hc⟩ := h
  exact ⟨c, lg, hex, le_trans hc hb⟩

theorem Runs.seq {O : Oracle} {a b : Stmt} {st st₁ st₂ : Store} {b₁ b₂ : ℕ}
    (h1 : Runs O a st st₁ b₁) (h2 : Runs O b st₁ st₂ b₂) :
    Runs O (.seq a b) st st₂ (b₁ + b₂ + 1) := by
  obtain ⟨c₁, lg₁, hex₁, hc₁⟩ := h1
  obtain ⟨c₂, lg₂, hex₂, hc₂⟩ := h2
  exact ⟨c₁ + c₂ + 1, lg₂ ++ lg₁, exec_seq hex₁ hex₂, by omega⟩

theorem Runs.lit (O : Oracle) (st : Store) (i : ℕ) (v : Str) :
    Runs O (.lit i v) st (upd st i v) (1 + v.length) := ⟨_, _, exec_lit O st i v, le_rfl⟩

theorem Runs.cat (O : Oracle) (st : Store) (i j k : ℕ) :
    Runs O (.cat i j k) st (upd st i (st j ++ st k)) (1 + (st j).length + (st k).length) :=
  ⟨_, _, exec_cat O st i j k, by simp; omega⟩

theorem Runs.rep (O : Oracle) (st : Store) (i j k : ℕ) :
    Runs O (.rep i j k) st (upd st i (List.replicate ((st j).length * (st k).length) true))
      (1 + (st j).length * (st k).length) := ⟨_, _, exec_rep O st i j k, le_rfl⟩

theorem Runs.cns (O : Oracle) (st : Store) (i : ℕ) (b : Bool) (j : ℕ) :
    Runs O (.cns i b j) st (upd st i (b :: st j)) (2 + (st j).length) :=
  ⟨_, _, exec_cns O st i b j, by simp; omega⟩

theorem Runs.qry (O : Oracle) (st : Store) (i j : ℕ) :
    Runs O (.qry i j) st (upd st i (if O (st j) then [true] else [])) 1 :=
  ⟨_, _, exec_qry O st i j, le_rfl⟩

theorem Runs.skip (O : Oracle) (st : Store) : Runs O .skip st st 1 :=
  ⟨_, _, exec_skip O st, le_rfl⟩

theorem Runs.ifte {O : Oracle} {cd : Cond} {a b : Stmt} {st st' : Store} {bd : ℕ}
    (h : Runs O (if cd.ev st then a else b) st st' bd) :
    Runs O (.ifte cd a b) st st' (bd + 1) := by
  obtain ⟨c, lg, hex, hc⟩ := h
  exact ⟨c + 1, lg, exec_ifte hex, by omega⟩

/-! ### Existence of a fresh string of a given length -/

theorem exists_fresh (n : ℕ) (L : List Str) (h : L.length < 2 ^ n) :
    ∃ y : Str, y.length = n ∧ y ∉ L := by
  classical
  by_contra hc
  push_neg at hc
  have hsub : (Finset.univ : Finset (Fin n → Bool)).image (fun f => List.ofFn f) ⊆ L.toFinset := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
    obtain ⟨f, rfl⟩ := hy
    simp only [List.mem_toFinset]
    exact hc _ (by simp)
  have hcard : ((Finset.univ : Finset (Fin n → Bool)).image (fun f => List.ofFn f)).card = 2 ^ n := by
    rw [Finset.card_image_of_injective _ (fun f g hfg => List.ofFn_injective hfg)]
    simp
  have := Finset.card_le_card hsub
  rw [hcard] at this
  have h2 : L.toFinset.card ≤ L.length := List.toFinset_card_le L
  omega

end CS.BGS

