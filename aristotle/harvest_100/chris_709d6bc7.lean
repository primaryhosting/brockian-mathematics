/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.Model

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-! ## A calculus for reasoning about program execution -/

/-- `Exec O S n f` says: started with registers `σ`, the statement `S` terminates
after exactly `n σ` steps, leaving the registers in state `f σ` (and the rest of
the control stack untouched). -/
def Exec (O : Oracle) (S : Stmt) (n : (ℕ → Str) → ℕ) (f : (ℕ → Str) → (ℕ → Str)) : Prop :=
  ∀ (σ : ℕ → Str) (rest : List Stmt), (step O)^[n σ] (⟨S :: rest, σ⟩ : Config) = ⟨rest, f σ⟩

theorem exec_skip (O : Oracle) : Exec O .skip (fun _ => 1) id := by
  intro σ rest; simp [step]

theorem exec_push (O : Oracle) (r : ℕ) (b : Bool) :
    Exec O (.push r b) (fun _ => 1) (fun σ => Function.update σ r (b :: σ r)) := by
  intro σ rest; simp [step]

theorem exec_pop (O : Oracle) (r : ℕ) :
    Exec O (.pop r) (fun _ => 1) (fun σ => Function.update σ r (σ r).tail) := by
  intro σ rest; simp [step]

theorem exec_query (O : Oracle) (s r : ℕ) :
    Exec O (.query s r) (fun _ => 1) (fun σ => Function.update σ r (O (σ s) :: σ r)) := by
  intro σ rest; simp [step]

theorem exec_seq {O : Oracle} {a b : Stmt} {na nb : (ℕ → Str) → ℕ}
    {fa fb : (ℕ → Str) → (ℕ → Str)} (ha : Exec O a na fa) (hb : Exec O b nb fb) :
    Exec O (.seq a b) (fun σ => nb (fa σ) + (na σ + 1)) (fun σ => fb (fa σ)) := by
  intro σ rest
  rw [Function.iterate_add_apply, Function.iterate_add_apply]
  have h1 : (step O)^[1] (⟨Stmt.seq a b :: rest, σ⟩ : Config) = ⟨a :: b :: rest, σ⟩ := by
    simp [step]
  rw [h1, ha σ (b :: rest), hb (fa σ) rest]

theorem exec_ite {O : Oracle} {r : ℕ} {a b : Stmt} {na nb : (ℕ → Str) → ℕ}
    {fa fb : (ℕ → Str) → (ℕ → Str)} (ha : Exec O a na fa) (hb : Exec O b nb fb) :
    Exec O (.ite r a b)
      (fun σ => (if (σ r).head? = some true then na σ else nb σ) + 1)
      (fun σ => if (σ r).head? = some true then fa σ else fb σ) := by
  intro σ rest
  rw [Function.iterate_add_apply]
  have h1 : (step O)^[1] (⟨Stmt.ite r a b :: rest, σ⟩ : Config)
      = ⟨(if (σ r).head? = some true then a else b) :: rest, σ⟩ := by
    simp [step]
  rw [h1]
  by_cases h : (σ r).head? = some true
  · simp only [h, if_pos]
    exact ha σ rest
  · simp only [h, if_neg, if_false]
    exact hb σ rest

theorem replicate_append_cons {α : Type*} (m : ℕ) (b : α) (l : List α) :
    List.replicate m b ++ b :: l = b :: (List.replicate m b ++ l) := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.replicate_succ, ih]

theorem exec_padAux (O : Oracle) (m r : ℕ) :
    Exec O (.padAux m r) (fun _ => m + 1)
      (fun σ => Function.update σ r (List.replicate m true ++ σ r)) := by
  intro σ rest
  induction m generalizing σ with
  | zero => simp [step, Function.update_eq_self]
  | succ m ih =>
      have h1 : (step O)^[1] (⟨Stmt.padAux (m + 1) r :: rest, σ⟩ : Config)
          = ⟨Stmt.padAux m r :: rest, Function.update σ r (true :: σ r)⟩ := by
        simp [step]
      rw [show m + 1 + 1 = (m + 1) + 1 from rfl, Function.iterate_add_apply, h1,
        ih (Function.update σ r (true :: σ r))]
      congr 1
      funext y
      by_cases hy : y = r <;>
        simp [Function.update_apply, hy, List.replicate_succ, replicate_append_cons]

theorem exec_pad (O : Oracle) (k s r : ℕ) :
    Exec O (.pad k s r) (fun σ => (((σ s).length + 2) ^ k + 1) + 1)
      (fun σ => Function.update σ r (List.replicate (((σ s).length + 2) ^ k) true ++ σ r)) := by
  intro σ rest
  have h1 : (step O)^[1] (⟨Stmt.pad k s r :: rest, σ⟩ : Config)
      = ⟨Stmt.padAux (((σ s).length + 2) ^ k) r :: rest, σ⟩ := by
    simp [step]
  rw [Function.iterate_add_apply, h1, exec_padAux O _ r σ rest]

/-- Push `m` copies of the bit `b` onto register `r`. -/
def pushRep : ℕ → ℕ → Bool → Stmt
  | 0, _, _ => .skip
  | m + 1, r, b => .seq (.push r b) (pushRep m r b)

theorem exec_pushRep (O : Oracle) (m r : ℕ) (b : Bool) :
    Exec O (pushRep m r b) (fun _ => 2 * m + 1)
      (fun σ => Function.update σ r (List.replicate m b ++ σ r)) := by
  induction m with
  | zero =>
      intro σ rest
      simp [pushRep, step, Function.update_eq_self]
  | succ m ih =>
      intro σ rest
      have h := exec_seq (exec_push O r b) ih σ rest
      simp only at h
      rw [show (fun _ : ℕ → Str => 2 * (m + 1) + 1) σ = (2 * m + 1) + (1 + 1) from by
        simp; ring]
      refine (h.trans ?_)
      congr 1
      funext y
      by_cases hy : y = r <;>
        simp [Function.update_apply, hy, List.replicate_succ, replicate_append_cons]


theorem Exec.congr {O : Oracle} {S : Stmt} {n n' : (ℕ → Str) → ℕ}
    {f f' : (ℕ → Str) → (ℕ → Str)} (h : Exec O S n f)
    (hn : ∀ σ, n σ = n' σ) (hf : ∀ σ, f σ = f' σ) : Exec O S n' f' := by
  intro σ rest
  rw [← hn σ, ← hf σ]
  exact h σ rest

/-! ## Loops -/

/-- Doubling each bit of a string. -/
def dupStr : Str → Str
  | [] => []
  | b :: t => b :: b :: dupStr t

theorem dupStr_append (l₁ l₂ : Str) : dupStr (l₁ ++ l₂) = dupStr l₁ ++ dupStr l₂ := by
  induction l₁ with
  | nil => simp [dupStr]
  | cons b t ih => simp [dupStr, ih]

/-- Move the content of register `0` onto register `2`, doubling each bit. -/
def loopA : Stmt :=
  .wh 0 (.ite 0 (.seq (.push 2 true) (.seq (.push 2 true) (.pop 0)))
                (.seq (.push 2 false) (.seq (.push 2 false) (.pop 0))))

theorem exec_loopA_body (O : Oracle) :
    Exec O (.ite 0 (.seq (.push 2 true) (.seq (.push 2 true) (.pop 0)))
                   (.seq (.push 2 false) (.seq (.push 2 false) (.pop 0))))
      (fun _ => 6)
      (fun σ r => if r = 0 then (σ 0).tail
        else if r = 2 then ((σ 0).head?.getD false) :: ((σ 0).head?.getD false) :: σ 2
        else σ r) := by
  have hbr : ∀ b : Bool, Exec O (.seq (.push 2 b) (.seq (.push 2 b) (.pop 0)))
      (fun _ => 5)
      (fun σ r => if r = 0 then (σ 0).tail else if r = 2 then b :: b :: σ 2 else σ r) := by
    intro b
    refine Exec.congr (exec_seq (exec_push O 2 b) (exec_seq (exec_push O 2 b) (exec_pop O 0)))
      (fun σ => by simp) (fun σ => ?_)
    funext y
    by_cases h0 : y = 0 <;> by_cases h2 : y = 2 <;>
      simp [Function.update_apply, h0, h2]
  refine Exec.congr (exec_ite (hbr true) (hbr false)) (fun σ => by split <;> rfl) (fun σ => ?_)
  by_cases h : (σ 0).head? = some true
  · simp only [h, if_pos]
    funext y
    by_cases h2 : y = 2 <;> simp [h2, h]
  · simp only [h, if_neg, if_false]
    funext y
    by_cases h2 : y = 2 <;> simp [h2]
    cases hh : (σ 0).head? with
    | none => simp
    | some c => cases c with
      | true => exact absurd hh h
      | false => simp

theorem exec_loopA (O : Oracle) :
    Exec O loopA (fun σ => 7 * (σ 0).length + 1)
      (fun σ r => if r = 0 then [] else if r = 2 then dupStr (σ 0).reverse ++ σ 2 else σ r) := by
  have key : ∀ (x : Str) (σ : ℕ → Str), σ 0 = x → ∀ rest : List Stmt,
      (step O)^[7 * x.length + 1] (⟨loopA :: rest, σ⟩ : Config)
        = ⟨rest, fun r => if r = 0 then [] else if r = 2 then dupStr x.reverse ++ σ 2 else σ r⟩ := by
    intro x
    induction x with
    | nil =>
        intro σ h0 rest
        have h1 : (step O)^[1] (⟨loopA :: rest, σ⟩ : Config) = ⟨rest, σ⟩ := by
          simp [loopA, step, h0]
        simpa using h1.trans (by
          congr 1
          funext y
          by_cases hy0 : y = 0 <;> by_cases hy2 : y = 2 <;>
            simp [hy0, hy2, h0, dupStr])
    | cons b t ih =>
        intro σ h0 rest
        set σ' : ℕ → Str := fun r => if r = 0 then t else if r = 2 then b :: b :: σ 2 else σ r
          with hσ'
        have h7 : (step O)^[7] (⟨loopA :: rest, σ⟩ : Config) = ⟨loopA :: rest, σ'⟩ := by
          have hs : (step O)^[1] (⟨loopA :: rest, σ⟩ : Config)
              = ⟨(.ite 0 (.seq (.push 2 true) (.seq (.push 2 true) (.pop 0)))
                   (.seq (.push 2 false) (.seq (.push 2 false) (.pop 0))))
                  :: loopA :: rest, σ⟩ := by
            simp [loopA, step, h0]
          rw [show (7 : ℕ) = 6 + 1 from rfl, Function.iterate_add_apply, hs,
            exec_loopA_body O σ (loopA :: rest)]
          congr 1
          funext y
          by_cases hy0 : y = 0 <;> by_cases hy2 : y = 2 <;>
            simp [hσ', hy0, hy2, h0]
        rw [show 7 * (b :: t).length + 1 = (7 * t.length + 1) + 7 from by
          simp [List.length_cons]; ring, Function.iterate_add_apply, h7,
          ih σ' (by simp [hσ']) rest]
        congr 1
        funext y
        by_cases hy0 : y = 0 <;> by_cases hy2 : y = 2 <;>
          simp [hσ', hy0, hy2, dupStr_append, dupStr]
  intro σ rest
  exact key (σ 0) σ rfl rest

/-- Take one bit off register `1` for each bit of register `0`, pushing them
onto register `2`. -/
def loopB : Stmt :=
  .wh 0 (.seq (.pop 0) (.ite 1 (.seq (.pop 1) (.push 2 true)) (.seq (.pop 1) (.push 2 false))))

/-- The first `n` bits of `w`, padded with `false` if `w` is too short. -/
def padTake : ℕ → Str → Str
  | 0, _ => []
  | n + 1, w => (w.head?.getD false) :: padTake n w.tail

theorem padTake_length (n : ℕ) (w : Str) : (padTake n w).length = n := by
  induction n generalizing w with
  | zero => simp [padTake]
  | succ n ih => simp [padTake, ih]

theorem padTake_self (w : Str) : padTake w.length w = w := by
  induction w with
  | nil => simp [padTake]
  | cons b t ih => simp [padTake, ih]

theorem exec_loopB_body (O : Oracle) :
    Exec O (.seq (.pop 0) (.ite 1 (.seq (.pop 1) (.push 2 true)) (.seq (.pop 1) (.push 2 false))))
      (fun _ => 6)
      (fun σ r => if r = 0 then (σ 0).tail else if r = 1 then (σ 1).tail
        else if r = 2 then ((σ 1).head?.getD false) :: σ 2 else σ r) := by
  have hbr : ∀ b : Bool, Exec O (.seq (.pop 1) (.push 2 b)) (fun _ => 3)
      (fun σ r => if r = 1 then (σ 1).tail else if r = 2 then b :: σ 2 else σ r) := by
    intro b
    refine Exec.congr (exec_seq (exec_pop O 1) (exec_push O 2 b)) (fun σ => by simp)
      (fun σ => ?_)
    funext y
    by_cases h1 : y = 1 <;> by_cases h2 : y = 2 <;> simp [Function.update_apply, h1, h2]
  have hite : Exec O (.ite 1 (.seq (.pop 1) (.push 2 true)) (.seq (.pop 1) (.push 2 false)))
      (fun _ => 4)
      (fun σ r => if r = 1 then (σ 1).tail
        else if r = 2 then ((σ 1).head?.getD false) :: σ 2 else σ r) := by
    refine Exec.congr (exec_ite (hbr true) (hbr false)) (fun σ => by split <;> rfl) (fun σ => ?_)
    by_cases h : (σ 1).head? = some true
    · simp only [h, if_pos]
      funext y
      by_cases h2 : y = 2 <;> simp [h2, h]
    · simp only [h, if_neg, if_false]
      funext y
      by_cases h2 : y = 2 <;> simp [h2]
      cases hh : (σ 1).head? with
      | none => simp
      | some c => cases c with
        | true => exact absurd hh h
        | false => simp
  refine Exec.congr (exec_seq (exec_pop O 0) hite) (fun σ => by simp) (fun σ => ?_)
  funext y
  by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> by_cases h2 : y = 2 <;>
    simp [Function.update_apply, h0, h1, h2]

theorem exec_loopB (O : Oracle) :
    Exec O loopB (fun σ => 7 * (σ 0).length + 1)
      (fun σ r => if r = 0 then [] else if r = 1 then (σ 1).drop (σ 0).length
        else if r = 2 then (padTake (σ 0).length (σ 1)).reverse ++ σ 2 else σ r) := by
  have key : ∀ (x : Str) (σ : ℕ → Str), σ 0 = x → ∀ rest : List Stmt,
      (step O)^[7 * x.length + 1] (⟨loopB :: rest, σ⟩ : Config)
        = ⟨rest, fun r => if r = 0 then [] else if r = 1 then (σ 1).drop x.length
            else if r = 2 then (padTake x.length (σ 1)).reverse ++ σ 2 else σ r⟩ := by
    intro x
    induction x with
    | nil =>
        intro σ h0 rest
        have h1 : (step O)^[1] (⟨loopB :: rest, σ⟩ : Config) = ⟨rest, σ⟩ := by
          simp [loopB, step, h0]
        simpa using h1.trans (by
          congr 1
          funext y
          by_cases hy0 : y = 0 <;> by_cases hy1 : y = 1 <;> by_cases hy2 : y = 2 <;>
            simp [hy0, hy1, hy2, h0, padTake])
    | cons b t ih =>
        intro σ h0 rest
        set σ' : ℕ → Str := fun r => if r = 0 then t else if r = 1 then (σ 1).tail
          else if r = 2 then ((σ 1).head?.getD false) :: σ 2 else σ r with hσ'
        have h7 : (step O)^[7] (⟨loopB :: rest, σ⟩ : Config) = ⟨loopB :: rest, σ'⟩ := by
          have hs : (step O)^[1] (⟨loopB :: rest, σ⟩ : Config)
              = ⟨(.seq (.pop 0)
                    (.ite 1 (.seq (.pop 1) (.push 2 true)) (.seq (.pop 1) (.push 2 false))))
                  :: loopB :: rest, σ⟩ := by
            simp [loopB, step, h0]
          rw [show (7 : ℕ) = 6 + 1 from rfl, Function.iterate_add_apply, hs,
            exec_loopB_body O σ (loopB :: rest)]
          congr 1
          funext y
          by_cases hy0 : y = 0 <;> by_cases hy1 : y = 1 <;> by_cases hy2 : y = 2 <;>
            simp [hσ', hy0, hy1, hy2, h0]
        rw [show 7 * (b :: t).length + 1 = (7 * t.length + 1) + 7 from by
          simp [List.length_cons]; ring, Function.iterate_add_apply, h7,
          ih σ' (by simp [hσ']) rest]
        congr 1
        funext y
        by_cases hy0 : y = 0 <;> by_cases hy1 : y = 1 <;> by_cases hy2 : y = 2 <;>
          simp [hσ', hy0, hy1, hy2, padTake, List.drop_tail]
  intro σ rest
  exact key (σ 0) σ rfl rest

/-- Empty register `1`. -/
def clearOne : Stmt := .wh 1 (.pop 1)

theorem exec_clearOne (O : Oracle) :
    Exec O clearOne (fun σ => 2 * (σ 1).length + 1)
      (fun σ r => if r = 1 then [] else σ r) := by
  have key : ∀ (w : Str) (σ : ℕ → Str), σ 1 = w → ∀ rest : List Stmt,
      (step O)^[2 * w.length + 1] (⟨clearOne :: rest, σ⟩ : Config)
        = ⟨rest, fun r => if r = 1 then [] else σ r⟩ := by
    intro w
    induction w with
    | nil =>
        intro σ h1 rest
        have h : (step O)^[1] (⟨clearOne :: rest, σ⟩ : Config) = ⟨rest, σ⟩ := by
          simp [clearOne, step, h1]
        simpa using h.trans (by
          congr 1
          funext y
          by_cases hy : y = 1 <;> simp [hy, h1])
    | cons b t ih =>
        intro σ h1 rest
        set σ' : ℕ → Str := fun r => if r = 1 then t else σ r with hσ'
        have h2 : (step O)^[2] (⟨clearOne :: rest, σ⟩ : Config) = ⟨clearOne :: rest, σ'⟩ := by
          have hs : (step O)^[1] (⟨clearOne :: rest, σ⟩ : Config)
              = ⟨Stmt.pop 1 :: clearOne :: rest, σ⟩ := by
            simp [clearOne, step, h1]
          rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, hs,
            exec_pop O 1 σ (clearOne :: rest)]
          congr 1
          funext y
          by_cases hy : y = 1 <;> simp [hσ', Function.update_apply, hy, h1]
        rw [show 2 * (b :: t).length + 1 = (2 * t.length + 1) + 2 from by
          simp [List.length_cons]; ring, Function.iterate_add_apply, h2,
          ih σ' (by simp [hσ']) rest]
        congr 1
        funext y
        by_cases hy : y = 1 <;> simp [hσ', hy]
  intro σ rest
  exact key (σ 1) σ rfl rest

end CS

/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


import Mathlib

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-! ## Strings, oracles, languages -/

/-- Binary strings. -/
abbrev Str := List Bool

/-- An oracle is a decision procedure for strings (a language, given by its
characteristic function). -/
abbrev Oracle := Str → Bool

/-! ## An oracle machine model

A machine is a structured program operating on countably many stack registers
holding binary strings.  Each elementary instruction costs one step, and each
instruction changes the content of a register by at most one bit, so that in
`t` steps a register can grow by at most `t` bits.  Register `0` holds the
input (and, at the end of a computation, the answer bit on top), register `1`
holds the witness (nondeterministic guess) and all other registers start empty.
-/

/-- Programs. `query s r` queries the oracle on the content of register `s` and
pushes the answer bit onto register `r`.  `padAux m r` pushes `m` bits onto
register `r`, one per step (so it costs `m + 1` steps); `pad k s r` starts such
a block-write of `(|reg s| + 2) ^ k` bits. -/
inductive Stmt where
  | skip : Stmt
  | push : ℕ → Bool → Stmt
  | pop : ℕ → Stmt
  | query : ℕ → ℕ → Stmt
  | seq : Stmt → Stmt → Stmt
  | ite : ℕ → Stmt → Stmt → Stmt
  | wh : ℕ → Stmt → Stmt
  | padAux : ℕ → ℕ → Stmt
  | pad : ℕ → ℕ → ℕ → Stmt
  deriving DecidableEq

/-- A configuration: the list of statements still to be executed, and the
contents of the registers. -/
structure Config where
  ctrl : List Stmt
  regs : ℕ → Str

/-- One step of computation. -/
def step (O : Oracle) (c : Config) : Config :=
  match c.ctrl with
  | [] => c
  | s :: rest =>
    match s with
    | .skip => ⟨rest, c.regs⟩
    | .push r b => ⟨rest, Function.update c.regs r (b :: c.regs r)⟩
    | .pop r => ⟨rest, Function.update c.regs r (c.regs r).tail⟩
    | .query s r => ⟨rest, Function.update c.regs r (O (c.regs s) :: c.regs r)⟩
    | .seq a b => ⟨a :: b :: rest, c.regs⟩
    | .ite r a b => ⟨(if (c.regs r).head? = some true then a else b) :: rest, c.regs⟩
    | .wh r body =>
        if c.regs r = [] then ⟨rest, c.regs⟩ else ⟨body :: .wh r body :: rest, c.regs⟩
    | .padAux m r =>
        match m with
        | 0 => ⟨rest, c.regs⟩
        | m + 1 => ⟨.padAux m r :: rest, Function.update c.regs r (true :: c.regs r)⟩
    | .pad k s r => ⟨.padAux (((c.regs s).length + 2) ^ k) r :: rest, c.regs⟩

/-- The string queried by a configuration, if the next instruction is a query. -/
def qry (c : Config) : Option Str :=
  match c.ctrl with
  | .query s _ :: _ => some (c.regs s)
  | _ => none

/-- The initial configuration of machine `M` on input `x` with witness `w`. -/
def init (M : Stmt) (x w : Str) : Config :=
  ⟨[M], fun r => if r = 0 then x else if r = 1 then w else []⟩

/-- The configuration after `T` steps. -/
def runFor (O : Oracle) (M : Stmt) (x w : Str) (T : ℕ) : Config :=
  (step O)^[T] (init M x w)

/-- `M` accepts `(x, w)` with oracle `O` within `T` steps. -/
def AcceptsIn (O : Oracle) (M : Stmt) (x w : Str) (T : ℕ) : Prop :=
  (runFor O M x w T).ctrl = [] ∧ ((runFor O M x w T).regs 0).head? = some true

/-! ## Basic properties of the semantics -/

theorem step_halted (O : Oracle) {c : Config} (h : c.ctrl = []) : step O c = c := by
  unfold step
  rw [h]

theorem iterate_step_halted (O : Oracle) {c : Config} (h : c.ctrl = []) (n : ℕ) :
    (step O)^[n] c = c := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply, step_halted O h, ih]

theorem iterate_step_stable (O : Oracle) (c : Config) {n : ℕ}
    (h : ((step O)^[n] c).ctrl = []) {m : ℕ} (hm : n ≤ m) :
    (step O)^[m] c = (step O)^[n] c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [show n + d = d + n from by omega, Function.iterate_add_apply,
    iterate_step_halted O h]

theorem AcceptsIn.mono {O : Oracle} {M : Stmt} {x w : Str} {T T' : ℕ}
    (h : AcceptsIn O M x w T) (hle : T ≤ T') : AcceptsIn O M x w T' := by
  obtain ⟨h1, h2⟩ := h
  have : runFor O M x w T' = runFor O M x w T := iterate_step_stable O _ h1 hle
  exact ⟨by rw [this]; exact h1, by rw [this]; exact h2⟩

/-- Each step increases the length of any register by at most one. -/
theorem step_len (O : Oracle) (c : Config) (r : ℕ) :
    ((step O c).regs r).length ≤ (c.regs r).length + 1 := by
  unfold step
  match hc : c.ctrl with
  | [] => simp
  | s :: rest =>
    cases s with
    | skip => simp
    | push r' b =>
        by_cases h : r = r' <;> simp [Function.update, h] <;> omega
    | pop r' =>
        by_cases h : r = r' <;> simp [Function.update, h] <;> omega
    | query s' r' =>
        by_cases h : r = r' <;> simp [Function.update, h] <;> omega
    | seq a b => simp
    | ite r' a b => simp
    | wh r' body => by_cases h : c.regs r' = [] <;> simp [h]
    | padAux m r' =>
        cases m with
        | zero => simp
        | succ m => by_cases h : r = r' <;> simp [Function.update, h] <;> omega
    | pad k s' r' => simp

theorem iterate_step_len (O : Oracle) (c : Config) (r : ℕ) (t : ℕ) :
    (((step O)^[t] c).regs r).length ≤ (c.regs r).length + t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (step_len O _ r) (by omega)

/-- Every register content during a run of `M` on `(x, w)` after `t` steps has
length at most `max |x| |w| + t`. -/
theorem runFor_len (O : Oracle) (M : Stmt) (x w : Str) (t : ℕ) (r : ℕ) :
    ((runFor O M x w t).regs r).length ≤ max x.length w.length + t := by
  have := iterate_step_len O (init M x w) r t
  refine le_trans this (by
    have : ((init M x w).regs r).length ≤ max x.length w.length := by
      unfold init
      by_cases h0 : r = 0
      · simp [h0]
      · by_cases h1 : r = 1 <;> simp [h0, h1]
    omega)

/-! ## Locality: the computation only depends on the answers to the queries made -/

/-- The queries made during the first `T` steps starting from `c`. -/
def qList (O : Oracle) (c : Config) : ℕ → List Str
  | 0 => []
  | T + 1 => (qList O c T) ++ (qry ((step O)^[T] c)).toList

theorem qList_length (O : Oracle) (c : Config) (T : ℕ) : (qList O c T).length ≤ T := by
  induction T with
  | zero => simp [qList]
  | succ T ih =>
      simp only [qList, List.length_append]
      have : ((qry ((step O)^[T] c)).toList).length ≤ 1 := by
        cases qry ((step O)^[T] c) <;> simp
      omega

theorem qList_mono (O : Oracle) (c : Config) {T T' : ℕ} (h : T ≤ T') :
    ∀ s ∈ qList O c T, s ∈ qList O c T' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => simp
  | succ d ih =>
      intro s hs
      have hT : T + (d + 1) = (T + d) + 1 := by omega
      rw [hT]
      simp only [qList, List.mem_append]
      exact Or.inl (ih s hs)

theorem step_congr (O₁ O₂ : Oracle) (c : Config)
    (h : ∀ s ∈ qry c, O₁ s = O₂ s) : step O₁ c = step O₂ c := by
  unfold step
  match hc : c.ctrl with
  | [] => rfl
  | s :: rest =>
    cases s with
    | query s' r' =>
        have : O₁ (c.regs s') = O₂ (c.regs s') := by
          apply h
          simp [qry, hc]
        simp [this]
    | skip => rfl
    | push r' b => rfl
    | pop r' => rfl
    | seq a b => rfl
    | ite r' a b => rfl
    | wh r' body => rfl
    | padAux m r' => cases m <;> rfl
    | pad k s' r' => rfl

/-- If two oracles agree on all strings queried during the first `T` steps of
the `O₁`-run, then the two runs coincide for `T` steps. -/
theorem iterate_step_congr (O₁ O₂ : Oracle) (c : Config) (T : ℕ)
    (h : ∀ s ∈ qList O₁ c T, O₁ s = O₂ s) :
    (step O₁)^[T] c = (step O₂)^[T] c := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hT : ∀ s ∈ qList O₁ c T, O₁ s = O₂ s := by
        intro s hs
        exact h s (qList_mono O₁ c (Nat.le_succ T) s hs)
      have heq := ih hT
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← heq]
      apply step_congr
      intro s hs
      apply h
      simp only [qList, List.mem_append]
      right
      cases hq : qry ((step O₁)^[T] c) with
      | none => rw [hq] at hs; simp at hs
      | some v => rw [hq] at hs; simp at hs; simp [hs]

/-! ## The relativized classes P and NP -/

/-- `M` halts on `(x, w)` within `T` steps. -/
def Halts (O : Oracle) (M : Stmt) (x w : Str) (T : ℕ) : Prop :=
  (runFor O M x w T).ctrl = []

/-- If a machine has halted by time `T`, acceptance at any later time is the
same as acceptance at time `T`. -/
theorem AcceptsIn_of_halts {O : Oracle} {M : Stmt} {x w : Str} {T T' : ℕ}
    (hH : Halts O M x w T) (hle : T ≤ T') (h : AcceptsIn O M x w T') :
    AcceptsIn O M x w T := by
  have heq : runFor O M x w T' = runFor O M x w T := iterate_step_stable O _ hH hle
  unfold AcceptsIn at h ⊢
  rw [heq] at h
  exact h

/-- `L ∈ P^O`: some machine decides `L` (with empty witness), halting within
time `(n+2)^k`. -/
def PLang (O : Oracle) : Set (Set Str) :=
  {L | ∃ (M : Stmt) (k : ℕ),
      (∀ x : Str, Halts O M x [] ((x.length + 2) ^ k)) ∧
      (∀ x : Str, x ∈ L ↔ AcceptsIn O M x [] ((x.length + 2) ^ k))}

/-- `L ∈ NP^O`: some verifier machine, running in time `(n+2)^k`, accepts `x`
together with some witness of length at most `(n+2)^k` exactly when `x ∈ L`. -/
def NPLang (O : Oracle) : Set (Set Str) :=
  {L | ∃ (M : Stmt) (k : ℕ), ∀ x : Str,
      x ∈ L ↔ ∃ w : Str, w.length ≤ (x.length + 2) ^ k ∧
        AcceptsIn O M x w ((x.length + 2) ^ k)}

end CS

/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.Programs

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-! ## There are only countably many machines -/

def Stmt.toNat : Stmt → ℕ
  | .skip => Nat.pair 0 0
  | .push r b => Nat.pair 1 (Nat.pair r (cond b 1 0))
  | .pop r => Nat.pair 2 r
  | .query s r => Nat.pair 3 (Nat.pair s r)
  | .seq a b => Nat.pair 4 (Nat.pair a.toNat b.toNat)
  | .ite r a b => Nat.pair 5 (Nat.pair r (Nat.pair a.toNat b.toNat))
  | .wh r a => Nat.pair 6 (Nat.pair r a.toNat)
  | .padAux m r => Nat.pair 7 (Nat.pair m r)
  | .pad k s r => Nat.pair 8 (Nat.pair k (Nat.pair s r))

theorem Stmt.toNat_injective : Function.Injective Stmt.toNat := by
  intro a
  induction a with
  | skip => intro b h; cases b <;> simp_all [Stmt.toNat, Nat.pair_eq_pair]
  | push r c =>
      intro b h
      cases b <;> simp [Stmt.toNat, Nat.pair_eq_pair] at h
      rename_i r' c'
      obtain ⟨h1, h2⟩ := h
      subst h1
      cases c <;> cases c' <;> simp_all
  | pop r => intro b h; cases b <;> simp_all [Stmt.toNat, Nat.pair_eq_pair]
  | query s r => intro b h; cases b <;> simp_all [Stmt.toNat, Nat.pair_eq_pair]
  | seq p q ihp ihq =>
      intro b h
      cases b <;> simp [Stmt.toNat, Nat.pair_eq_pair] at h
      rw [ihp h.1, ihq h.2]
  | ite r p q ihp ihq =>
      intro b h
      cases b <;> simp [Stmt.toNat, Nat.pair_eq_pair] at h
      rw [h.1, ihp h.2.1, ihq h.2.2]
  | wh r p ihp =>
      intro b h
      cases b <;> simp [Stmt.toNat, Nat.pair_eq_pair] at h
      rw [h.1, ihp h.2]
  | padAux m r => intro b h; cases b <;> simp_all [Stmt.toNat, Nat.pair_eq_pair]
  | pad k s r => intro b h; cases b <;> simp_all [Stmt.toNat, Nat.pair_eq_pair]

instance : Countable Stmt := Stmt.toNat_injective.countable

instance : Nonempty Stmt := ⟨.skip⟩

/-- An enumeration of all pairs (machine, exponent). -/
noncomputable def enumPair : ℕ → Stmt × ℕ := (exists_surjective_nat (Stmt × ℕ)).choose

theorem enumPair_surjective : Function.Surjective enumPair :=
  (exists_surjective_nat (Stmt × ℕ)).choose_spec

/-! ## An arithmetic helper for time bounds -/

theorem const_mul_pow_le (C j n : ℕ) : C * (n + 2) ^ j ≤ (n + 2) ^ (j + C) := by
  have h1 : C ≤ (n + 2) ^ C :=
    le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left (by omega) C)
  calc C * (n + 2) ^ j ≤ (n + 2) ^ C * (n + 2) ^ j := Nat.mul_le_mul_right _ h1
    _ = (n + 2) ^ (j + C) := by rw [pow_add]; ring

/-- Running a whole program from the initial configuration. -/
theorem exec_init {O : Oracle} {M : Stmt} {x w : Str} {n : (ℕ → Str) → ℕ}
    {f : (ℕ → Str) → (ℕ → Str)} (h : Exec O M n f) :
    (step O)^[n (init M x w).regs] (init M x w) = ⟨[], f (init M x w).regs⟩ :=
  h (init M x w).regs []

/-! ## The verifier used for the separating oracle

On input `x` and witness `w` it reads `|x|` bits off the witness and queries the
resulting string. -/

def verifier : Stmt := .seq loopB (.query 2 0)

theorem verifier_run (O : Oracle) (x w : Str) :
    ∃ (c : ℕ) (σ' : ℕ → Str), (step O)^[c] (init verifier x w) = ⟨[], σ'⟩ ∧
      σ' 0 = [O (padTake x.length w).reverse] ∧ c ≤ 7 * x.length + 3 := by
  refine ⟨_, _, exec_init (x := x) (w := w) (exec_seq (exec_loopB O) (exec_query O 2 0)), ?_, ?_⟩
  · simp [init]
  · simp [init]
    omega

theorem verifier_accepts (O : Oracle) (x w : Str) {T : ℕ} (hT : 7 * x.length + 3 ≤ T) :
    AcceptsIn O verifier x w T ↔ O (padTake x.length w).reverse = true := by
  obtain ⟨c, σ', hrun, hσ', hc⟩ := verifier_run O x w
  have hhalt : ((step O)^[c] (init verifier x w)).ctrl = [] := by rw [hrun]
  have hstable : runFor O verifier x w T = ⟨[], σ'⟩ := by
    unfold runFor
    rw [iterate_step_stable O _ hhalt (le_trans hc hT)]
    exact hrun
  unfold AcceptsIn
  rw [hstable]
  simp [hσ']

/-! ## Padding a machine so that it ignores its witness -/

def ignoreWitness (M : Stmt) : Stmt := .seq clearOne M

theorem ignoreWitness_run (O : Oracle) (M : Stmt) (x w : Str) :
    (step O)^[2 * w.length + 2] (init (ignoreWitness M) x w) = init M x [] := by
  have hs : (step O)^[1] (init (ignoreWitness M) x w) = ⟨[clearOne, M], (init M x w).regs⟩ := by
    simp [init, ignoreWitness, step]
  rw [show 2 * w.length + 2 = (2 * w.length + 1) + 1 from rfl, Function.iterate_add_apply, hs]
  have h := exec_clearOne O (init M x w).regs [M]
  rw [show ((fun σ : ℕ → Str => 2 * (σ 1).length + 1) (init M x w).regs)
      = 2 * w.length + 1 from by simp [init]] at h
  rw [h]
  simp only [init, Config.mk.injEq, true_and]
  funext y
  by_cases hy : y = 1 <;> simp [hy]

theorem ignoreWitness_accepts_iff (O : Oracle) (M : Stmt) (x w : Str) (T : ℕ) :
    AcceptsIn O (ignoreWitness M) x w (T + (2 * w.length + 2)) ↔ AcceptsIn O M x [] T := by
  unfold AcceptsIn runFor
  rw [show T + (2 * w.length + 2) = T + (2 * w.length + 2) from rfl,
    Function.iterate_add_apply, ignoreWitness_run O M x w]

/-! ## The encoding used by the collapsing oracle -/

/-- Length of the padding block in the encoding. -/
def encPad (k n : ℕ) : ℕ := (n + 2) + (n + 2) ^ (k + 1)

/-- The string queried by the deterministic simulator: the machine index `i`
and the exponent `k` in unary, the reversal of the input with each bit doubled,
and a long block of padding. -/
def ENC (i k : ℕ) (x : Str) : Str :=
  List.replicate i true ++ false :: (List.replicate k true ++ false ::
    (dupStr x.reverse ++ true :: false :: List.replicate (encPad k x.length) true))

/-- The deterministic machine which queries `ENC i k x` and copies the answer. -/
def colProg (i k : ℕ) : Stmt :=
  .seq (.pad (k + 1) 0 2) (.seq (.pad 1 0 2) (.seq (.push 2 false) (.seq (.push 2 true)
    (.seq loopA (.seq (.push 2 false) (.seq (pushRep k 2 true) (.seq (.push 2 false)
      (.seq (pushRep i 2 true) (.query 2 0)))))))))

theorem colProg_run (O : Oracle) (i k : ℕ) (x : Str) :
    ∃ (c : ℕ) (σ' : ℕ → Str), (step O)^[c] (init (colProg i k) x []) = ⟨[], σ'⟩ ∧
      σ' 0 = [O (ENC i k x)] ∧
      c ≤ 30 + 2 * i + 2 * k + 10 * (x.length + 2) + (x.length + 2) ^ (k + 1) := by
  refine ⟨_, _, exec_init (x := x) (w := ([] : Str))
    (exec_seq (exec_pad O (k + 1) 0 2) (exec_seq (exec_pad O 1 0 2)
      (exec_seq (exec_push O 2 false) (exec_seq (exec_push O 2 true)
      (exec_seq (exec_loopA O) (exec_seq (exec_push O 2 false)
      (exec_seq (exec_pushRep O k 2 true) (exec_seq (exec_push O 2 false)
      (exec_seq (exec_pushRep O i 2 true) (exec_query O 2 0)))))))))), ?_, ?_⟩
  · simp [init, Function.update_apply, ENC, encPad, List.replicate_add]
  · simp [init]
    ring_nf
    omega

theorem colProg_halts_accepts (O : Oracle) (i k : ℕ) (x : Str) {T : ℕ}
    (hT : 30 + 2 * i + 2 * k + 10 * (x.length + 2) + (x.length + 2) ^ (k + 1) ≤ T) :
    Halts O (colProg i k) x [] T ∧
      (AcceptsIn O (colProg i k) x [] T ↔ O (ENC i k x) = true) := by
  obtain ⟨c, σ', hrun, hσ', hc⟩ := colProg_run O i k x
  have hhalt : ((step O)^[c] (init (colProg i k) x [])).ctrl = [] := by rw [hrun]
  have hstable : runFor O (colProg i k) x [] T = ⟨[], σ'⟩ := by
    unfold runFor
    rw [iterate_step_stable O _ hhalt (le_trans hc hT)]
    exact hrun
  refine ⟨by unfold Halts; rw [hstable], ?_⟩
  unfold AcceptsIn
  rw [hstable]
  simp [hσ']

/-! ## `P` is contained in `NP` -/

theorem ignoreWitness_not_halted (O : Oracle) (M : Stmt) (x w : Str) {t : ℕ}
    (ht : t < 2 * w.length + 2) : ((step O)^[t] (init (ignoreWitness M) x w)).ctrl ≠ [] := by
  intro h
  have hstab := iterate_step_stable O (init (ignoreWitness M) x w) h (le_of_lt ht)
  rw [ignoreWitness_run O M x w] at hstab
  have : (init M x ([] : Str)).ctrl = [] := by rw [hstab, h]
  simp [init] at this

theorem AcceptsIn_ignoreWitness_imp (O : Oracle) (M : Stmt) (x w : Str) (T : ℕ)
    (h : AcceptsIn O (ignoreWitness M) x w T) : AcceptsIn O M x [] T := by
  rcases Nat.lt_or_ge T (2 * w.length + 2) with hlt | hge
  · exact absurd h.1 (ignoreWitness_not_halted O M x w hlt)
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hge
    have hacc : AcceptsIn O M x [] d := by
      rw [← ignoreWitness_accepts_iff O M x w d,
        show d + (2 * w.length + 2) = T from by omega]
      exact h
    exact hacc.mono (by omega)

theorem PLang_subset_NPLang (O : Oracle) : PLang O ⊆ NPLang O := by
  rintro L ⟨M, k, hH, hMk⟩
  refine ⟨ignoreWitness M, k + 2, fun x => ?_⟩
  have h1 : 1 ≤ (x.length + 2) ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : (x.length + 2) ^ k * 4 ≤ (x.length + 2) ^ (k + 2) := by
    rw [show k + 2 = k + 2 from rfl, pow_add]
    exact Nat.mul_le_mul_left _ (by
      have : (x.length + 2) ^ 2 = (x.length + 2) * (x.length + 2) := by ring
      nlinarith)
  have hTB : (x.length + 2) ^ k + 2 ≤ (x.length + 2) ^ (k + 2) := by omega
  constructor
  · intro hx
    refine ⟨[], by simp, ?_⟩
    have hacc : AcceptsIn O M x [] ((x.length + 2) ^ (k + 2) - 2) :=
      ((hMk x).1 hx).mono (by omega)
    have hiw := (ignoreWitness_accepts_iff O M x [] ((x.length + 2) ^ (k + 2) - 2)).2 hacc
    have heq : (x.length + 2) ^ (k + 2) - 2 + (2 * ([] : Str).length + 2)
        = (x.length + 2) ^ (k + 2) := by simp; omega
    rwa [heq] at hiw
  · rintro ⟨w, _, hacc⟩
    have h3 := AcceptsIn_ignoreWitness_imp O M x w _ hacc
    exact (hMk x).2 (AcceptsIn_of_halts (hH x) (by omega) h3)

end CS

/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.Machines

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-! ## Polynomials are eventually dominated by `2 ^ n` -/

theorem poly_lt_exp (k N : ℕ) : ∃ n, N ≤ n ∧ (n + 2) ^ k < 2 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt k (r := (2:ℝ)) (by norm_num)
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (n:ℝ) ^ k / 2 ^ n < (2:ℝ)⁻¹ ^ k := by
    have hpos : (0:ℝ) < (2:ℝ)⁻¹ ^ k := by positivity
    exact h.eventually (eventually_lt_nhds hpos)
  obtain ⟨n, hn⟩ := ((hev.and (Filter.eventually_ge_atTop (max N 2))).exists)
  refine ⟨n, le_trans (le_max_left _ _) hn.2, ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right N 2) hn.2
  have key : ((n:ℝ) + 2) ^ k < 2 ^ n := by
    have hle : ((n:ℝ) + 2) ≤ 2 * n := by
      have : (2:ℝ) ≤ n := by exact_mod_cast hn2
      linarith
    have h1 : ((n:ℝ) + 2) ^ k ≤ (2 * n) ^ k := pow_le_pow_left₀ (by positivity) hle k
    have h3 : (n:ℝ) ^ k < (2:ℝ)⁻¹ ^ k * 2 ^ n := by
      have hpow : (0:ℝ) < 2 ^ n := by positivity
      have h4 := hn.1
      rw [div_lt_iff₀ hpow] at h4
      linarith
    calc ((n:ℝ) + 2) ^ k ≤ 2 ^ k * (n:ℝ) ^ k := by rw [← mul_pow]; exact h1
      _ < 2 ^ k * ((2:ℝ)⁻¹ ^ k * 2 ^ n) := mul_lt_mul_of_pos_left h3 (by positivity)
      _ = 2 ^ n := by rw [← mul_assoc, ← mul_pow]; norm_num
  exact_mod_cast key

/-- A length at least `N` at which `2 ^ ℓ` beats the time bound `(ℓ + 2) ^ k`. -/
def chooseLen (N k : ℕ) : ℕ := Nat.find (poly_lt_exp k N)

theorem chooseLen_ge (N k : ℕ) : N ≤ chooseLen N k := (Nat.find_spec (poly_lt_exp k N)).1

theorem chooseLen_big (N k : ℕ) : (chooseLen N k + 2) ^ k < 2 ^ (chooseLen N k) :=
  (Nat.find_spec (poly_lt_exp k N)).2

/-! ## Queries made during a run -/

theorem mem_qList (O : Oracle) (c : Config) (T : ℕ) (s : Str) (h : s ∈ qList O c T) :
    ∃ j, j < T ∧ qry ((step O)^[j] c) = some s := by
  induction T with
  | zero => simp [qList] at h
  | succ T ih =>
      simp only [qList, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨j, hj, hq⟩ := ih h
        exact ⟨j, by omega, hq⟩
      · refine ⟨T, by omega, ?_⟩
        cases hq : qry ((step O)^[T] c) with
        | none => rw [hq] at h; simp at h
        | some v =>
            rw [hq] at h
            simp at h
            subst h
            simp_all

theorem qList_len_bound (O : Oracle) (M : Stmt) (x w : Str) (T : ℕ) (s : Str)
    (h : s ∈ qList O (init M x w) T) : s.length ≤ max x.length w.length + T := by
  obtain ⟨j, hj, hq⟩ := mem_qList O (init M x w) T s h
  unfold qry at hq
  cases hc : ((step O)^[j] (init M x w)).ctrl with
  | nil => rw [hc] at hq; simp at hq
  | cons hd tl =>
      rw [hc] at hq
      cases hd with
      | query a b =>
          simp only at hq
          have : s = ((step O)^[j] (init M x w)).regs a := by
            injection hq.symm
          rw [this]
          have := runFor_len O M x w j a
          unfold runFor at this
          omega
      | skip => simp at hq
      | push a b => simp at hq
      | pop a => simp at hq
      | seq a b => simp at hq
      | ite a b c => simp at hq
      | wh a b => simp at hq
      | padAux a b => simp at hq
      | pad a b c => simp at hq

/-! ## Oracles given by finite sets -/

open Classical in
/-- The oracle deciding membership in a finite set. -/
noncomputable def oracleOf (F : Finset Str) : Oracle := fun s => decide (s ∈ F)

theorem oracleOf_apply (F : Finset Str) (s : Str) : oracleOf F s = true ↔ s ∈ F := by
  classical
  simp [oracleOf]

/-! ## Transferring a computation between oracles -/

theorem AcceptsIn_congr {O₁ O₂ : Oracle} {M : Stmt} {x w : Str} {T : ℕ}
    (h : ∀ s ∈ qList O₁ (init M x w) T, O₁ s = O₂ s) :
    (AcceptsIn O₁ M x w T ↔ AcceptsIn O₂ M x w T) := by
  unfold AcceptsIn runFor
  rw [iterate_step_congr O₁ O₂ (init M x w) T h]

/-! ## Choosing a string that was not queried -/

theorem exists_fresh (l : ℕ) (Q : List Str) (h : Q.length < 2 ^ l) :
    ∃ z : Str, z.length = l ∧ z ∉ Q := by
  classical
  by_contra hc
  push_neg at hc
  have hsub : (Finset.univ : Finset (Fin l → Bool)).image (fun f => List.ofFn f)
      ⊆ Q.toFinset := by
    intro s hs
    simp only [Finset.mem_image] at hs
    obtain ⟨f, _, rfl⟩ := hs
    have := hc (List.ofFn f) (by simp)
    simpa using this
  have hcard : ((Finset.univ : Finset (Fin l → Bool)).image (fun f => List.ofFn f)).card
      = 2 ^ l := by
    rw [Finset.card_image_of_injective _ List.ofFn_injective]
    simp
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  have h2 := List.toFinset_card_le Q
  omega

open Classical in
/-- Some string of length `l` outside the list `Q` (when one exists). -/
noncomputable def freshStr (l : ℕ) (Q : List Str) : Str :=
  if h : ∃ z : Str, z.length = l ∧ z ∉ Q then h.choose else []

theorem freshStr_spec (l : ℕ) (Q : List Str) (h : Q.length < 2 ^ l) :
    (freshStr l Q).length = l ∧ freshStr l Q ∉ Q := by
  have hex := exists_fresh l Q h
  simp only [freshStr, dif_pos hex]
  exact hex.choose_spec

/-! ## The stage construction of the separating oracle -/

open Classical in
/-- Stage `n` of the construction: the strings put into the oracle so far,
together with a bound below which the oracle is already decided. -/
noncomputable def stage : ℕ → Finset Str × ℕ
  | 0 => (∅, 0)
  | n + 1 =>
      let F := (stage n).1
      let l := chooseLen (stage n).2 (enumPair n).2
      let T := (l + 2) ^ (enumPair n).2
      let x : Str := List.replicate l true
      (if AcceptsIn (oracleOf F) (enumPair n).1 x [] T then F
        else insert (freshStr l (qList (oracleOf F) (init (enumPair n).1 x []) T)) F,
       l + T + 1)

/-- The input diagonalized against at stage `n` has this length. -/
noncomputable def stLen (n : ℕ) : ℕ := chooseLen (stage n).2 (enumPair n).2

/-- The time bound used at stage `n`. -/
noncomputable def stTime (n : ℕ) : ℕ := (stLen n + 2) ^ (enumPair n).2

/-- The input diagonalized against at stage `n`. -/
noncomputable def stInput (n : ℕ) : Str := List.replicate (stLen n) true

theorem stInput_length (n : ℕ) : (stInput n).length = stLen n := by simp [stInput]

theorem stage_snd_succ (n : ℕ) : (stage (n + 1)).2 = stLen n + stTime n + 1 := rfl

open Classical in
theorem stage_fst_succ (n : ℕ) :
    (stage (n + 1)).1 =
      if AcceptsIn (oracleOf (stage n).1) (enumPair n).1 (stInput n) [] (stTime n)
        then (stage n).1
        else insert (freshStr (stLen n)
          (qList (oracleOf (stage n).1) (init (enumPair n).1 (stInput n) []) (stTime n)))
          (stage n).1 := rfl

theorem stage_snd_le_stLen (n : ℕ) : (stage n).2 ≤ stLen n := chooseLen_ge _ _

theorem stTime_pos (n : ℕ) : 0 < stTime n := by
  unfold stTime
  positivity

theorem stage_snd_lt_succ (n : ℕ) : stLen n < (stage (n + 1)).2 := by
  rw [stage_snd_succ]
  have := stTime_pos n
  omega

theorem stage_snd_mono_succ (n : ℕ) : (stage n).2 ≤ (stage (n + 1)).2 :=
  le_trans (stage_snd_le_stLen n) (le_of_lt (stage_snd_lt_succ n))

theorem stage_snd_mono {n m : ℕ} (h : n ≤ m) : (stage n).2 ≤ (stage m).2 := by
  induction m with
  | zero => simp_all
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with h' | h'
      · exact le_trans (ih (by omega)) (stage_snd_mono_succ m)
      · have : n = m + 1 := by omega
        subst this
        exact le_rfl

theorem stage_fst_subset_succ (n : ℕ) : (stage n).1 ⊆ (stage (n + 1)).1 := by
  rw [stage_fst_succ]
  split
  · exact subset_rfl
  · exact Finset.subset_insert _ _

theorem stage_fst_mono {n m : ℕ} (h : n ≤ m) : (stage n).1 ⊆ (stage m).1 := by
  induction m with
  | zero => simp_all
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with h' | h'
      · exact subset_trans (ih (by omega)) (stage_fst_subset_succ m)
      · have : n = m + 1 := by omega
        subst this
        exact subset_rfl

theorem stage_mem_succ (n : ℕ) (s : Str) (hs : s ∈ (stage (n + 1)).1) :
    s ∈ (stage n).1 ∨ s.length = stLen n := by
  rw [stage_fst_succ] at hs
  split at hs
  · exact Or.inl hs
  · rcases Finset.mem_insert.1 hs with h | h
    · right
      subst h
      by_cases hQ : (qList (oracleOf (stage n).1) (init (enumPair n).1 (stInput n) [])
          (stTime n)).length < 2 ^ (stLen n)
      · exact (freshStr_spec _ _ hQ).1
      · exfalso
        apply hQ
        have h1 := qList_length (oracleOf (stage n).1)
          (init (enumPair n).1 (stInput n) []) (stTime n)
        have h2 : stTime n < 2 ^ (stLen n) := chooseLen_big (stage n).2 (enumPair n).2
        omega
    · exact Or.inl h

theorem stage_len_lt (n : ℕ) (s : Str) (hs : s ∈ (stage n).1) : s.length < (stage n).2 := by
  induction n with
  | zero => simp [stage] at hs
  | succ n ih =>
      rcases stage_mem_succ n s hs with h | h
      · have := ih h
        have h2 := stage_snd_le_stLen n
        have h3 := stage_snd_lt_succ n
        omega
      · have h3 := stage_snd_lt_succ n
        omega

theorem stage_mem_later {n m : ℕ} (h : n ≤ m) (s : Str) (hs : s ∈ (stage m).1) :
    s ∈ (stage n).1 ∨ (stage n).2 ≤ s.length := by
  induction m with
  | zero =>
      have : n = 0 := by omega
      subst this
      exact Or.inl hs
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with h' | h'
      · rcases stage_mem_succ m s hs with h1 | h1
        · exact ih (by omega) h1
        · right
          have : (stage n).2 ≤ (stage m).2 := stage_snd_mono (by omega)
          have h2 := stage_snd_le_stLen m
          omega
      · have : n = m + 1 := by omega
        subst this
        exact Or.inl hs

/-- The separating oracle. -/
def Bset : Set Str := {s | ∃ n, s ∈ (stage n).1}

open Classical in
/-- The separating oracle, as a characteristic function. -/
noncomputable def Boracle : Oracle := fun s => decide (s ∈ Bset)

theorem Boracle_true_iff (s : Str) : Boracle s = true ↔ ∃ n, s ∈ (stage n).1 := by
  classical
  simp [Boracle, Bset]

/-- Below the threshold of stage `n`, the final oracle agrees with stage `n`. -/
theorem Boracle_agrees (n : ℕ) (s : Str) (hs : s.length < (stage n).2) :
    (Boracle s = true ↔ s ∈ (stage n).1) := by
  rw [Boracle_true_iff]
  constructor
  · rintro ⟨m, hm⟩
    rcases Nat.lt_or_ge m n with h | h
    · exact stage_fst_mono (le_of_lt h) hm
    · rcases stage_mem_later h s hm with h1 | h1
      · exact h1
      · omega
  · intro h
    exact ⟨n, h⟩

/-! ## The diagonal language -/

/-- The language `{x : some string of length `|x|` is in the oracle}`. -/
def diagLang (O : Oracle) : Set Str := {x | ∃ z : Str, z.length = x.length ∧ O z = true}

theorem diagLang_mem_NP (O : Oracle) : diagLang O ∈ NPLang O := by
  refine ⟨verifier, 3, fun x => ?_⟩
  have hT : 7 * x.length + 3 ≤ (x.length + 2) ^ 3 := by
    have h : (x.length + 2) ^ 3 = x.length ^ 3 + 6 * x.length ^ 2 + 12 * x.length + 8 := by ring
    omega
  have hlen : x.length ≤ (x.length + 2) ^ 3 :=
    le_trans (by omega) (Nat.le_self_pow (by norm_num) (x.length + 2))
  constructor
  · rintro ⟨z, hz, hOz⟩
    refine ⟨z.reverse, by simpa [hz] using hlen, ?_⟩
    rw [verifier_accepts O x z.reverse hT]
    have : padTake x.length z.reverse = z.reverse := by
      rw [show x.length = z.reverse.length from by simp [hz]]
      exact padTake_self _
    rw [this]
    simpa using hOz
  · rintro ⟨w, _, hacc⟩
    rw [verifier_accepts O x w hT] at hacc
    exact ⟨(padTake x.length w).reverse, by simp [padTake_length], hacc⟩

/-! ## The diagonal language for `B` is not in `P^B` -/

theorem diagLang_not_mem_P : diagLang Boracle ∉ PLang Boracle := by
  rintro ⟨M, k, -, hMk⟩
  obtain ⟨n, hn⟩ := enumPair_surjective (M, k)
  have hM : (enumPair n).1 = M := by rw [hn]
  have hk : (enumPair n).2 = k := by rw [hn]
  have hxlen : (stInput n).length = stLen n := stInput_length n
  have hT : stTime n = ((stInput n).length + 2) ^ k := by
    rw [hxlen]
    unfold stTime
    rw [hk]
  have hqlen : ∀ s ∈ qList (oracleOf (stage n).1) (init M (stInput n) []) (stTime n),
      s.length < (stage (n + 1)).2 := by
    intro s hs
    have hb := qList_len_bound (oracleOf (stage n).1) M (stInput n) [] (stTime n) s hs
    rw [hxlen] at hb
    rw [stage_snd_succ]
    simp only [List.length_nil, Nat.max_eq_left, Nat.zero_le, max_eq_left] at hb
    omega
  by_cases hacc : AcceptsIn (oracleOf (stage n).1) M (stInput n) [] (stTime n)
  · -- the machine accepts, so no string of length `stLen n` enters the oracle
    have hfst : (stage (n + 1)).1 = (stage n).1 := by
      rw [stage_fst_succ, hM, if_pos hacc]
    have hagree : ∀ s ∈ qList (oracleOf (stage n).1) (init M (stInput n) []) (stTime n),
        oracleOf (stage n).1 s = Boracle s := by
      intro s hs
      rw [Bool.eq_iff_iff, oracleOf_apply, Boracle_agrees (n + 1) s (hqlen s hs), hfst]
    have haccB : AcceptsIn Boracle M (stInput n) [] (stTime n) := (AcceptsIn_congr hagree).1 hacc
    have hmem : stInput n ∈ diagLang Boracle := by
      rw [hMk (stInput n), ← hT]
      exact haccB
    obtain ⟨z, hz, hzB⟩ := hmem
    rw [hxlen] at hz
    rw [Boracle_true_iff] at hzB
    obtain ⟨m, hm⟩ := hzB
    have hzin : z ∈ (stage n).1 ∨ (stage (n + 1)).2 ≤ z.length := by
      rcases Nat.lt_or_ge m (n + 1) with h | h
      · left
        have : z ∈ (stage (n + 1)).1 := stage_fst_mono (by omega) hm
        rwa [hfst] at this
      · rcases stage_mem_later h z hm with h1 | h1
        · left; rwa [hfst] at h1
        · right; exact h1
    rcases hzin with h1 | h1
    · have h2 := stage_len_lt n z h1
      have h3 := stage_snd_le_stLen n
      omega
    · rw [stage_snd_succ] at h1
      have := stTime_pos n
      omega
  · -- the machine rejects, so a fresh string of length `stLen n` enters the oracle
    have hQ : (qList (oracleOf (stage n).1) (init M (stInput n) []) (stTime n)).length
        < 2 ^ (stLen n) := by
      have h1 := qList_length (oracleOf (stage n).1) (init M (stInput n) []) (stTime n)
      have h2 : stTime n < 2 ^ (stLen n) := chooseLen_big (stage n).2 (enumPair n).2
      omega
    have hzspec := freshStr_spec (stLen n)
      (qList (oracleOf (stage n).1) (init M (stInput n) []) (stTime n)) hQ
    have hfst : (stage (n + 1)).1 = insert (freshStr (stLen n)
        (qList (oracleOf (stage n).1) (init M (stInput n) []) (stTime n))) (stage n).1 := by
      rw [stage_fst_succ, hM, if_neg hacc]
    have hagree : ∀ s ∈ qList (oracleOf (stage n).1) (init M (stInput n) []) (stTime n),
        oracleOf (stage n).1 s = Boracle s := by
      intro s hs
      have hne : s ≠ freshStr (stLen n)
          (qList (oracleOf (stage n).1) (init M (stInput n) []) (stTime n)) := by
        intro h
        exact hzspec.2 (h ▸ hs)
      rw [Bool.eq_iff_iff, oracleOf_apply, Boracle_agrees (n + 1) s (hqlen s hs), hfst,
        Finset.mem_insert]
      constructor
      · exact fun h => Or.inr h
      · rintro (h | h)
        · exact absurd h hne
        · exact h
    have hnB : ¬ AcceptsIn Boracle M (stInput n) [] (stTime n) := fun h =>
      hacc ((AcceptsIn_congr hagree).2 h)
    have hmem : stInput n ∈ diagLang Boracle := by
      refine ⟨freshStr (stLen n)
        (qList (oracleOf (stage n).1) (init M (stInput n) []) (stTime n)), ?_, ?_⟩
      · rw [hxlen, hzspec.1]
      · rw [Boracle_true_iff]
        exact ⟨n + 1, by rw [hfst]; exact Finset.mem_insert_self _ _⟩
    rw [hMk (stInput n), ← hT] at hmem
    exact hnB hmem

/-- There is an oracle relative to which `P` and `NP` differ. -/
theorem P_ne_NP_Boracle : PLang Boracle ≠ NPLang Boracle := by
  intro h
  exact diagLang_not_mem_P (by rw [h]; exact diagLang_mem_NP Boracle)

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

