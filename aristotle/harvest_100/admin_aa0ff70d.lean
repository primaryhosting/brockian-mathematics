import Mathlib

/-!
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Overview

The Immerman-Szelepcsényi theorem states that nondeterministic space is closed under
complement; for logarithmic space, `NL = coNL`.  Its content is the *inductive counting*
technique: a nondeterministic machine can, using only `O(log n)` workspace, verify that a
vertex is **not** reachable in the configuration graph of another nondeterministic machine.

This file formalises exactly that.  We fix a small nondeterministic imperative language
whose programs use a constant number of variables holding natural numbers bounded by the
number `m` of vertices of the graph they are run on (so `O(log m)` bits of workspace), and
which can inspect the graph only through the local edge test `edg a b` applied to two of
its variables.  We then exhibit **one fixed program** `CS.nonReach` -- a closed term, not
depending on the graph, on `m`, or on anything else -- and prove

* `CS.immerman_szelepcsenyi`: `nonReach` has an accepting run on a graph `E` with source
  `s` and target `t` if and only if `t` is *not* reachable from `s`;
* `CS.immerman_szelepcsenyi_machine`: consequently, for every nondeterministic machine `M`
  with a finite configuration space, `nonReach` run on the configuration graph of `M`
  accepts exactly when `M` rejects;
* `CS.nonReach_space`: all variables stay bounded by `m` throughout a run, and there are
  only `13` of them (`CS.env_card`), i.e. the complementing computation uses `O(log m)`
  space.

If `M` is a nondeterministic `O(log n)`-space machine on inputs of length `n`, its
configuration graph has `m = n^{O(1)}` vertices, so `log m = O(log n)`: the complementing
program is again a nondeterministic logarithmic-space computation.  This is `NL = coNL`.
-/

namespace CS

/-! ## A nondeterministic logarithmic-space machine model

A machine is a *program* in a tiny imperative language with a fixed, finite number of
variables.  Each variable holds a natural number bounded by `m`, the number of vertices of
the configuration graph the program is run on; hence each variable occupies `O(log m)` bits
and a whole configuration of the program (program point + variable values) occupies
`O(log m)` bits.  The program may inspect the graph only through the local test
`edge a b` on the values of two of its variables.

`Stmt.ch` is nondeterministic choice and `Stmt.guess` nondeterministically stores an
arbitrary value `≤ m` in a variable; `Stmt.fail` has no transition, so a computation
*accepts* exactly when a terminating execution exists.
-/

abbrev Var := Fin 13

def vZ : Var := 0     -- constant 0
def vS : Var := 1     -- source vertex
def vTgt : Var := 2   -- target vertex
def vI : Var := 3     -- layer index
def vC : Var := 4     -- |R_i|
def vC2 : Var := 5    -- accumulator for |R_{i+1}|
def vV : Var := 6     -- vertex under consideration
def vU : Var := 7     -- vertex enumerated in the counting loop
def vCnt : Var := 8   -- number of certified vertices
def vF : Var := 9     -- flag
def vW : Var := 10    -- current vertex of a guessed path
def vJ : Var := 11    -- length of the guessed path so far
def vT : Var := 12    -- guessed next vertex


inductive Cond where
  | eqv (a b : Var) : Cond
  | ltv (a b : Var) : Cond
  | isV (a : Var) : Cond
  | edg (a b : Var) : Cond

inductive Stmt where
  | skip : Stmt
  | fail : Stmt
  | zero (x : Var) : Stmt
  | incr (x : Var) : Stmt
  | cpy (x y : Var) : Stmt
  | guess (x : Var) : Stmt
  | seq (a b : Stmt) : Stmt
  | ite (c : Cond) (a b : Stmt) : Stmt
  | ch (a b : Stmt) : Stmt
  | wh (c : Cond) (a : Stmt) : Stmt

/-- Environments: the values of the (finitely many) variables. -/
abbrev Env := Var → ℕ

def upd (e : Env) (x : Var) (k : ℕ) : Env := Function.update e x k

@[simp] theorem upd_same (e : Env) (x : Var) (k : ℕ) : upd e x k x = k := by
  simp [upd]

@[simp] theorem upd_ne (e : Env) {x y : Var} (k : ℕ) (h : y ≠ x) : upd e x k y = e y := by
  simp [upd, Function.update_of_ne h]

theorem upd_apply (e : Env) (x y : Var) (k : ℕ) :
    upd e x k y = if y = x then k else e y := by
  simp [upd, Function.update_apply]

variable {m : ℕ}

/-- The edge test on raw natural numbers. -/
def edgeB (E : Fin m → Fin m → Bool) (y x : ℕ) : Bool :=
  if hy : y < m then if hx : x < m then E ⟨y, hy⟩ ⟨x, hx⟩ else false else false

def evalCond (E : Fin m → Fin m → Bool) (c : Cond) (e : Env) : Bool :=
  match c with
  | .eqv a b => decide (e a = e b)
  | .ltv a b => decide (e a < e b)
  | .isV a => decide (e a < m)
  | .edg a b => edgeB E (e a) (e b)

/-- Big-step semantics.  There is no rule for `fail`, and `incr` is blocked once a variable
reaches the bound `m`: this is what makes the model space bounded. -/
inductive Exec (E : Fin m → Fin m → Bool) : Stmt → Env → Env → Prop
  | skip {e} : Exec E .skip e e
  | zero {e x} : Exec E (.zero x) e (upd e x 0)
  | incr {e x} : e x < m → Exec E (.incr x) e (upd e x (e x + 1))
  | cpy {e x y} : Exec E (.cpy x y) e (upd e x (e y))
  | guess {e x k} : k ≤ m → Exec E (.guess x) e (upd e x k)
  | seq {a b e e' e''} : Exec E a e e' → Exec E b e' e'' → Exec E (.seq a b) e e''
  | iteT {c a b e e'} : evalCond E c e = true → Exec E a e e' → Exec E (.ite c a b) e e'
  | iteF {c a b e e'} : evalCond E c e = false → Exec E b e e' → Exec E (.ite c a b) e e'
  | chL {a b e e'} : Exec E a e e' → Exec E (.ch a b) e e'
  | chR {a b e e'} : Exec E b e e' → Exec E (.ch a b) e e'
  | whF {c a e} : evalCond E c e = false → Exec E (.wh c a) e e
  | whT {c a e e' e''} : evalCond E c e = true → Exec E a e e' → Exec E (.wh c a) e' e'' →
      Exec E (.wh c a) e e''

/-- The set of variables a statement can modify. -/
def mods : Stmt → Finset Var
  | .skip | .fail => ∅
  | .zero x | .incr x | .cpy x _ | .guess x => {x}
  | .seq a b | .ite _ a b | .ch a b => mods a ∪ mods b
  | .wh _ a => mods a

theorem exec_frame {E : Fin m → Fin m → Bool} {st : Stmt} {e e' : Env}
    (h : Exec E st e e') : ∀ x ∉ mods st, e' x = e x := by
  induction h with
  | skip => intro x _; rfl
  | zero => intro x hx; simp [mods] at hx; exact upd_ne _ _ hx
  | incr h => intro x hx; simp [mods] at hx; exact upd_ne _ _ hx
  | cpy => intro x hx; simp [mods] at hx; exact upd_ne _ _ hx
  | guess h => intro x hx; simp [mods] at hx; exact upd_ne _ _ hx
  | seq _ _ iha ihb =>
      intro x hx
      simp [mods, Finset.mem_union] at hx
      rw [ihb x (by simp [hx.2]), iha x (by simp [hx.1])]
  | iteT _ _ ih => intro x hx; simp [mods, Finset.mem_union] at hx; exact ih x (by simp [hx.1])
  | iteF _ _ ih => intro x hx; simp [mods, Finset.mem_union] at hx; exact ih x (by simp [hx.2])
  | chL _ ih => intro x hx; simp [mods, Finset.mem_union] at hx; exact ih x (by simp [hx.1])
  | chR _ ih => intro x hx; simp [mods, Finset.mem_union] at hx; exact ih x (by simp [hx.2])
  | whF => intro x _; rfl
  | whT _ _ _ ihb ihw =>
      intro x hx
      simp [mods] at hx
      rw [ihw x (by simpa [mods] using hx), ihb x (by simpa [mods] using hx)]

theorem upd_bounded {e : Env} {y : Var} {k : ℕ} (hb : ∀ x, e x ≤ m) (hk : k ≤ m) :
    ∀ x, upd e y k x ≤ m := by
  intro x
  by_cases hx : x = y
  · subst hx; simpa using hk
  · rw [upd_ne _ _ hx]; exact hb x

theorem exec_bounded {E : Fin m → Fin m → Bool} {st : Stmt} {e e' : Env}
    (h : Exec E st e e') (hb : ∀ x, e x ≤ m) : ∀ x, e' x ≤ m := by
  induction h with
  | skip => exact hb
  | zero => exact upd_bounded hb (Nat.zero_le _)
  | incr h => exact upd_bounded hb (by omega)
  | cpy => exact upd_bounded hb (hb _)
  | guess h => exact upd_bounded hb h
  | seq _ _ iha ihb => exact ihb (iha hb)
  | iteT _ _ ih => exact ih hb
  | iteF _ _ ih => exact ih hb
  | chL _ ih => exact ih hb
  | chR _ ih => exact ih hb
  | whF => exact hb
  | whT _ _ _ ihb ihw => exact ihw (ihb hb)

/-! ### Inversion lemmas -/

theorem exec_skip_inv {E : Fin m → Fin m → Bool} {e e' : Env} (h : Exec E .skip e e') :
    e' = e := by cases h; rfl

theorem exec_fail_inv {E : Fin m → Fin m → Bool} {e e' : Env} (h : Exec E .fail e e') :
    False := by cases h

theorem exec_zero_inv {E : Fin m → Fin m → Bool} {x : Var} {e e' : Env}
    (h : Exec E (.zero x) e e') : e' = upd e x 0 := by cases h; rfl

theorem exec_incr_inv {E : Fin m → Fin m → Bool} {x : Var} {e e' : Env}
    (h : Exec E (.incr x) e e') : e x < m ∧ e' = upd e x (e x + 1) := by
  cases h with | incr hlt => exact ⟨hlt, rfl⟩

theorem exec_cpy_inv {E : Fin m → Fin m → Bool} {x y : Var} {e e' : Env}
    (h : Exec E (.cpy x y) e e') : e' = upd e x (e y) := by cases h; rfl

theorem exec_guess_inv {E : Fin m → Fin m → Bool} {x : Var} {e e' : Env}
    (h : Exec E (.guess x) e e') : ∃ k, k ≤ m ∧ e' = upd e x k := by
  cases h with | @guess _ _ k hk => exact ⟨k, hk, rfl⟩

theorem exec_seq_inv {E : Fin m → Fin m → Bool} {a b : Stmt} {e e'' : Env}
    (h : Exec E (.seq a b) e e'') : ∃ e', Exec E a e e' ∧ Exec E b e' e'' := by
  cases h with | @seq _ _ _ e1 _ h1 h2 => exact ⟨e1, h1, h2⟩

theorem exec_ite_inv {E : Fin m → Fin m → Bool} {c : Cond} {a b : Stmt} {e e' : Env}
    (h : Exec E (.ite c a b) e e') :
    (evalCond E c e = true ∧ Exec E a e e') ∨ (evalCond E c e = false ∧ Exec E b e e') := by
  cases h with
  | iteT hc hb => exact Or.inl ⟨hc, hb⟩
  | iteF hc hb => exact Or.inr ⟨hc, hb⟩

theorem exec_ch_inv {E : Fin m → Fin m → Bool} {a b : Stmt} {e e' : Env}
    (h : Exec E (.ch a b) e e') : Exec E a e e' ∨ Exec E b e e' := by
  cases h with
  | chL hb => exact Or.inl hb
  | chR hb => exact Or.inr hb

/-- Soundness rule for `while` loops: an invariant preserved by the body holds on exit. -/
theorem wh_sound {E : Fin m → Fin m → Bool} {c : Cond} {body : Stmt} {Inv : Env → Prop}
    (hbody : ∀ a a', Inv a → evalCond E c a = true → Exec E body a a' → Inv a')
    {e e' : Env} (h : Exec E (.wh c body) e e') (hI : Inv e) :
    Inv e' ∧ evalCond E c e' = false := by
  generalize hst : (Stmt.wh c body) = st at h
  induction h with
  | @whF c' a' e0 hc => cases hst; exact ⟨hI, hc⟩
  | @whT c' a' e0 e1 e2 hc hb hw ihb ihw =>
      cases hst
      exact ihw (hbody _ _ hI hc hb) rfl
  | skip => cases hst
  | zero => cases hst
  | incr => cases hst
  | cpy => cases hst
  | guess => cases hst
  | seq => cases hst
  | iteT => cases hst
  | iteF => cases hst
  | chL => cases hst
  | chR => cases hst

/-! ## Layers of reachability -/

/-- `reachB E s i x` : the vertex `x` is reachable from `s` by a path of length at most `i`. -/
def reachB (E : Fin m → Fin m → Bool) (s : Fin m) : ℕ → ℕ → Bool
  | 0, x => decide (x = s.val)
  | i + 1, x => reachB E s i x || (List.range m).any (fun y => reachB E s i y && edgeB E y x)

/-- The set of vertices reachable in at most `i` steps and smaller than `k`. -/
def Rlt (E : Fin m → Fin m → Bool) (s : Fin m) (i k : ℕ) : Finset ℕ :=
  (Finset.range k).filter (fun x => reachB E s i x = true)

/-- The set of vertices reachable in at most `i` steps. -/
def Rset (E : Fin m → Fin m → Bool) (s : Fin m) (i : ℕ) : Finset ℕ := Rlt E s i m

/-- The number of vertices reachable in at most `i` steps. -/
def Rcard (E : Fin m → Fin m → Bool) (s : Fin m) (i : ℕ) : ℕ := (Rset E s i).card

theorem edgeB_lt {E : Fin m → Fin m → Bool} {y x : ℕ} (h : edgeB E y x = true) :
    y < m ∧ x < m := by
  unfold edgeB at h
  split at h
  · split at h
    · exact ⟨‹_›, ‹_›⟩
    · simp at h
  · simp at h

theorem edgeB_fin {E : Fin m → Fin m → Bool} (a b : Fin m) : edgeB E a.val b.val = E a b := by
  simp [edgeB, a.isLt, b.isLt]

theorem reachB_lt {E : Fin m → Fin m → Bool} {s : Fin m} :
    ∀ {i x}, reachB E s i x = true → x < m := by
  intro i
  induction i with
  | zero => intro x h; simp [reachB] at h; subst h; exact s.isLt
  | succ i ih =>
      intro x h
      simp [reachB] at h
      rcases h with h | ⟨y, _, _, h2⟩
      · exact ih h
      · exact (edgeB_lt h2).2

theorem reachB_zero {E : Fin m → Fin m → Bool} {s : Fin m} : reachB E s 0 s.val = true := by
  simp [reachB]

theorem reachB_succ {E : Fin m → Fin m → Bool} {s : Fin m} {i x : ℕ} (h : reachB E s i x = true) :
    reachB E s (i+1) x = true := by simp [reachB, h]

theorem reachB_le {E : Fin m → Fin m → Bool} {s : Fin m} {i j x : ℕ} (hij : i ≤ j)
    (h : reachB E s i x = true) : reachB E s j x = true := by
  induction j with
  | zero =>
      have : i = 0 := by omega
      subst this; exact h
  | succ j ih =>
      rcases Nat.lt_or_ge i (j+1) with h1 | h1
      · exact reachB_succ (ih (by omega))
      · have : i = j + 1 := by omega
        subst this; exact h

theorem reachB_step {E : Fin m → Fin m → Bool} {s : Fin m} {i y x : ℕ}
    (hy : reachB E s i y = true) (he : edgeB E y x = true) : reachB E s (i+1) x = true := by
  simp [reachB]
  right
  exact ⟨y, (edgeB_lt he).1, hy, he⟩

theorem reachB_succ_cases {E : Fin m → Fin m → Bool} {s : Fin m} {i x : ℕ}
    (h : reachB E s (i+1) x = true) :
    reachB E s i x = true ∨ ∃ y, reachB E s i y = true ∧ edgeB E y x = true := by
  simp [reachB] at h
  rcases h with h | ⟨y, _, h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨y, h1, h2⟩

theorem mem_Rlt {E : Fin m → Fin m → Bool} {s : Fin m} {i k x : ℕ} :
    x ∈ Rlt E s i k ↔ x < k ∧ reachB E s i x = true := by
  simp [Rlt, Finset.mem_filter, Finset.mem_range]

theorem mem_Rset {E : Fin m → Fin m → Bool} {s : Fin m} {i x : ℕ} :
    x ∈ Rset E s i ↔ reachB E s i x = true := by
  rw [Rset, mem_Rlt]
  exact ⟨fun h => h.2, fun h => ⟨reachB_lt h, h⟩⟩

theorem Rset_subset {E : Fin m → Fin m → Bool} {s : Fin m} {i : ℕ} :
    Rset E s i ⊆ Rset E s (i+1) := by
  intro x hx
  rw [mem_Rset] at *
  exact reachB_succ hx

theorem Rset_stable_step {E : Fin m → Fin m → Bool} {s : Fin m} {i : ℕ}
    (h : Rset E s i = Rset E s (i+1)) : Rset E s (i+1) = Rset E s (i+2) := by
  apply Finset.Subset.antisymm Rset_subset
  intro x hx
  rw [mem_Rset] at *
  rcases reachB_succ_cases hx with h1 | ⟨y, hy, he⟩
  · exact h1
  · have hy' : y ∈ Rset E s (i+1) := mem_Rset.2 hy
    rw [← h, mem_Rset] at hy'
    exact reachB_step hy' he

theorem Rset_stable {E : Fin m → Fin m → Bool} {s : Fin m} {i : ℕ}
    (h : Rset E s i = Rset E s (i+1)) : ∀ j, i ≤ j → Rset E s j = Rset E s (j+1) := by
  intro j hj
  induction j with
  | zero =>
      have : i = 0 := by omega
      subst this; exact h
  | succ j ih =>
      rcases Nat.lt_or_ge i (j+1) with h1 | h1
      · exact Rset_stable_step (ih (by omega))
      · have : i = j+1 := by omega
        subst this; exact h

theorem Rset_zero {E : Fin m → Fin m → Bool} {s : Fin m} : Rset E s 0 = {s.val} := by
  ext x
  simp [mem_Rset, reachB]

theorem Rcard_zero {E : Fin m → Fin m → Bool} {s : Fin m} : Rcard E s 0 = 1 := by
  simp [Rcard, Rset_zero]

theorem Rset_card_growth {E : Fin m → Fin m → Bool} {s : Fin m} :
    ∀ i, (∀ j, j < i → Rset E s j ≠ Rset E s (j+1)) → i + 1 ≤ (Rset E s i).card := by
  intro i
  induction i with
  | zero => intro _; simp [Rset_zero]
  | succ i ih =>
      intro h
      have h1 : i + 1 ≤ (Rset E s i).card := ih (fun j hj => h j (by omega))
      have h2 : (Rset E s i).card < (Rset E s (i+1)).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Rset_subset, h i (by omega)⟩)
      omega

theorem Rset_sat {E : Fin m → Fin m → Bool} {s : Fin m} : Rset E s m = Rset E s (m+1) := by
  by_cases h : ∀ j, j < m → Rset E s j ≠ Rset E s (j+1)
  · have h1 := Rset_card_growth m h
    have hle : (Rset E s m).card ≤ m := by
      calc (Rset E s m).card ≤ (Finset.range m).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
        _ = m := by simp
    omega
  · push_neg at h
    obtain ⟨j, hj, hje⟩ := h
    exact Rset_stable hje m (by omega)

theorem reachB_to_rtg {E : Fin m → Fin m → Bool} {s : Fin m} :
    ∀ (i x : ℕ) (h : reachB E s i x = true),
      Relation.ReflTransGen (fun a b : Fin m => E a b = true) s ⟨x, reachB_lt h⟩ := by
  intro i
  induction i with
  | zero =>
      intro x h
      simp [reachB] at h
      subst h
      exact Relation.ReflTransGen.refl
  | succ i ih =>
      intro x h
      rcases reachB_succ_cases h with h1 | ⟨y, hy, he⟩
      · have h2 := ih x h1
        convert h2 using 2
      · have h2 := ih y hy
        refine Relation.ReflTransGen.tail h2 ?_
        rw [show (⟨y, reachB_lt hy⟩ : Fin m) = ⟨y, (edgeB_lt he).1⟩ from rfl]
        rw [show (⟨x, reachB_lt h⟩ : Fin m) = ⟨x, (edgeB_lt he).2⟩ from rfl]
        rw [← edgeB_fin (E := E) ⟨y, (edgeB_lt he).1⟩ ⟨x, (edgeB_lt he).2⟩]
        exact he

theorem rtg_to_reachB {E : Fin m → Fin m → Bool} {s x : Fin m}
    (h : Relation.ReflTransGen (fun a b : Fin m => E a b = true) s x) :
    reachB E s m x.val = true := by
  induction h with
  | refl => exact reachB_le (Nat.zero_le _) reachB_zero
  | @tail b c _ hbc ih =>
      have h1 : reachB E s (m+1) c.val = true :=
        reachB_step ih (by rw [edgeB_fin]; exact hbc)
      have h2 : c.val ∈ Rset E s (m+1) := mem_Rset.2 h1
      rw [← Rset_sat, mem_Rset] at h2
      exact h2

/-- The `m+1`-st reachability layer is exactly the set of reachable vertices. -/
theorem reachB_succ_iff_rtg {E : Fin m → Fin m → Bool} {s x : Fin m} :
    reachB E s (m+1) x.val = true ↔
      Relation.ReflTransGen (fun a b : Fin m => E a b = true) s x := by
  constructor
  · intro h
    have := reachB_to_rtg (m+1) x.val h
    simpa using this
  · intro h
    exact reachB_succ (rtg_to_reachB h)

/-! ## The program -/

def setOne (x : Var) : Stmt := .seq (.zero x) (.incr x)

/-- One step of the guessed path: either guess the next vertex and check the edge, or stop
(by setting the length counter to its maximum). -/
def certBody : Stmt :=
  .ch (.seq (.guess vT) (.ite (.edg vW vT) (.seq (.cpy vW vT) (.incr vJ)) .fail))
      (.cpy vJ vI)

def certLoop : Stmt := .wh (.ltv vJ vI) certBody

/-- Certify that the vertex stored in `vU` lies in the `vI`-th reachability layer, by
guessing a path from `vS` of length at most `vI`. -/
def cert : Stmt :=
  .seq (.cpy vW vS) (.seq (.zero vJ) (.seq certLoop (.ite (.eqv vW vU) .skip .fail)))

/-- Body run for each certified vertex: raise the flag if it is `vV` or has an edge to `vV`. -/
def flagBody : Stmt :=
  .seq (.ite (.eqv vU vV) (setOne vF) .skip) (.ite (.edg vU vV) (setOne vF) .skip)

/-- One iteration of the counting loop: optionally certify the current vertex `vU` as
belonging to `R_{vI}`, counting it and running `flagBody` on it. -/
def countBody : Stmt :=
  .seq (.ch (.seq cert (.seq (.incr vCnt) flagBody)) .skip) (.incr vU)

def countLoop : Stmt := .wh (.isV vU) countBody

/-- Inductive counting: assuming `vC = |R_{vI}|`, decide whether `vV ∈ R_{vI + 1}`,
leaving the answer in `vF`. -/
def checkV : Stmt :=
  .seq (.zero vU) (.seq (.zero vCnt) (.seq (.zero vF)
    (.seq countLoop (.ite (.eqv vCnt vC) .skip .fail))))

/-- Compute `|R_{vI + 1}|` into `vC2`. -/
def vertexBody : Stmt :=
  .seq checkV (.seq (.ite (.eqv vF vZ) .skip (.incr vC2)) (.incr vV))

def vertexLoop : Stmt := .wh (.isV vV) vertexBody

def stepPhase : Stmt := .seq (.zero vC2) (.seq (.zero vV) vertexLoop)

/-- One iteration of the outer loop: replace `|R_{vI}|` by `|R_{vI+1}|`. -/
def layerBody : Stmt := .seq stepPhase (.seq (.cpy vC vC2) (.incr vI))

def layerLoop : Stmt := .wh (.isV vI) layerBody

/-- The complete nondeterministic log-space program deciding **non**-reachability of the
vertex in `vTgt` from the vertex in `vS`. -/
def nonReach : Stmt :=
  .seq (.zero vZ) (.seq (setOne vC) (.seq (.zero vI)
    (.seq layerLoop
      (.seq (.cpy vV vTgt) (.seq checkV (.ite (.eqv vF vZ) .skip .fail))))))

def initEnv (s t : Fin m) : Env :=
  fun x => if x = vS then s.val else if x = vTgt then t.val else 0

/-! ## Correctness of the certification gadget -/

theorem reachB_path {E : Fin m → Fin m → Bool} {s : Fin m} :
    ∀ (i x : ℕ), reachB E s i x = true →
      ∃ (n : ℕ) (f : ℕ → ℕ), n ≤ i ∧ f 0 = s.val ∧ f n = x ∧
        ∀ j < n, edgeB E (f j) (f (j+1)) = true := by
  intro i
  induction i with
  | zero =>
      intro x hx
      simp [reachB] at hx
      exact ⟨0, fun _ => s.val, le_rfl, rfl, hx.symm, by omega⟩
  | succ i ih =>
      intro x hx
      rcases reachB_succ_cases hx with h1 | ⟨y, hy, he⟩
      · obtain ⟨n, f, hn, hf0, hfn, hedge⟩ := ih x h1
        exact ⟨n, f, by omega, hf0, hfn, hedge⟩
      · obtain ⟨n, f, hn, hf0, hfn, hedge⟩ := ih y hy
        refine ⟨n + 1, fun j => if j ≤ n then f j else x, by omega, by simp [hf0], by simp, ?_⟩
        intro j hj
        rcases Nat.lt_or_ge j n with h | h
        · have h1 : j ≤ n := by omega
          have h2 : j + 1 ≤ n := by omega
          simp only [h1, h2, if_pos]
          exact hedge j h
        · have hjn : j = n := by omega
          subst hjn
          have h2 : ¬ (j + 1 ≤ j) := by omega
          simp only [le_refl, if_pos, h2, if_false]
          rw [hfn]
          exact he


theorem cert_sound {E : Fin m → Fin m → Bool} {s : Fin m} {i : ℕ} {e e' : Env}
    (hS : e vS = s.val) (hI : e vI = i) (h : Exec E cert e e') :
    reachB E s i (e vU) = true := by
  rw [cert] at h
  obtain ⟨a1, hc1, h⟩ := exec_seq_inv h
  obtain ⟨a2, hc2, h⟩ := exec_seq_inv h
  obtain ⟨a3, hloop, hfin⟩ := exec_seq_inv h
  rw [exec_cpy_inv hc1] at hc2
  rw [exec_zero_inv hc2] at hloop
  have key := wh_sound (E := E)
    (Inv := fun a => a vI = i ∧ a vS = s.val ∧ a vU = e vU ∧ a vJ ≤ i ∧
      reachB E s (a vJ) (a vW) = true) ?_ hloop ?_
  · obtain ⟨⟨hI3, hS3, hU3, hJ3, hR3⟩, _⟩ := key
    rcases exec_ite_inv hfin with ⟨hcc, hsk⟩ | ⟨_, hf⟩
    · have hwu : a3 vW = a3 vU := by simpa [evalCond] using hcc
      rw [exec_skip_inv hsk] at *
      rw [hwu, hU3] at hR3
      exact reachB_le hJ3 hR3
    · exact absurd hf (fun hh => exec_fail_inv hh)
  · rintro a a' ⟨hI1, hS1, hU1, hJ1, hR1⟩ hcond hbody
    have hlt : a vJ < a vI := by simpa [evalCond] using hcond
    rcases exec_ch_inv hbody with hL | hR
    · obtain ⟨b1, hg, hite⟩ := exec_seq_inv hL
      obtain ⟨k, hk, hb1⟩ := exec_guess_inv hg
      subst hb1
      rcases exec_ite_inv hite with ⟨hce, hbb⟩ | ⟨_, hf⟩
      · obtain ⟨b2, hcpy, hinc⟩ := exec_seq_inv hbb
        rw [exec_cpy_inv hcpy] at hinc
        obtain ⟨hlt2, hb2⟩ := exec_incr_inv hinc
        subst hb2
        have hedge : edgeB E (a vW) k = true := by
          simpa [evalCond] using hce
        refine ⟨by simp +decide [hI1], by simp +decide [hS1], by simp +decide [hU1],
          by simp +decide; omega, ?_⟩
        simp +decide
        exact reachB_step hR1 hedge
      · exact absurd hf (fun hh => exec_fail_inv hh)
    · rw [exec_cpy_inv hR]
      refine ⟨by simp +decide [hI1], by simp +decide [hS1], by simp +decide [hU1], ?_, ?_⟩
      · simp +decide [hI1]
      · simp +decide [hI1]
        exact reachB_le hJ1 hR1
  · refine ⟨by simp +decide [hI], by simp +decide [hS], by simp +decide, by simp +decide, ?_⟩
    simp +decide [hS]
    exact reachB_zero


/-- Completeness of the path-guessing loop. -/
theorem certLoop_complete {E : Fin m → Fin m → Bool} {i : ℕ} (hi : i ≤ m) :
    ∀ (n : ℕ) (f : ℕ → ℕ), (∀ j < n, edgeB E (f j) (f (j+1)) = true) →
      ∀ (a : Env), a vI = i → a vW = f 0 → a vJ + n ≤ i →
        ∃ a', Exec E certLoop a a' ∧ a' vW = f n := by
  intro n
  induction n with
  | zero =>
      intro f _ a hI hW hJ
      rcases Nat.lt_or_ge (a vJ) (a vI) with hlt | hge
      · refine ⟨upd a vJ (a vI), ?_, by simp +decide [hW]⟩
        refine Exec.whT (by simp +decide [evalCond, hlt]) (Exec.chR Exec.cpy) (Exec.whF ?_)
        simp +decide [evalCond]
      · exact ⟨a, Exec.whF (by simp +decide [evalCond]; omega), hW⟩
  | succ n ih =>
      intro f hf a hI hW hJ
      have hlt : a vJ < a vI := by omega
      have hedge : edgeB E (a vW) (f 1) = true := by rw [hW]; exact hf 0 (by omega)
      have hf1 : f 1 ≤ m := le_of_lt (edgeB_lt hedge).2
      have hbody : Exec E certBody a
          (upd (upd (upd a vT (f 1)) vW ((upd a vT (f 1)) vT)) vJ
            ((upd (upd a vT (f 1)) vW ((upd a vT (f 1)) vT)) vJ + 1)) := by
        refine Exec.chL (Exec.seq (Exec.guess hf1)
          (Exec.iteT ?_ (Exec.seq Exec.cpy (Exec.incr ?_))))
        · simpa +decide [evalCond] using hedge
        · simp +decide
          omega
      obtain ⟨a', hrun, hw'⟩ := ih (fun j => f (j+1)) (fun j hj => hf (j+1) (by omega))
        (upd (upd (upd a vT (f 1)) vW ((upd a vT (f 1)) vT)) vJ
            ((upd (upd a vT (f 1)) vW ((upd a vT (f 1)) vT)) vJ + 1))
        (by simp +decide [hI]) (by simp +decide) (by simp +decide; omega)
      exact ⟨a', Exec.whT (by simp +decide [evalCond, hlt]) hbody hrun, by simpa using hw'⟩

theorem cert_complete {E : Fin m → Fin m → Bool} {s : Fin m} {i : ℕ} {e : Env}
    (hS : e vS = s.val) (hI : e vI = i) (hi : i ≤ m)
    (hR : reachB E s i (e vU) = true) : ∃ e', Exec E cert e e' := by
  obtain ⟨n, f, hn, hf0, hfn, hedge⟩ := reachB_path i (e vU) hR
  obtain ⟨a3, hrun, hw3⟩ := certLoop_complete hi n f hedge (upd (upd e vW (e vS)) vJ 0)
    (by simp +decide [hI]) (by simp +decide [hS, hf0]) (by simp +decide; omega)
  have hU3 : a3 vU = (upd (upd e vW (e vS)) vJ 0) vU := exec_frame hrun vU (by decide)
  refine ⟨a3, Exec.seq Exec.cpy (Exec.seq Exec.zero (Exec.seq hrun (Exec.iteT ?_ Exec.skip)))⟩
  have : a3 vU = e vU := by rw [hU3]; simp +decide
  simp +decide [evalCond, hw3, this, hfn]

theorem reachB_succ_iff' {E : Fin m → Fin m → Bool} {s : Fin m} {i v : ℕ} :
    reachB E s (i+1) v = true ↔
      ∃ u, reachB E s i u = true ∧ (u = v ∨ edgeB E u v = true) := by
  constructor
  · intro h
    rcases reachB_succ_cases h with h1 | ⟨y, hy, he⟩
    · exact ⟨v, h1, Or.inl rfl⟩
    · exact ⟨y, hy, Or.inr he⟩
  · rintro ⟨u, hu, rfl | he⟩
    · exact reachB_succ hu
    · exact reachB_step hu he

theorem Rlt_succ {E : Fin m → Fin m → Bool} {s : Fin m} {i k : ℕ} :
    Rlt E s i (k+1) =
      if reachB E s i k = true then insert k (Rlt E s i k) else Rlt E s i k := by
  simp [Rlt, Finset.range_add_one, Finset.filter_insert]

theorem Rlt_card_succ_pos {E : Fin m → Fin m → Bool} {s : Fin m} {i k : ℕ}
    (h : reachB E s i k = true) : (Rlt E s i (k+1)).card = (Rlt E s i k).card + 1 := by
  rw [Rlt_succ, if_pos h, Finset.card_insert_of_notMem (by simp [mem_Rlt])]

theorem Rlt_card_succ_neg {E : Fin m → Fin m → Bool} {s : Fin m} {i k : ℕ}
    (h : ¬ reachB E s i k = true) : (Rlt E s i (k+1)).card = (Rlt E s i k).card := by
  rw [Rlt_succ, if_neg h]

theorem Rlt_m {E : Fin m → Fin m → Bool} {s : Fin m} {i : ℕ} : Rlt E s i m = Rset E s i := rfl

/-- Soundness of the flag-setting body. -/
theorem flagBody_sound {E : Fin m → Fin m → Bool} {a a' : Env} (h : Exec E flagBody a a') :
    ((a' vF ≠ 0) ↔ (a vF ≠ 0 ∨ a vU = a vV ∨ edgeB E (a vU) (a vV) = true)) ∧
      ∀ x, x ≠ vF → a' x = a x := by
  have hframe : ∀ x, x ≠ vF → a' x = a x := by
    intro x hx
    refine exec_frame h x ?_
    revert hx
    revert x
    decide
  refine ⟨?_, hframe⟩
  rw [flagBody] at h
  obtain ⟨b1, h1, h2⟩ := exec_seq_inv h
  have key : ∀ (c : Cond) (b b2 : Env), Exec E (.ite c (setOne vF) .skip) b b2 →
      (evalCond E c b = true → b2 vF = 1) ∧ (evalCond E c b = false → b2 = b) := by
    intro c b b2 hb
    rcases exec_ite_inv hb with ⟨hc, hs⟩ | ⟨hc, hs⟩
    · refine ⟨fun _ => ?_, fun hcf => by rw [hc] at hcf; exact absurd hcf (by simp)⟩
      obtain ⟨b3, hz, hi⟩ := exec_seq_inv hs
      rw [exec_zero_inv hz] at hi
      obtain ⟨_, hb2⟩ := exec_incr_inv hi
      rw [hb2]
      simp
    · refine ⟨fun hct => by rw [hc] at hct; exact absurd hct (by simp), fun _ => ?_⟩
      exact exec_skip_inv hs
  obtain ⟨k1t, k1f⟩ := key _ _ _ h1
  obtain ⟨k2t, k2f⟩ := key _ _ _ h2
  have hb1U : b1 vU = a vU := by
    rcases Bool.eq_false_or_eq_true (evalCond E (.eqv vU vV) a) with hc | hc
    · exact exec_frame h1 vU (by decide)
    · rw [k1f hc]
  have hb1V : b1 vV = a vV := exec_frame h1 vV (by decide)
  constructor
  · intro hne
    rcases Bool.eq_false_or_eq_true (evalCond E (.eqv vU vV) a) with hc1 | hc1
    · exact Or.inr (Or.inl (by simpa [evalCond] using hc1))
    · rcases Bool.eq_false_or_eq_true (evalCond E (.edg vU vV) b1) with hc2 | hc2
      · have hc2' : edgeB E (a vU) (a vV) = true := by
          simp only [evalCond] at hc2
          rwa [hb1U, hb1V] at hc2
        exact Or.inr (Or.inr hc2')
      · rw [k2f hc2, k1f hc1] at hne
        exact Or.inl hne
  · intro hor
    rcases Bool.eq_false_or_eq_true (evalCond E (.edg vU vV) b1) with hc2 | hc2
    · rw [k2t hc2]
      simp
    · rcases Bool.eq_false_or_eq_true (evalCond E (.eqv vU vV) a) with hc1 | hc1
      · rw [k2f hc2, k1t hc1]
        simp
      · rw [k2f hc2, k1f hc1]
        rcases hor with h' | h' | h'
        · exact h'
        · exact absurd h' (by simpa [evalCond] using hc1)
        · have hc2' : edgeB E (a vU) (a vV) = false := by
            simp only [evalCond] at hc2
            rwa [hb1U, hb1V] at hc2
          rw [hc2'] at h'
          exact absurd h' (by simp)

theorem flagBody_complete {E : Fin m → Fin m → Bool} (hm : 0 < m) (a : Env) :
    ∃ a', Exec E flagBody a a' := by
  have key : ∀ (c : Cond) (b : Env), ∃ b', Exec E (.ite c (setOne vF) .skip) b b' := by
    intro c b
    rcases Bool.eq_false_or_eq_true (evalCond E c b) with hc | hc
    · exact ⟨upd (upd b vF 0) vF ((upd b vF 0) vF + 1),
        Exec.iteT hc (Exec.seq Exec.zero (Exec.incr (by simpa using hm)))⟩
    · exact ⟨b, Exec.iteF hc Exec.skip⟩
  obtain ⟨b1, h1⟩ := key (.eqv vU vV) a
  obtain ⟨b2, h2⟩ := key (.edg vU vV) b1
  exact ⟨b2, Exec.seq h1 h2⟩

theorem Rlt_card_mono {E : Fin m → Fin m → Bool} {s : Fin m} {i k : ℕ} :
    (Rlt E s i k).card ≤ (Rlt E s i (k+1)).card := by
  by_cases h : reachB E s i k = true
  · rw [Rlt_card_succ_pos h]; omega
  · rw [Rlt_card_succ_neg h]

/-- Soundness of the inductive-counting subroutine. -/
theorem checkV_sound {E : Fin m → Fin m → Bool} {s : Fin m} {i v : ℕ} {e e' : Env}
    (hI : e vI = i) (hS : e vS = s.val) (hV : e vV = v) (hC : e vC = Rcard E s i)
    (h : Exec E checkV e e') :
    (e' vF ≠ 0) ↔ reachB E s (i+1) v = true := by
  rw [checkV] at h
  obtain ⟨a1, hz1, h⟩ := exec_seq_inv h
  obtain ⟨a2, hz2, h⟩ := exec_seq_inv h
  obtain ⟨a3, hz3, h⟩ := exec_seq_inv h
  obtain ⟨a4, hloop, hfin⟩ := exec_seq_inv h
  rw [exec_zero_inv hz1] at hz2
  rw [exec_zero_inv hz2] at hz3
  rw [exec_zero_inv hz3] at hloop
  have key := wh_sound (E := E)
    (Inv := fun a => a vI = i ∧ a vS = s.val ∧ a vV = v ∧ a vC = e vC ∧ a vU ≤ m ∧
      a vCnt ≤ (Rlt E s i (a vU)).card ∧
      (a vF ≠ 0 → ∃ u, reachB E s i u = true ∧ (u = v ∨ edgeB E u v = true)) ∧
      (a vCnt = (Rlt E s i (a vU)).card → ∀ u, u < a vU → reachB E s i u = true →
        (u = v ∨ edgeB E u v = true) → a vF ≠ 0)) ?_ hloop ?_
  · obtain ⟨⟨hI4, hS4, hV4, hC4, hU4, hCnt4, hFa, hFb⟩, hcond⟩ := key
    have hUm : a4 vU = m := by
      have : ¬ (a4 vU < m) := by simpa [evalCond] using hcond
      omega
    rcases exec_ite_inv hfin with ⟨hcc, hsk⟩ | ⟨_, hf⟩
    · rw [exec_skip_inv hsk]
      have hcnt : a4 vCnt = a4 vC := by simpa [evalCond] using hcc
      rw [hC4, hC] at hcnt
      have hfull : a4 vCnt = (Rlt E s i (a4 vU)).card := by
        rw [hcnt, hUm]
        rfl
      rw [reachB_succ_iff']
      constructor
      · exact hFa
      · rintro ⟨u, hu, htest⟩
        exact hFb hfull u (by rw [hUm]; exact reachB_lt hu) hu htest
    · exact absurd hf (fun hh => exec_fail_inv hh)
  · -- the loop body preserves the invariant
    rintro a a' ⟨hI1, hS1, hV1, hC1, hU1, hCnt1, hFa1, hFb1⟩ hcond hbody
    have hUlt : a vU < m := by simpa [evalCond] using hcond
    rw [countBody] at hbody
    obtain ⟨b, hb, hinc⟩ := exec_seq_inv hbody
    obtain ⟨hbUlt, ha'⟩ := exec_incr_inv hinc
    rcases exec_ch_inv hb with hL | hR
    · -- the vertex `a vU` is certified
      obtain ⟨c1, hcert, hrest⟩ := exec_seq_inv hL
      obtain ⟨c2, hcnt, hflag⟩ := exec_seq_inv hrest
      have hreach : reachB E s i (a vU) = true := cert_sound hS1 hI1 hcert
      have hc1 : ∀ x, x ∉ ({vW, vJ, vT} : Finset Var) → c1 x = a x := by
        intro x hx
        refine exec_frame hcert x ?_
        revert hx
        revert x
        decide
      obtain ⟨hltc, hc2eq⟩ := exec_incr_inv hcnt
      obtain ⟨hflagiff, hflagframe⟩ := flagBody_sound hflag
      have hc2 : ∀ x, x ≠ vCnt → c2 x = c1 x := by
        intro x hx
        rw [hc2eq]
        exact upd_ne _ _ hx
      have hbU : b vU = a vU := by
        rw [hflagframe vU (by decide), hc2 vU (by decide), hc1 vU (by decide)]
      have hbV : b vV = v := by
        rw [hflagframe vV (by decide), hc2 vV (by decide), hc1 vV (by decide), hV1]
      have hbI : b vI = i := by
        rw [hflagframe vI (by decide), hc2 vI (by decide), hc1 vI (by decide), hI1]
      have hbS : b vS = s.val := by
        rw [hflagframe vS (by decide), hc2 vS (by decide), hc1 vS (by decide), hS1]
      have hbC : b vC = e vC := by
        rw [hflagframe vC (by decide), hc2 vC (by decide), hc1 vC (by decide), hC1]
      have hbCnt : b vCnt = a vCnt + 1 := by
        rw [hflagframe vCnt (by decide), hc2eq]
        simp [hc1 vCnt (by decide)]
      have hc2U : c2 vU = a vU := by rw [hc2 vU (by decide), hc1 vU (by decide)]
      have hc2V : c2 vV = v := by rw [hc2 vV (by decide), hc1 vV (by decide), hV1]
      have hc2F : c2 vF = a vF := by rw [hc2 vF (by decide), hc1 vF (by decide)]
      have hcardsucc : (Rlt E s i (a vU + 1)).card = (Rlt E s i (a vU)).card + 1 :=
        Rlt_card_succ_pos hreach
      subst ha'
      refine ⟨by simp +decide [hbI], by simp +decide [hbS], by simp +decide [hbV],
        by simp +decide [hbC], by simp +decide [hbU]; omega, ?_, ?_, ?_⟩
      · simp +decide [hbCnt, hbU, hcardsucc]
        omega
      · intro hne
        simp +decide at hne
        rcases hflagiff.1 hne with h' | h' | h'
        · exact hFa1 (by rwa [hc2F] at h')
        · exact ⟨a vU, hreach, Or.inl (by rw [← hc2U, ← hc2V]; exact h')⟩
        · exact ⟨a vU, hreach, Or.inr (by rw [← hc2U, ← hc2V]; exact h')⟩
      · intro heq u hu hru htest
        simp +decide [hbCnt, hbU, hcardsucc] at heq
        have heq' : a vCnt = (Rlt E s i (a vU)).card := by omega
        simp +decide
        rcases Nat.lt_or_ge u (a vU) with hlt | hge
        · refine hflagiff.2 (Or.inl ?_)
          rw [hc2F]
          exact hFb1 heq' u hlt hru htest
        · have : u = a vU := by
            have : u < a vU + 1 := by simpa [hbU] using hu
            omega
          subst this
          rcases htest with h' | h'
          · exact hflagiff.2 (Or.inr (Or.inl (by rw [hc2U, hc2V]; exact h')))
          · exact hflagiff.2 (Or.inr (Or.inr (by rw [hc2U, hc2V]; exact h')))
    · -- the vertex `a vU` is skipped
      have hba : a = b := (exec_skip_inv hR).symm
      subst hba
      subst ha'
      refine ⟨by simp +decide [hI1], by simp +decide [hS1], by simp +decide [hV1],
        by simp +decide [hC1], by simp +decide; omega, ?_, ?_, ?_⟩
      · simp +decide
        exact le_trans hCnt1 Rlt_card_mono
      · intro hne
        simp +decide at hne
        exact hFa1 hne
      · intro heq u hu hru htest
        simp +decide at heq hu ⊢
        have hmono := Rlt_card_mono (E := E) (s := s) (i := i) (k := a vU)
        have hnr : ¬ reachB E s i (a vU) = true := by
          intro hr
          rw [Rlt_card_succ_pos hr] at heq
          omega
        have heq' : a vCnt = (Rlt E s i (a vU)).card := by
          rw [Rlt_card_succ_neg hnr] at heq
          exact heq
        have hlt : u < a vU := by
          rcases Nat.lt_or_ge u (a vU) with h' | h'
          · exact h'
          · have : u = a vU := by omega
            subst this
            exact absurd hru hnr
        exact hFb1 heq' u hlt hru htest
  · -- the invariant holds initially
    refine ⟨by simp +decide [hI], by simp +decide [hS], by simp +decide [hV],
      by simp +decide, by simp +decide, ?_, ?_, ?_⟩
    · simp +decide [Rlt]
    · simp +decide
    · intro _ u hu
      simp +decide at hu

theorem Rlt_card_le {E : Fin m → Fin m → Bool} {s : Fin m} {i k : ℕ} :
    (Rlt E s i k).card ≤ k := by
  calc (Rlt E s i k).card ≤ (Finset.range k).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = k := by simp

theorem Rlt_zero {E : Fin m → Fin m → Bool} {s : Fin m} {i : ℕ} : (Rlt E s i 0).card = 0 := by
  simp [Rlt]

/-- Completeness of the counting loop: certifying exactly the vertices of `R_i` gives a
successful run. -/
theorem countLoop_complete {E : Fin m → Fin m → Bool} {s : Fin m} {i : ℕ} (hi : i ≤ m) :
    ∀ (d : ℕ) (a : Env), m - a vU = d → a vU ≤ m → a vI = i → a vS = s.val →
      a vCnt = (Rlt E s i (a vU)).card →
      ∃ a', Exec E countLoop a a' ∧ a' vU = m ∧ a' vCnt = (Rlt E s i m).card := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro a hd hUm hI hS hCnt
    rcases Nat.lt_or_ge (a vU) m with hlt | hge
    · -- one more iteration
      have hbody : ∃ a', Exec E countBody a a' ∧ a' vU = a vU + 1 ∧
          a' vCnt = (Rlt E s i (a vU + 1)).card := by
        by_cases hr : reachB E s i (a vU) = true
        · obtain ⟨c1, hcert⟩ := cert_complete hS hI hi hr
          have hc1 : ∀ x, x ∉ ({vW, vJ, vT} : Finset Var) → c1 x = a x := by
            intro x hx
            refine exec_frame hcert x ?_
            revert hx; revert x; decide
          have hc1Cnt : c1 vCnt = a vCnt := hc1 vCnt (by decide)
          have hcltm : c1 vCnt < m := by
            rw [hc1Cnt, hCnt]
            exact lt_of_le_of_lt Rlt_card_le hlt
          obtain ⟨b, hfb⟩ := flagBody_complete (lt_of_le_of_lt (Nat.zero_le _) hlt)
            (upd c1 vCnt (c1 vCnt + 1))
          obtain ⟨_, hframe⟩ := flagBody_sound hfb
          have hbU : b vU = a vU := by
            rw [hframe vU (by decide), upd_ne _ _ (by decide), hc1 vU (by decide)]
          have hbCnt : b vCnt = a vCnt + 1 := by
            rw [hframe vCnt (by decide)]
            simp [hc1Cnt]
          refine ⟨upd b vU (b vU + 1), Exec.seq (Exec.chL (Exec.seq hcert
            (Exec.seq (Exec.incr hcltm) hfb))) (Exec.incr (by rw [hbU]; exact hlt)), ?_, ?_⟩
          · simp [hbU]
          · rw [upd_ne _ _ (by decide), hbCnt, hCnt, Rlt_card_succ_pos hr]
        · refine ⟨upd a vU (a vU + 1),
            Exec.seq (Exec.chR Exec.skip) (Exec.incr hlt), by simp, ?_⟩
          rw [upd_ne _ _ (by decide), hCnt, Rlt_card_succ_neg hr]
      obtain ⟨a1, hrun1, hU1, hCnt1⟩ := hbody
      have hI1 : a1 vI = i := by rw [exec_frame hrun1 vI (by decide), hI]
      have hS1 : a1 vS = s.val := by rw [exec_frame hrun1 vS (by decide), hS]
      obtain ⟨a', hrun', hU', hCnt'⟩ := ih (m - a1 vU) (by omega) a1 rfl (by omega) hI1 hS1
        (by rw [hCnt1, hU1])
      exact ⟨a', Exec.whT (by simp [evalCond, hlt]) hrun1 hrun', hU', hCnt'⟩
    · have hUm' : a vU = m := by omega
      refine ⟨a, Exec.whF (by simp [evalCond]; omega), hUm', ?_⟩
      rw [hCnt, hUm']

theorem checkV_complete {E : Fin m → Fin m → Bool} {s : Fin m} {i : ℕ} {e : Env}
    (hI : e vI = i) (hS : e vS = s.val) (hC : e vC = Rcard E s i) (hi : i ≤ m) :
    ∃ e', Exec E checkV e e' := by
  obtain ⟨a4, hrun, hU4, hCnt4⟩ := countLoop_complete (E := E) (s := s) hi
    (m - (upd (upd (upd e vU 0) vCnt 0) vF 0) vU) (upd (upd (upd e vU 0) vCnt 0) vF 0) rfl
    (by simp +decide) (by simp +decide [hI]) (by simp +decide [hS])
    (by simp +decide [Rlt_zero])
  have hC4 : a4 vC = Rcard E s i := by
    rw [exec_frame hrun vC (by decide)]
    simp +decide [hC]
  refine ⟨a4, Exec.seq Exec.zero (Exec.seq Exec.zero (Exec.seq Exec.zero
    (Exec.seq hrun (Exec.iteT ?_ Exec.skip))))⟩
  simp [evalCond, hCnt4, hC4, Rcard, Rset]

/-- Soundness of the layer-counting phase. -/
theorem stepPhase_sound {E : Fin m → Fin m → Bool} {s : Fin m} {i : ℕ} {e e' : Env}
    (hI : e vI = i) (hS : e vS = s.val) (hC : e vC = Rcard E s i) (hZ : e vZ = 0)
    (h : Exec E stepPhase e e') : e' vC2 = Rcard E s (i+1) := by
  rw [stepPhase] at h
  obtain ⟨a1, hz1, h⟩ := exec_seq_inv h
  obtain ⟨a2, hz2, hloop⟩ := exec_seq_inv h
  rw [exec_zero_inv hz1] at hz2
  rw [exec_zero_inv hz2] at hloop
  have key := wh_sound (E := E)
    (Inv := fun a => a vI = i ∧ a vS = s.val ∧ a vC = Rcard E s i ∧ a vZ = 0 ∧ a vV ≤ m ∧
      a vC2 = (Rlt E s (i+1) (a vV)).card) ?_ hloop ?_
  · obtain ⟨⟨_, _, _, _, hVm, hC2⟩, hcond⟩ := key
    have hVm' : e' vV = m := by
      have : ¬ (e' vV < m) := by simpa [evalCond] using hcond
      omega
    rw [hC2, hVm']
    rfl
  · rintro a a' ⟨hI1, hS1, hC1, hZ1, hV1, hC21⟩ hcond hbody
    have hVlt : a vV < m := by simpa [evalCond] using hcond
    rw [vertexBody] at hbody
    obtain ⟨b, hchk, hrest⟩ := exec_seq_inv hbody
    obtain ⟨c, hite, hinc⟩ := exec_seq_inv hrest
    have hbI : b vI = i := by rw [exec_frame hchk vI (by decide), hI1]
    have hbS : b vS = s.val := by rw [exec_frame hchk vS (by decide), hS1]
    have hbV : b vV = a vV := exec_frame hchk vV (by decide)
    have hbC : b vC = Rcard E s i := by rw [exec_frame hchk vC (by decide), hC1]
    have hbZ : b vZ = 0 := by rw [exec_frame hchk vZ (by decide), hZ1]
    have hbC2 : b vC2 = (Rlt E s (i+1) (a vV)).card := by
      rw [exec_frame hchk vC2 (by decide), hC21]
    have hflag : (b vF ≠ 0) ↔ reachB E s (i+1) (a vV) = true :=
      checkV_sound hI1 hS1 rfl hC1 hchk
    obtain ⟨hltv, hc'⟩ := exec_incr_inv hinc
    have hcC2 : c vC2 = (Rlt E s (i+1) (a vV + 1)).card ∧ c vV = a vV ∧ c vI = i ∧
        c vS = s.val ∧ c vC = Rcard E s i ∧ c vZ = 0 := by
      rcases exec_ite_inv hite with ⟨hcc, hsk⟩ | ⟨hcc, hin⟩
      · -- flag is zero: the vertex is not in the next layer
        have hb0 : b vF = 0 := by
          have : b vF = b vZ := by simpa [evalCond] using hcc
          rw [this, hbZ]
        have hnr : ¬ reachB E s (i+1) (a vV) = true := by
          intro hr
          exact absurd hb0 (hflag.2 hr)
        rw [exec_skip_inv hsk]
        refine ⟨?_, hbV, hbI, hbS, hbC, hbZ⟩
        rw [hbC2, Rlt_card_succ_neg hnr]
      · have hb0 : b vF ≠ 0 := by
          intro h0
          have : ¬ (b vF = b vZ) := by simpa [evalCond] using hcc
          exact this (by rw [h0, hbZ])
        have hr : reachB E s (i+1) (a vV) = true := hflag.1 hb0
        obtain ⟨_, hc⟩ := exec_incr_inv hin
        rw [hc]
        refine ⟨?_, by simp +decide [hbV], by simp +decide [hbI], by simp +decide [hbS],
          by simp +decide [hbC], by simp +decide [hbZ]⟩
        simp +decide [hbC2, Rlt_card_succ_pos hr]
    obtain ⟨hcC2', hcV, hcI, hcS, hcC, hcZ⟩ := hcC2
    rw [hc']
    refine ⟨by simp +decide [hcI], by simp +decide [hcS], by simp +decide [hcC],
      by simp +decide [hcZ], by simp +decide [hcV]; omega, ?_⟩
    simp +decide [hcV, hcC2']
  · refine ⟨by simp +decide [hI], by simp +decide [hS], by simp +decide [hC],
      by simp +decide [hZ], by simp +decide, by simp +decide [Rlt]⟩

/-- Completeness of the vertex loop of the layer-counting phase. -/
theorem vertexLoop_complete {E : Fin m → Fin m → Bool} {s : Fin m} {i : ℕ} (hi : i ≤ m) :
    ∀ (d : ℕ) (a : Env), m - a vV = d → a vV ≤ m → a vI = i → a vS = s.val →
      a vC = Rcard E s i → a vZ = 0 → a vC2 = (Rlt E s (i+1) (a vV)).card →
      ∃ a', Exec E vertexLoop a a' ∧ a' vC2 = Rcard E s (i+1) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro a hd hVm hI hS hC hZ hC2
    rcases Nat.lt_or_ge (a vV) m with hlt | hge
    · obtain ⟨b, hchk⟩ := checkV_complete hI hS hC hi
      have hflag : (b vF ≠ 0) ↔ reachB E s (i+1) (a vV) = true :=
        checkV_sound hI hS rfl hC hchk
      have hbI : b vI = i := by rw [exec_frame hchk vI (by decide), hI]
      have hbS : b vS = s.val := by rw [exec_frame hchk vS (by decide), hS]
      have hbV : b vV = a vV := exec_frame hchk vV (by decide)
      have hbC : b vC = Rcard E s i := by rw [exec_frame hchk vC (by decide), hC]
      have hbZ : b vZ = 0 := by rw [exec_frame hchk vZ (by decide), hZ]
      have hbC2 : b vC2 = (Rlt E s (i+1) (a vV)).card := by
        rw [exec_frame hchk vC2 (by decide), hC2]
      have hstep : ∃ c, Exec E (.ite (.eqv vF vZ) .skip (.incr vC2)) b c ∧
          c vC2 = (Rlt E s (i+1) (a vV + 1)).card ∧ c vV = a vV ∧ c vI = i ∧ c vS = s.val ∧
          c vC = Rcard E s i ∧ c vZ = 0 := by
        rcases Bool.eq_false_or_eq_true (evalCond E (.eqv vF vZ) b) with hcc | hcc
        · have hb0 : b vF = 0 := by
            have : b vF = b vZ := by simpa [evalCond] using hcc
            rw [this, hbZ]
          have hnr : ¬ reachB E s (i+1) (a vV) = true := by
            intro hr
            exact absurd hb0 (hflag.2 hr)
          exact ⟨b, Exec.iteT hcc Exec.skip, by rw [hbC2, Rlt_card_succ_neg hnr], hbV, hbI,
            hbS, hbC, hbZ⟩
        · have hb0 : b vF ≠ 0 := by
            intro h0
            have : ¬ (b vF = b vZ) := by simpa [evalCond] using hcc
            exact this (by rw [h0, hbZ])
          have hr : reachB E s (i+1) (a vV) = true := hflag.1 hb0
          have hlt2 : b vC2 < m := by
            rw [hbC2]
            exact lt_of_le_of_lt Rlt_card_le hlt
          refine ⟨upd b vC2 (b vC2 + 1), Exec.iteF hcc (Exec.incr hlt2), ?_,
            by simp +decide [hbV], by simp +decide [hbI], by simp +decide [hbS],
            by simp +decide [hbC], by simp +decide [hbZ]⟩
          simp +decide [hbC2, Rlt_card_succ_pos hr]
      obtain ⟨c, hite, hcC2, hcV, hcI, hcS, hcC, hcZ⟩ := hstep
      have hcVlt : c vV < m := by rw [hcV]; exact hlt
      refine ?_
      obtain ⟨a', hrun', hC2'⟩ := ih (m - (a vV + 1)) (by omega) (upd c vV (c vV + 1))
        (by simp +decide [hcV]) (by simp +decide [hcV]; omega) (by simp +decide [hcI])
        (by simp +decide [hcS]) (by simp +decide [hcC]) (by simp +decide [hcZ])
        (by simp +decide [hcV, hcC2])
      refine ⟨a', Exec.whT (by simp [evalCond, hlt]) ?_ hrun', hC2'⟩
      rw [vertexBody]
      exact Exec.seq hchk (Exec.seq hite (Exec.incr hcVlt))
    · have hVm' : a vV = m := by omega
      refine ⟨a, Exec.whF (by simp [evalCond]; omega), ?_⟩
      rw [hC2, hVm']
      rfl

theorem stepPhase_complete {E : Fin m → Fin m → Bool} {s : Fin m} {i : ℕ} {e : Env}
    (hI : e vI = i) (hS : e vS = s.val) (hC : e vC = Rcard E s i) (hZ : e vZ = 0)
    (hi : i ≤ m) : ∃ e', Exec E stepPhase e e' := by
  obtain ⟨a', hrun, _⟩ := vertexLoop_complete (E := E) (s := s) hi
    (m - (upd (upd e vC2 0) vV 0) vV) (upd (upd e vC2 0) vV 0) rfl (by simp +decide)
    (by simp +decide [hI]) (by simp +decide [hS]) (by simp +decide [hC])
    (by simp +decide [hZ]) (by simp +decide [Rlt])
  exact ⟨a', Exec.seq Exec.zero (Exec.seq Exec.zero hrun)⟩

/-- Soundness of the outer loop: on exit `vC` holds `|R_m|`. -/
theorem layerLoop_sound {E : Fin m → Fin m → Bool} {s : Fin m} {a a' : Env}
    (hZ : a vZ = 0) (hS : a vS = s.val) (hI : a vI = 0) (hC : a vC = Rcard E s 0)
    (h : Exec E layerLoop a a') :
    a' vI = m ∧ a' vC = Rcard E s m := by
  have key := wh_sound (E := E)
    (Inv := fun b => b vZ = 0 ∧ b vS = s.val ∧ b vI ≤ m ∧ b vC = Rcard E s (b vI)) ?_ h ?_
  · obtain ⟨⟨_, _, hIm, hC'⟩, hcond⟩ := key
    have hIm' : a' vI = m := by
      have : ¬ (a' vI < m) := by simpa [evalCond] using hcond
      omega
    exact ⟨hIm', by rw [hC', hIm']⟩
  · rintro b b' ⟨hZ1, hS1, hI1, hC1⟩ hcond hbody
    have hIlt : b vI < m := by simpa [evalCond] using hcond
    rw [layerBody] at hbody
    obtain ⟨c, hstep, hrest⟩ := exec_seq_inv hbody
    obtain ⟨c2, hcpy, hinc⟩ := exec_seq_inv hrest
    have hcC2 : c vC2 = Rcard E s (b vI + 1) := stepPhase_sound rfl hS1 hC1 hZ1 hstep
    have hcZ : c vZ = 0 := by rw [exec_frame hstep vZ (by decide), hZ1]
    have hcS : c vS = s.val := by rw [exec_frame hstep vS (by decide), hS1]
    have hcI : c vI = b vI := exec_frame hstep vI (by decide)
    rw [exec_cpy_inv hcpy] at hinc
    obtain ⟨hlt2, hb'⟩ := exec_incr_inv hinc
    rw [hb']
    refine ⟨by simp +decide [hcZ], by simp +decide [hcS], ?_, ?_⟩
    · simp +decide [hcI]
      omega
    · simp +decide [hcI, hcC2]
  · exact ⟨hZ, hS, by omega, by rw [hC, hI]⟩

theorem layerLoop_complete {E : Fin m → Fin m → Bool} {s : Fin m} :
    ∀ (d : ℕ) (a : Env), m - a vI = d → a vI ≤ m → a vZ = 0 → a vS = s.val →
      a vC = Rcard E s (a vI) → ∃ a', Exec E layerLoop a a' := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro a hd hIm hZ hS hC
    rcases Nat.lt_or_ge (a vI) m with hlt | hge
    · obtain ⟨c, hstep⟩ := stepPhase_complete rfl hS hC hZ (le_of_lt hlt)
      have hcC2 : c vC2 = Rcard E s (a vI + 1) := stepPhase_sound rfl hS hC hZ hstep
      have hcZ : c vZ = 0 := by rw [exec_frame hstep vZ (by decide), hZ]
      have hcS : c vS = s.val := by rw [exec_frame hstep vS (by decide), hS]
      have hcI : c vI = a vI := exec_frame hstep vI (by decide)
      have hcIlt : (upd c vC (c vC2)) vI < m := by simp +decide [hcI]; exact hlt
      obtain ⟨a', hrun⟩ := ih (m - (a vI + 1)) (by omega)
        (upd (upd c vC (c vC2)) vI ((upd c vC (c vC2)) vI + 1)) (by simp +decide [hcI])
        (by simp +decide [hcI]; omega) (by simp +decide [hcZ]) (by simp +decide [hcS])
        (by simp +decide [hcI, hcC2])
      exact ⟨a', Exec.whT (by simp [evalCond, hlt])
        (Exec.seq hstep (Exec.seq Exec.cpy (Exec.incr hcIlt))) hrun⟩
    · exact ⟨a, Exec.whF (by simp [evalCond]; omega)⟩

/-! ## Main theorem -/

/-- **Immerman–Szelepcsényi.**  A single fixed nondeterministic program using a constant
number of variables, each holding a value at most `m`, accepts exactly when the target
vertex is *not* reachable from the source in the `m`-vertex graph `E`.  Since the
configuration graph of a nondeterministic `O(log n)`-space machine has polynomially many
vertices, this says `NL = coNL`. -/
theorem immerman_szelepcsenyi {m : ℕ} (E : Fin m → Fin m → Bool) (s t : Fin m) :
    (∃ e, Exec E nonReach (initEnv s t) e) ↔
      ¬ Relation.ReflTransGen (fun a b => E a b = true) s t := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) s.isLt
  -- the state after the three initialisations
  set a3 : Env := upd (upd (upd (upd (initEnv s t) vZ 0) vC 0) vC
    ((upd (upd (initEnv s t) vZ 0) vC 0) vC + 1)) vI 0 with ha3
  have h3Z : a3 vZ = 0 := by simp +decide [ha3]
  have h3S : a3 vS = s.val := by simp +decide [ha3, initEnv]
  have h3T : a3 vTgt = t.val := by simp +decide [ha3, initEnv]
  have h3I : a3 vI = 0 := by simp +decide [ha3]
  have h3C : a3 vC = Rcard E s 0 := by simp +decide [ha3, Rcard_zero]
  constructor
  · rintro ⟨e', hrun⟩
    rw [nonReach] at hrun
    obtain ⟨b1, hb1, hrun⟩ := exec_seq_inv hrun
    obtain ⟨b2, hb2, hrun⟩ := exec_seq_inv hrun
    obtain ⟨b3, hb3, hrun⟩ := exec_seq_inv hrun
    obtain ⟨b4, hloop, hrun⟩ := exec_seq_inv hrun
    obtain ⟨b5, hcpy, hrun⟩ := exec_seq_inv hrun
    obtain ⟨b6, hchk, hfin⟩ := exec_seq_inv hrun
    -- identify `b3` with `a3`
    have hb3eq : b3 = a3 := by
      rw [exec_zero_inv hb1] at hb2
      obtain ⟨c, hz, hi⟩ := exec_seq_inv hb2
      rw [exec_zero_inv hz] at hi
      obtain ⟨_, hb2'⟩ := exec_incr_inv hi
      rw [hb2'] at hb3
      rw [exec_zero_inv hb3, ha3]
    subst hb3eq
    obtain ⟨h4I, h4C⟩ := layerLoop_sound h3Z h3S h3I h3C hloop
    have h4Z : b4 vZ = 0 := by rw [exec_frame hloop vZ (by decide), h3Z]
    have h4S : b4 vS = s.val := by rw [exec_frame hloop vS (by decide), h3S]
    have h4T : b4 vTgt = t.val := by rw [exec_frame hloop vTgt (by decide), h3T]
    rw [exec_cpy_inv hcpy] at hchk
    have hflag : (b6 vF ≠ 0) ↔ reachB E s (m+1) t.val = true :=
      checkV_sound (by simp +decide [h4I]) (by simp +decide [h4S]) (by simp +decide [h4T])
        (by simp +decide [h4C]) hchk
    have h6Z : b6 vZ = 0 := by
      rw [exec_frame hchk vZ (by decide)]
      simp +decide [h4Z]
    rcases exec_ite_inv hfin with ⟨hcc, _⟩ | ⟨_, hf⟩
    · have h6F : b6 vF = 0 := by
        have : b6 vF = b6 vZ := by simpa [evalCond] using hcc
        rw [this, h6Z]
      intro hrtg
      exact (hflag.2 (reachB_succ_iff_rtg.2 hrtg)) h6F
    · exact absurd hf (fun hh => exec_fail_inv hh)
  · intro hnr
    obtain ⟨b4, hloop⟩ := layerLoop_complete (E := E) (s := s) (m - a3 vI) a3 rfl
      (by omega) h3Z h3S (by rw [h3C, h3I])
    obtain ⟨h4I, h4C⟩ := layerLoop_sound h3Z h3S h3I h3C hloop
    have h4Z : b4 vZ = 0 := by rw [exec_frame hloop vZ (by decide), h3Z]
    have h4S : b4 vS = s.val := by rw [exec_frame hloop vS (by decide), h3S]
    have h4T : b4 vTgt = t.val := by rw [exec_frame hloop vTgt (by decide), h3T]
    obtain ⟨b6, hchk⟩ := checkV_complete (E := E) (s := s) (i := m)
      (e := upd b4 vV (b4 vTgt)) (by simp +decide [h4I]) (by simp +decide [h4S])
      (by simp +decide [h4C]) le_rfl
    have hflag : (b6 vF ≠ 0) ↔ reachB E s (m+1) t.val = true :=
      checkV_sound (by simp +decide [h4I]) (by simp +decide [h4S]) (by simp +decide [h4T])
        (by simp +decide [h4C]) hchk
    have h6Z : b6 vZ = 0 := by
      rw [exec_frame hchk vZ (by decide)]
      simp +decide [h4Z]
    have h6F : b6 vF = 0 := by
      by_contra hne
      exact hnr (reachB_succ_iff_rtg.1 (hflag.1 hne))
    refine ⟨b6, ?_⟩
    rw [nonReach]
    obtain ⟨d1, hd1, d2, hd2, hd3⟩ :
        ∃ d1, Exec E (.zero vZ) (initEnv s t) d1 ∧ ∃ d2, Exec E (setOne vC) d1 d2 ∧
          Exec E (.zero vI) d2 a3 :=
      ⟨_, Exec.zero, _, Exec.seq Exec.zero (Exec.incr (by simpa using hm)), Exec.zero⟩
    exact Exec.seq hd1 (Exec.seq hd2 (Exec.seq hd3 (Exec.seq hloop
      (Exec.seq Exec.cpy (Exec.seq hchk (Exec.iteT (by simp [evalCond, h6F, h6Z]) Exec.skip))))))


/-! ## Nondeterministic machines with an arbitrary finite configuration space -/

theorem rtg_equiv {V : Type} {n : ℕ} (g : V ≃ Fin n) (r : V → V → Bool) (x y : V) :
    Relation.ReflTransGen (fun a b : Fin n => r (g.symm a) (g.symm b) = true) (g x) (g y)
      ↔ Relation.ReflTransGen (fun a b : V => r a b = true) x y := by
  constructor
  · intro h
    have := Relation.ReflTransGen.lift (p := fun a b : V => r a b = true) g.symm
      (fun a b hab => hab) h
    simpa using this
  · intro h
    exact Relation.ReflTransGen.lift (p := fun a b : Fin n => r (g.symm a) (g.symm b) = true) g
      (fun a b hab => by simpa using hab) h

/-- A nondeterministic machine with a finite configuration space: `step` is its
(nondeterministic) transition relation, and it accepts if some accepting configuration is
reachable from the initial one. -/
structure ConfigMachine where
  Conf : Type
  fintype : Fintype Conf
  decEq : DecidableEq Conf
  start : Conf
  step : Conf → Conf → Bool
  accept : Conf → Bool

attribute [instance] ConfigMachine.fintype ConfigMachine.decEq

/-- The machine accepts, i.e. some accepting configuration is reachable. -/
def ConfigMachine.Accepts (M : ConfigMachine) : Prop :=
  ∃ c, Relation.ReflTransGen (fun a b => M.step a b = true) M.start c ∧ M.accept c = true

/-- The configuration graph of `M` with a fresh sink vertex `none` reachable exactly from
the accepting configurations. -/
def ConfigMachine.stepO (M : ConfigMachine) : Option M.Conf → Option M.Conf → Bool
  | some a, some b => M.step a b
  | some a, none => M.accept a
  | none, _ => false

theorem ConfigMachine.rtg_some (M : ConfigMachine) {a : M.Conf} {y : Option M.Conf}
    (h : Relation.ReflTransGen (fun x y => M.stepO x y = true) (some a) y) :
    y = none ∨ ∃ z, y = some z ∧ Relation.ReflTransGen (fun x y => M.step x y = true) a z := by
  induction h with
  | refl => exact Or.inr ⟨a, rfl, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
      rcases ih with rfl | ⟨z, rfl, hz⟩
      · simp [ConfigMachine.stepO] at hbc
      · cases c with
        | none => exact Or.inl rfl
        | some w =>
            refine Or.inr ⟨w, rfl, hz.tail ?_⟩
            simpa [ConfigMachine.stepO] using hbc

theorem ConfigMachine.accepts_iff (M : ConfigMachine) :
    M.Accepts ↔
      Relation.ReflTransGen (fun x y => M.stepO x y = true) (some M.start) none := by
  constructor
  · rintro ⟨c, hc, hacc⟩
    have hlift : Relation.ReflTransGen (fun x y => M.stepO x y = true) (some M.start) (some c) :=
      Relation.ReflTransGen.lift (p := fun x y => M.stepO x y = true) some
        (fun a b hab => by simpa [ConfigMachine.stepO] using hab) hc
    exact hlift.tail (by simpa [ConfigMachine.stepO] using hacc)
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with hcon | ⟨c, hc, hstep⟩
    · exact absurd hcon (by simp)
    · rcases M.rtg_some hc with rfl | ⟨z, rfl, hz⟩
      · simp [ConfigMachine.stepO] at hstep
      · exact ⟨z, hz, by simpa [ConfigMachine.stepO] using hstep⟩

/-- The number of vertices of the augmented configuration graph. -/
noncomputable def ConfigMachine.size (M : ConfigMachine) : ℕ := Fintype.card (Option M.Conf)

noncomputable def ConfigMachine.enc (M : ConfigMachine) : Option M.Conf ≃ Fin M.size :=
  Fintype.equivFin _

/-- The augmented configuration graph of `M`, as a graph on `Fin M.size`. -/
noncomputable def ConfigMachine.graph (M : ConfigMachine) : Fin M.size → Fin M.size → Bool :=
  fun a b => M.stepO (M.enc.symm a) (M.enc.symm b)

/-- **Immerman–Szelepcsényi for machines.**  For every nondeterministic machine `M` with a
finite configuration space, the fixed program `nonReach`, run on the configuration graph of
`M`, accepts exactly when `M` rejects.  The program uses `13` variables holding values at
most `M.size`, i.e. `O(log M.size)` bits of workspace: if `M` is a nondeterministic
`O(log n)`-space machine on an input of length `n`, then `M.size` is polynomial in `n` and
the complementing machine again runs in space `O(log n)`.  This is `NL = coNL`. -/
theorem immerman_szelepcsenyi_machine (M : ConfigMachine) :
    (∃ e, Exec M.graph nonReach (initEnv (M.enc (some M.start)) (M.enc none)) e) ↔
      ¬ M.Accepts := by
  rw [immerman_szelepcsenyi, M.accepts_iff]
  exact not_congr (rtg_equiv M.enc M.stepO (some M.start) none)

/-! ## Space bound -/

/-- All variables of the program stay bounded by `m` throughout a run started in the
initial environment: the semantics blocks `incr` at the bound.  Every intermediate
environment of a run is the final environment of a sub-derivation, so this applies to the
whole computation. -/
theorem nonReach_space {E : Fin m → Fin m → Bool} {s t : Fin m} {e : Env}
    (h : Exec E nonReach (initEnv s t) e) : ∀ x, e x ≤ m := by
  refine exec_bounded h (fun x => ?_)
  by_cases h1 : x = vS
  · simp only [initEnv, h1]
    exact le_of_lt s.isLt
  · by_cases h2 : x = vTgt
    · simp only [initEnv, h2]
      exact le_of_lt t.isLt
    · simp only [initEnv, if_neg h1, if_neg h2]
      exact Nat.zero_le _

/-- The whole workspace of the program consists of `13` variables holding values at most
`m`, i.e. of `(m+1)^13` possible environments: `O(log m)` bits. -/
theorem env_card : Fintype.card (Var → Fin (m+1)) = (m+1)^13 := by
  simp

end CS

