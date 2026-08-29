/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file is self-contained: it depends on nothing but the Lean core library.

We set up a concrete model of computation.  Inputs are natural numbers, programs are
natural numbers as well (a code is read as `pair tag args`, so that every natural number
is a program), and `eval k c x` runs the program `c` on input `x` with a budget of `k`
steps.  The instruction set contains the basic arithmetic and pairing operations, a
conditional, an unbounded loop, and one universal instruction which runs a given program
on a given input under a given step budget, at the cost of that budget plus one step.

`InTime t L` says that the language `L : Nat → Bool` is decided by some program within
`t x` steps on every input `x`.  Since running a program with more fuel gives the same
result (`eval_mono`), these classes grow with `t`.

The main result `CS.time_hierarchy` is the time hierarchy theorem for this model: if the
time bound `t` is itself computable within time `b`, and `T x ≥ t x + b x + 8`, then
every language decidable in time `t` is decidable in time `T`, and some language --
the diagonal language `diagLang t` -- is decidable in time `T` but not in time `t`.
-/

namespace CS

/-! ## A pairing function on `Nat` -/

/-- `twos d` is the 2-adic valuation of `d` (with `twos 0 = 0`). -/
def twos : Nat → Nat
  | 0 => 0
  | d + 1 => if (d + 1) % 2 = 0 then twos ((d + 1) / 2) + 1 else 0
decreasing_by omega

theorem twos_odd (b : Nat) : twos (2 * b + 1) = 0 := by
  rw [twos]
  have h : (2 * b + 1) % 2 = 1 := by omega
  simp [h]

theorem twos_even (n : Nat) : twos (2 * (n + 1)) = twos (n + 1) + 1 := by
  have h2 : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
  rw [h2, twos]
  have h : (2 * n + 1 + 1) % 2 = 0 := by omega
  have h3 : (2 * n + 1 + 1) / 2 = n + 1 := by omega
  simp [h, h3]

theorem twos_pair (a b : Nat) : twos (2 ^ a * (2 * b + 1)) = a := by
  induction a with
  | zero => simpa using twos_odd b
  | succ a ih =>
      have hp : 0 < 2 ^ a * (2 * b + 1) := Nat.mul_pos (Nat.two_pow_pos a) (by omega)
      obtain ⟨n, hn⟩ : ∃ n, 2 ^ a * (2 * b + 1) = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hp).symm⟩
      have h : 2 ^ (a + 1) * (2 * b + 1) = 2 * (n + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc, hn]
      rw [h, twos_even, ← hn, ih]

/-- Pairing of two naturals into one. -/
def pair (a b : Nat) : Nat := 2 ^ a * (2 * b + 1) - 1

/-- First projection of `pair`. -/
def fst (c : Nat) : Nat := twos (c + 1)

/-- Second projection of `pair`. -/
def snd (c : Nat) : Nat := ((c + 1) / 2 ^ (twos (c + 1)) - 1) / 2

theorem pair_add_one (a b : Nat) : pair a b + 1 = 2 ^ a * (2 * b + 1) := by
  have hp : 0 < 2 ^ a * (2 * b + 1) := Nat.mul_pos (Nat.two_pow_pos a) (by omega)
  unfold pair; omega

@[simp] theorem fst_pair (a b : Nat) : fst (pair a b) = a := by
  unfold fst; rw [pair_add_one, twos_pair]

@[simp] theorem snd_pair (a b : Nat) : snd (pair a b) = b := by
  unfold snd
  rw [pair_add_one, twos_pair, Nat.mul_div_cancel_left _ (Nat.two_pow_pos a)]
  omega

/-! ## The machine model -/

/-- Encoding of a possibly-diverging output as a natural number:
`0` means "no output", `v + 1` means "output `v`". -/
def encOpt : Option Nat → Nat
  | none => 0
  | some v => v + 1

/--
`eval k c x` runs the program with code `c` on input `x` with a budget (fuel) of `k`
steps, returning `some v` if it produces the output `v` within the budget and `none`
otherwise.

A code `c` is read as `pair tag args`; the tag selects the instruction:

* `0`: identity
* `1`: the constant `args`
* `2`: successor
* `3`: predecessor
* `4`: pairing of the two subprograms in `args`
* `5`, `6`: the two projections
* `7`: composition of the two subprograms in `args`
* `8`: `if f x = 0 then g x else h x`
* `9`: the loop `x ↦ if x = 0 then 0 else loop f (f x)` (unbounded recursion)
* `10`: the universal instruction: on input `pair k' (pair c' x')` it runs the program
  `c'` on the input `x'` with a budget of `k'` steps, and reports the (encoded) result.
  It requires a budget of at least `k' + 1` steps.

Every instruction consumes one unit of fuel, and subprograms are run with the
remaining fuel.
-/
def eval : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | k + 1, c, x =>
    if fst c = 0 then some x
    else if fst c = 1 then some (snd c)
    else if fst c = 2 then some (x + 1)
    else if fst c = 3 then some (x - 1)
    else if fst c = 4 then
      (eval k (fst (snd c)) x).bind fun u => (eval k (snd (snd c)) x).map fun v => pair u v
    else if fst c = 5 then some (fst x)
    else if fst c = 6 then some (snd x)
    else if fst c = 7 then (eval k (snd (snd c)) x).bind fun v => eval k (fst (snd c)) v
    else if fst c = 8 then
      (eval k (fst (snd c)) x).bind fun v =>
        if v = 0 then eval k (fst (snd (snd c))) x else eval k (snd (snd (snd c))) x
    else if fst c = 9 then
      (if x = 0 then some 0 else (eval k (snd c) x).bind fun v => eval k c v)
    else if fst c = 10 ∧ fst x ≤ k then
      some (encOpt (eval (fst x) (fst (snd x)) (snd (snd x))))
    else none
termination_by k => k
decreasing_by all_goals omega

theorem eval_zero (c x : Nat) : eval 0 c x = none := by rw [eval]

/-- Running a program with more fuel gives the same result. -/
theorem eval_succ : ∀ (k c x v : Nat), eval k c x = some v → eval (k + 1) c x = some v := by
  intro k
  induction k with
  | zero => intro c x v hv; rw [eval_zero] at hv; exact absurd hv (by simp)
  | succ k ih =>
    intro c x v hv
    rw [eval] at hv ⊢
    by_cases h0 : fst c = 0
    · simpa [h0] using hv
    by_cases h1 : fst c = 1
    · simpa [h0, h1] using hv
    by_cases h2 : fst c = 2
    · simpa [h0, h1, h2] using hv
    by_cases h3 : fst c = 3
    · simpa [h0, h1, h2, h3] using hv
    by_cases h4 : fst c = 4
    · simp only [h4, if_true] at hv ⊢
      cases hf : eval k (fst (snd c)) x with
      | none => rw [hf] at hv; simp at hv
      | some u =>
        cases hg : eval k (snd (snd c)) x with
        | none => rw [hf, hg] at hv; simp at hv
        | some w =>
          rw [hf, hg] at hv
          rw [ih _ _ _ hf, ih _ _ _ hg]
          simpa using hv
    by_cases h5 : fst c = 5
    · simpa [h0, h1, h2, h3, h4, h5] using hv
    by_cases h6 : fst c = 6
    · simpa [h0, h1, h2, h3, h4, h5, h6] using hv
    by_cases h7 : fst c = 7
    · simp only [h7, if_true] at hv ⊢
      cases hg : eval k (snd (snd c)) x with
      | none => rw [hg] at hv; simp at hv
      | some w =>
        rw [hg] at hv
        rw [ih _ _ _ hg]
        simpa using ih _ _ _ (by simpa using hv)
    by_cases h8 : fst c = 8
    · simp only [h8, if_true] at hv ⊢
      cases hf : eval k (fst (snd c)) x with
      | none => rw [hf] at hv; simp at hv
      | some w =>
        rw [hf] at hv
        rw [ih _ _ _ hf]
        simp only [Option.bind_some] at hv ⊢
        by_cases hw : w = 0
        · simp only [hw, if_true] at hv ⊢
          exact ih _ _ _ hv
        · simp only [hw, if_false] at hv ⊢
          exact ih _ _ _ hv
    by_cases h9 : fst c = 9
    · simp only [h9, if_true] at hv ⊢
      by_cases hx : x = 0
      · simpa [hx] using hv
      · simp only [hx, if_false] at hv ⊢
        cases hf : eval k (snd c) x with
        | none => rw [hf] at hv; simp at hv
        | some w =>
          rw [hf] at hv
          rw [ih _ _ _ hf]
          simpa using ih _ _ _ (by simpa using hv)
    by_cases h10 : fst c = 10
    · by_cases hk : fst x ≤ k
      · have hk' : fst x ≤ k + 1 := by omega
        simp only [h10, hk, hk', reduceIte, and_self] at hv ⊢
        exact hv
      · simp only [h10, hk, reduceIte, and_false] at hv
        exact absurd hv (by simp)
    · simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, if_false, false_and] at hv
      exact absurd hv (by simp)

theorem eval_add (k d c x v : Nat) (hv : eval k c x = some v) : eval (k + d) c x = some v := by
  induction d with
  | zero => exact hv
  | succ d ih => exact eval_succ _ _ _ _ ih

/-- Running a program with more fuel gives the same result. -/
theorem eval_mono {k k' c x v : Nat} (h : k ≤ k') (hv : eval k c x = some v) :
    eval k' c x = some v := by
  obtain ⟨d, rfl⟩ : ∃ d, k' = k + d := ⟨k' - k, by omega⟩
  exact eval_add k d c x v hv

/-! ## Basic programs -/

/-- The identity program. -/
def cId : Nat := pair 0 0
/-- The constant program with value `n`. -/
def cConst (n : Nat) : Nat := pair 1 n
/-- The predecessor program. -/
def cPred : Nat := pair 3 0
/-- Pairing of two programs. -/
def cPairC (f g : Nat) : Nat := pair 4 (pair f g)
/-- Composition of two programs. -/
def cComp (f g : Nat) : Nat := pair 7 (pair f g)
/-- Case distinction on whether the first program outputs `0`. -/
def cIfz (f g h : Nat) : Nat := pair 8 (pair f (pair g h))
/-- The loop `x ↦ if x = 0 then 0 else cLoop f (f x)`. -/
def cLoop (f : Nat) : Nat := pair 9 f
/-- The universal program. -/
def cSim : Nat := pair 10 0

theorem eval_cId (k x : Nat) : eval (k + 1) cId x = some x := by
  rw [eval]; simp [cId]

theorem eval_cConst (k n x : Nat) : eval (k + 1) (cConst n) x = some n := by
  rw [eval]; simp [cConst]

theorem eval_cPred (k x : Nat) : eval (k + 1) cPred x = some (x - 1) := by
  rw [eval]; simp [cPred]

theorem eval_cPairC {k f g x u v : Nat} (hf : eval k f x = some u) (hg : eval k g x = some v) :
    eval (k + 1) (cPairC f g) x = some (pair u v) := by
  rw [eval]; simp [cPairC, hf, hg]

theorem eval_cComp {k f g x v w : Nat} (hg : eval k g x = some v) (hf : eval k f v = some w) :
    eval (k + 1) (cComp f g) x = some w := by
  rw [eval]; simp [cComp, hg, hf]

theorem eval_cIfz_zero {k f g h x w : Nat} (hf : eval k f x = some 0)
    (hg : eval k g x = some w) : eval (k + 1) (cIfz f g h) x = some w := by
  rw [eval]; simp [cIfz, hf, hg]

theorem eval_cIfz_succ {k f g h x u w : Nat} (hf : eval k f x = some (u + 1))
    (hh : eval k h x = some w) : eval (k + 1) (cIfz f g h) x = some w := by
  rw [eval]; simp [cIfz, hf, hh]

theorem eval_cSim {k k' c y : Nat} (hk : k' ≤ k) :
    eval (k + 1) cSim (pair k' (pair c y)) = some (encOpt (eval k' c y)) := by
  rw [eval]; simp [cSim, hk]

theorem eval_cLoop_zero (k f : Nat) : eval (k + 1) (cLoop f) 0 = some 0 := by
  rw [eval]; simp [cLoop]

theorem eval_cLoop_succ {k f x u v : Nat} (hx : x ≠ 0) (hf : eval k f x = some u)
    (hl : eval k (cLoop f) u = some v) : eval (k + 1) (cLoop f) x = some v := by
  rw [eval]
  unfold cLoop at hl ⊢
  simp [hx, hf, hl]

/-- The model really does support unbounded iteration: counting down to `0` from `x`
takes about `2 * x` steps. -/
theorem eval_cLoop_cPred (x : Nat) : ∀ k, 2 * x + 1 ≤ k → eval k (cLoop cPred) x = some 0 := by
  induction x with
  | zero =>
      intro k hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact eval_cLoop_zero j cPred
  | succ x ih =>
      intro k hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      refine eval_cLoop_succ (by omega) (u := x) ?_ (ih (j + 1) (by omega))
      simpa using eval_cPred j (x + 1)

/-! ## Time-bounded classes -/

/-- A language, i.e. a subset of the set of inputs `Nat`, given by its characteristic
function. -/
abbrev Lang := Nat → Bool

/-- `InTime t L` says that the language `L` is decided by some program within `t x`
steps on every input `x`. -/
def InTime (t : Nat → Nat) (L : Lang) : Prop :=
  ∃ c : Nat, ∀ x, eval (t x) c x = some (if L x then 1 else 0)

/-- More time can only decide more languages. -/
theorem InTime.mono {t T : Nat → Nat} (h : ∀ x, t x ≤ T x) {L : Lang} (hL : InTime t L) :
    InTime T L := by
  obtain ⟨c, hc⟩ := hL
  exact ⟨c, fun x => eval_mono (h x) (hc x)⟩

/-! ### Non-emptiness of the time-bounded classes -/

/-- The empty language is decidable in one step. -/
theorem InTime_const_false : InTime (fun _ => 1) (fun _ => false) :=
  ⟨cConst 0, fun x => eval_cConst 0 0 x⟩

/-- The language `{0}` is decidable in two steps. -/
theorem InTime_eqZero : InTime (fun _ => 2) (fun x => x == 0) := by
  refine ⟨cIfz cId (cConst 1) (cConst 0), fun x => ?_⟩
  cases x with
  | zero => exact eval_cIfz_zero (eval_cId 0 0) (eval_cConst 0 1 0)
  | succ n => exact eval_cIfz_succ (eval_cId 0 (n + 1)) (eval_cConst 0 0 (n + 1))

/-! ## The diagonal language -/

/-- The diagonal language for the time bound `t`: the input `x`, read as a program code,
does *not* output `1` on input `x` within `t x` steps. -/
def diagLang (t : Nat → Nat) (x : Nat) : Bool :=
  match eval (t x) x x with
  | some 1 => false
  | _ => true

/-- Diagonalization: the diagonal language is not decidable in time `t`. -/
theorem diagLang_not_inTime (t : Nat → Nat) : ¬ InTime t (diagLang t) := by
  intro h
  obtain ⟨c, hc⟩ := h
  have hcc := hc c
  unfold diagLang at hcc
  cases he : eval (t c) c c with
  | none => rw [he] at hcc; simp at hcc
  | some v =>
      rw [he] at hcc
      match v, hcc with
      | 0, hcc => simp at hcc
      | 1, hcc => simp at hcc
      | (v + 2), hcc => simp at hcc

/-! ## The diagonal program -/

/-- On input `x`, this program simulates the program with code `x` on input `x` for
`t x` steps (where `pt` computes `t`), and returns the encoded outcome. -/
def simDiag (pt : Nat) : Nat := cComp cSim (cPairC pt (cPairC cId cId))

/-- The program deciding the diagonal language: it outputs `0` exactly when the
simulation returns the output `1`. -/
def diagCode (pt : Nat) : Nat :=
  cIfz (cComp cPred (simDiag pt)) (cConst 1)
    (cIfz (cComp cPred (cComp cPred (simDiag pt))) (cConst 0) (cConst 1))

theorem eval_simDiag {t b : Nat → Nat} {pt : Nat} (hpt : ∀ x, eval (b x) pt x = some (t x))
    (x : Nat) {m : Nat} (hm : t x + b x + 4 ≤ m) :
    eval m (simDiag pt) x = some (encOpt (eval (t x) x x)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 4 := ⟨m - 4, by omega⟩
  have hinner : eval (s + 2) (cPairC cId cId) x = some (pair x x) :=
    eval_cPairC (eval_cId _ _) (eval_cId _ _)
  have hpt' : eval (s + 2) pt x = some (t x) := eval_mono (by omega) (hpt x)
  have hargs : eval (s + 3) (cPairC pt (cPairC cId cId)) x = some (pair (t x) (pair x x)) :=
    eval_cPairC hpt' hinner
  have hsim : eval (s + 3) cSim (pair (t x) (pair x x)) = some (encOpt (eval (t x) x x)) :=
    eval_cSim (by omega)
  exact eval_cComp hargs hsim

theorem eval_diagCode {t b : Nat → Nat} {pt : Nat} (hpt : ∀ x, eval (b x) pt x = some (t x))
    (x : Nat) {m : Nat} (hm : t x + b x + 8 ≤ m) :
    eval m (diagCode pt) x = some (if diagLang t x then 1 else 0) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, i = s + 1 := ⟨i - 1, by omega⟩
  have hS : ∀ n, t x + b x + 4 ≤ n → eval n (simDiag pt) x = some (encOpt (eval (t x) x x)) :=
    fun n hn => eval_simDiag hpt x hn
  have hP : ∀ n, t x + b x + 5 ≤ n →
      eval n (cComp cPred (simDiag pt)) x = some (encOpt (eval (t x) x x) - 1) := by
    intro n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
    exact eval_cComp (hS (p + 1) (by omega)) (eval_cPred _ _)
  have hPP : ∀ n, t x + b x + 6 ≤ n →
      eval n (cComp cPred (cComp cPred (simDiag pt))) x =
        some (encOpt (eval (t x) x x) - 1 - 1) := by
    intro n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
    exact eval_cComp (hP (p + 1) (by omega)) (eval_cPred _ _)
  unfold diagCode diagLang
  cases he : eval (t x) x x with
  | none =>
      have h1 : eval (s + 2) (cComp cPred (simDiag pt)) x = some 0 := by
        rw [hP _ (by omega), he]; rfl
      simpa using eval_cIfz_zero h1 (eval_cConst _ _ _)
  | some v =>
      match v, he with
      | 0, he =>
          have h1 : eval (s + 2) (cComp cPred (simDiag pt)) x = some 0 := by
            rw [hP _ (by omega), he]; rfl
          simpa using eval_cIfz_zero h1 (eval_cConst _ _ _)
      | 1, he =>
          have h1 : eval (s + 2) (cComp cPred (simDiag pt)) x = some (0 + 1) := by
            rw [hP _ (by omega), he]; rfl
          have h2 : eval (s + 1) (cComp cPred (cComp cPred (simDiag pt))) x = some 0 := by
            rw [hPP _ (by omega), he]; rfl
          have h3 : eval (s + 2)
              (cIfz (cComp cPred (cComp cPred (simDiag pt))) (cConst 0) (cConst 1)) x = some 0 :=
            eval_cIfz_zero h2 (eval_cConst s 0 x)
          simpa using eval_cIfz_succ h1 h3
      | (v + 2), he =>
          have h1 : eval (s + 2) (cComp cPred (simDiag pt)) x = some (v + 1 + 1) := by
            rw [hP _ (by omega), he]; rfl
          have h2 : eval (s + 1) (cComp cPred (cComp cPred (simDiag pt))) x = some (v + 1) := by
            rw [hPP _ (by omega), he]; rfl
          have h3 : eval (s + 2)
              (cIfz (cComp cPred (cComp cPred (simDiag pt))) (cConst 0) (cConst 1)) x = some 1 :=
            eval_cIfz_succ h2 (eval_cConst s 1 x)
          simpa using eval_cIfz_succ h1 h3

/-! ## The time hierarchy theorem -/

/--
**Time hierarchy theorem.**  If the time bound `t` is itself computable within time `b`
(witnessed by the program `pt`), and `T` exceeds `t + b` by a constant, then the class of
languages decidable in time `T` strictly contains the class of languages decidable in
time `t`: every language decidable in time `t` is decidable in time `T`, and there is a
language (obtained by diagonalization) decidable in time `T` but not in time `t`.
-/
theorem time_hierarchy {t b T : Nat → Nat} {pt : Nat} (hpt : ∀ x, eval (b x) pt x = some (t x))
    (hT : ∀ x, t x + b x + 8 ≤ T x) :
    (∀ L : Lang, InTime t L → InTime T L) ∧ ∃ L : Lang, InTime T L ∧ ¬ InTime t L := by
  refine ⟨fun L hL => InTime.mono (fun x => by have := hT x; omega) hL, ?_⟩
  refine ⟨diagLang t, ⟨diagCode pt, fun x => eval_diagCode hpt x (hT x)⟩, ?_⟩
  exact diagLang_not_inTime t

/-- A concrete instance: linear time is strictly weaker than linear time plus a
constant amount of extra time. -/
theorem time_hierarchy_id :
    (∀ L : Lang, InTime (fun x => x) L → InTime (fun x => x + 9) L) ∧
      ∃ L : Lang, InTime (fun x => x + 9) L ∧ ¬ InTime (fun x => x) L :=
  time_hierarchy (t := fun x => x) (b := fun _ => 1) (pt := cId)
    (fun x => eval_cId 0 x) (fun x => by show x + 1 + 8 ≤ x + 9; omega)

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

