/-!
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We prove: **there exist problems with no fastest algorithm** — a Blum-style speedup
phenomenon — in a completely explicit machine model with an explicit runtime measure.

*Machines.* A `DigitMachine` fixes a base `b ≥ 2` and is a finite-state streaming
machine: it reads the base-`b` digits of its input one digit per step (least
significant digit first), updating a state taken from a finite state set, and finally
outputs a bit determined by the state it ends in.

*Runtime.* The runtime (`cost`) of a machine on input `x` is the number of steps it
performs, i.e. the number of base-`b` digits of `x`.

*Speedup.* Recoding the input in base `b ^ k` lets one machine step consume `k` old
digits, dividing the runtime by `k`. Consequently, for the (nontrivial) problem
"is `x` divisible by `3`?", every algorithm is beaten, on all but finitely many
inputs, by another algorithm for the same problem, and by an arbitrarily large factor;
hence no fastest algorithm exists.

*Scope.* The statement proved here is "there exist problems with no fastest algorithm",
with the speedup obtained by input recoding in an explicit machine model with an
explicit runtime measure (`no_fastest_algorithm`, `blum_speedup`). The speedup factor
is linear (any factor `k`), so this is the recoding/linear-speedup form of the
phenomenon rather than Blum's recursion-theoretic construction with an arbitrary
total computable speedup function.

As in the classical argument, the price of the speedup is a larger transition table
(the compressed machine reads digits from a larger alphabet), not a slower step: each
step of any machine remains a single lookup in a finite control, and is charged one
unit of time.

The file is self-contained: it uses nothing beyond the Lean prelude.
-/

set_option autoImplicit false

namespace CS

/-! ## Numbers and digit strings -/

/-- The natural number represented by the digit list `L` in base `b`, least
significant digit first. -/
def ofDigits (b : Nat) : List Nat → Nat
  | [] => 0
  | d :: L => d + b * ofDigits b L

theorem ofDigits_nil (b : Nat) : ofDigits b [] = 0 := rfl

theorem ofDigits_cons (b d : Nat) (L : List Nat) :
    ofDigits b (d :: L) = d + b * ofDigits b L := rfl

theorem ofDigits_append (b : Nat) (L₁ L₂ : List Nat) :
    ofDigits b (L₁ ++ L₂) = ofDigits b L₁ + b ^ L₁.length * ofDigits b L₂ := by
  induction L₁ with
  | nil => simp [ofDigits_nil]
  | cons d L ih =>
      show d + b * ofDigits b (L ++ L₂) = (d + b * ofDigits b L) + b ^ (L.length + 1) * ofDigits b L₂
      rw [ih, Nat.mul_add, Nat.pow_succ, Nat.add_assoc, ← Nat.mul_assoc,
        Nat.mul_comm b (b ^ L.length)]

/-- The number of base-`b` digits of `x` (for `b ≥ 2`); this is the number of steps a
base-`b` streaming machine takes on input `x`. -/
def numDigits (b x : Nat) : Nat :=
  if h : 2 ≤ b ∧ 0 < x then 1 + numDigits b (x / b) else 0
decreasing_by exact Nat.div_lt_self h.2 h.1

theorem numDigits_zero (b : Nat) : numDigits b 0 = 0 := by
  rw [numDigits]; simp

theorem numDigits_succ (b x : Nat) (hb : 2 ≤ b) (hx : 0 < x) :
    numDigits b x = 1 + numDigits b (x / b) := by
  rw [numDigits]; simp [hb, hx]

/-- The key characterisation: `x` has at most `n` base-`b` digits iff `x < b ^ n`. -/
theorem numDigits_le_iff (b : Nat) (hb : 2 ≤ b) :
    ∀ (n x : Nat), numDigits b x ≤ n ↔ x < b ^ n := by
  intro n
  induction n with
  | zero =>
      intro x
      have hpow : b ^ 0 = 1 := rfl
      constructor
      · intro h
        rcases Nat.eq_zero_or_pos x with hx | hx
        · omega
        · rw [numDigits_succ b x hb hx] at h
          omega
      · intro h
        have hx : x = 0 := by omega
        rw [hx, numDigits_zero]
        omega
  | succ n ih =>
      intro x
      rcases Nat.eq_zero_or_pos x with hx | hx
      · subst hx
        constructor
        · intro _
          exact Nat.pow_pos (by omega)
        · intro _
          rw [numDigits_zero]
          omega
      · rw [numDigits_succ b x hb hx]
        have h1 : (1 + numDigits b (x / b) ≤ n + 1) ↔ (numDigits b (x / b) ≤ n) := by omega
        rw [h1, ih (x / b), Nat.pow_succ]
        exact Nat.div_lt_iff_lt_mul (by omega)

/-! ## The machine model -/

/-- A finite-state machine reading the base-`base` digits of its input, least
significant digit first, one digit per step, and returning a Boolean determined by the
state it ends in. -/
structure DigitMachine : Type 1 where
  /-- The base in which the input is presented. -/
  base : Nat
  /-- Inputs are presented in a base of at least two. -/
  two_le_base : 2 ≤ base
  /-- The set of internal states. -/
  State : Type
  /-- An explicit list of all states: the control is finite. -/
  states : List State
  /-- Every state occurs in `states`. -/
  states_complete : ∀ s : State, s ∈ states
  /-- The initial state. -/
  start : State
  /-- One computation step: read one digit and update the state. -/
  step : State → Nat → State
  /-- The output bit read off the final state. -/
  out : State → Bool

namespace DigitMachine

/-- The state reached after streaming the digit list `L` (least significant first). -/
def run (M : DigitMachine) (L : List Nat) : M.State := L.foldl M.step M.start

/-- `M` solves the decision problem `f` if, on every base-`M.base` digit string `L`
(leading zeros allowed), `M` outputs `f` of the number represented by `L`. -/
def Solves (M : DigitMachine) (f : Nat → Bool) : Prop :=
  ∀ L : List Nat, (∀ d ∈ L, d < M.base) → M.out (M.run L) = f (ofDigits M.base L)

/-- The runtime of `M` on input `x`: one step per base-`M.base` digit of `x`. -/
def cost (M : DigitMachine) (x : Nat) : Nat := numDigits M.base x

/-- `M` is a *fastest* algorithm for `f` if it solves `f` and, for every machine `N`
solving `f`, `M` is at least as fast as `N` on all but finitely many inputs. -/
def Fastest (M : DigitMachine) (f : Nat → Bool) : Prop :=
  M.Solves f ∧ ∀ N : DigitMachine, N.Solves f → ∃ x₀ : Nat, ∀ x ≥ x₀, M.cost x ≤ N.cost x

end DigitMachine

/-! ## Digit blocks and compression of machines -/

/-- `blockDigits b k d` lists the `k` lowest base-`b` digits of `d`, least significant
first. -/
def blockDigits (b : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, d => (d % b) :: blockDigits b k (d / b)

theorem blockDigits_length (b k d : Nat) : (blockDigits b k d).length = k := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih => simp [blockDigits, ih]

theorem blockDigits_lt (b : Nat) (hb : 0 < b) :
    ∀ (k d : Nat), ∀ e ∈ blockDigits b k d, e < b := by
  intro k
  induction k with
  | zero => intro d e he; simp [blockDigits] at he
  | succ k ih =>
      intro d e he
      rcases List.mem_cons.1 he with h | h
      · subst h; exact Nat.mod_lt _ hb
      · exact ih _ _ h

theorem ofDigits_blockDigits (b : Nat) :
    ∀ (k d : Nat), d < b ^ k → ofDigits b (blockDigits b k d) = d := by
  intro k
  induction k with
  | zero =>
      intro d hd
      have : b ^ 0 = 1 := rfl
      have : d = 0 := by omega
      simp [blockDigits, ofDigits_nil, this]
  | succ k ih =>
      intro d hd
      have hb : 0 < b := by
        rcases Nat.eq_zero_or_pos b with h | h
        · subst h
          rw [Nat.zero_pow (by omega)] at hd
          omega
        · exact h
      have hdb : d / b < b ^ k := by
        rw [Nat.div_lt_iff_lt_mul hb]
        rw [Nat.pow_succ] at hd
        omega
      show ofDigits b ((d % b) :: blockDigits b k (d / b)) = d
      rw [ofDigits_cons, ih _ hdb]
      exact Nat.mod_add_div d b

/-- The compressed machine: it works in base `base ^ k`, each of its steps consuming
one base-`base ^ k` digit, i.e. simulating `k` steps of `M`. -/
def DigitMachine.compress (M : DigitMachine) (k : Nat) (hk : 1 ≤ k) : DigitMachine where
  base := M.base ^ k
  two_le_base := by
    have hb := M.two_le_base
    have h1 : M.base ^ 1 ≤ M.base ^ k := Nat.pow_le_pow_right (by omega) hk
    rw [Nat.pow_one] at h1
    omega
  State := M.State
  states := M.states
  states_complete := M.states_complete
  start := M.start
  step := fun s d => (blockDigits M.base k d).foldl M.step s
  out := M.out

theorem foldl_flatMap {α β γ : Type} (g : α → List β) (F : γ → β → γ) :
    ∀ (L : List α) (s : γ),
      (L.flatMap g).foldl F s = L.foldl (fun s a => (g a).foldl F s) s := by
  intro L
  induction L with
  | nil => intro s; rfl
  | cons a L ih => intro s; simp [List.flatMap_cons, List.foldl_append, ih]

theorem ofDigits_flatMap_blockDigits (b k : Nat) :
    ∀ (L : List Nat), (∀ d ∈ L, d < b ^ k) →
      ofDigits (b ^ k) L = ofDigits b (L.flatMap (blockDigits b k)) := by
  intro L
  induction L with
  | nil => intro _; simp [ofDigits_nil]
  | cons d L ih =>
      intro hL
      have hd : d < b ^ k := hL d List.mem_cons_self
      have hL' : ∀ e ∈ L, e < b ^ k := fun e he => hL e (List.mem_cons_of_mem _ he)
      rw [List.flatMap_cons, ofDigits_append, ofDigits_blockDigits b k d hd,
        blockDigits_length, ofDigits_cons, ih hL']

theorem DigitMachine.compress_solves (M : DigitMachine) (k : Nat) (hk : 1 ≤ k)
    (f : Nat → Bool) (hM : M.Solves f) : (M.compress k hk).Solves f := by
  intro L hL
  have hb : 0 < M.base := by have := M.two_le_base; omega
  have hexp : ∀ e ∈ L.flatMap (blockDigits M.base k), e < M.base := by
    intro e he
    rcases List.mem_flatMap.1 he with ⟨d, _, hd⟩
    exact blockDigits_lt M.base hb k d e hd
  have hrun : (M.compress k hk).run L = M.run (L.flatMap (blockDigits M.base k)) :=
    (foldl_flatMap (blockDigits M.base k) M.step L M.start).symm
  have hsol := hM (L.flatMap (blockDigits M.base k)) hexp
  show (M.compress k hk).out ((M.compress k hk).run L) = f (ofDigits (M.base ^ k) L)
  rw [hrun]
  show M.out (M.run (L.flatMap (blockDigits M.base k))) = f (ofDigits (M.base ^ k) L)
  rw [hsol, ← ofDigits_flatMap_blockDigits M.base k L hL]

/-! ## The runtime of the compressed machine -/

theorem numDigits_pow (b : Nat) (hb : 2 ≤ b) (k : Nat) (hk : 1 ≤ k) (x : Nat) :
    k * numDigits (b ^ k) x ≤ numDigits b x + (k - 1) := by
  have hbk : 2 ≤ b ^ k := by
    have h1 : b ^ 1 ≤ b ^ k := Nat.pow_le_pow_right (by omega) hk
    rw [Nat.pow_one] at h1
    omega
  have hkq : numDigits b x ≤ k * ((numDigits b x + k - 1) / k) := by
    have h := Nat.div_add_mod (numDigits b x + k - 1) k
    have hm : (numDigits b x + k - 1) % k < k := Nat.mod_lt _ (by omega)
    omega
  have hxlt : x < b ^ numDigits b x := (numDigits_le_iff b hb _ x).1 (by omega)
  have hle : b ^ numDigits b x ≤ b ^ (k * ((numDigits b x + k - 1) / k)) :=
    Nat.pow_le_pow_right (by omega) hkq
  have hxlt' : x < (b ^ k) ^ ((numDigits b x + k - 1) / k) := by
    rw [← Nat.pow_mul]
    omega
  have hA : numDigits (b ^ k) x ≤ (numDigits b x + k - 1) / k :=
    (numDigits_le_iff (b ^ k) hbk _ x).2 hxlt'
  have hqk : (numDigits b x + k - 1) / k * k ≤ numDigits b x + k - 1 :=
    Nat.div_mul_le_self _ _
  have : k * numDigits (b ^ k) x ≤ k * ((numDigits b x + k - 1) / k) :=
    Nat.mul_le_mul_left _ hA
  have hcomm : k * ((numDigits b x + k - 1) / k) = (numDigits b x + k - 1) / k * k :=
    Nat.mul_comm _ _
  omega

theorem DigitMachine.compress_cost (M : DigitMachine) (k : Nat) (hk : 1 ≤ k) (x : Nat) :
    k * (M.compress k hk).cost x ≤ M.cost x + k := by
  have h := numDigits_pow M.base M.two_le_base k hk x
  show k * numDigits (M.base ^ k) x ≤ numDigits M.base x + k
  omega

theorem DigitMachine.compress_cost_lt (M : DigitMachine) (x : Nat) (hx : M.base ≤ x) :
    (M.compress 2 (by omega)).cost x < M.cost x := by
  have h2 := numDigits_pow M.base M.two_le_base 2 (by omega) x
  have hb2 : 2 ≤ numDigits M.base x := by
    rcases Nat.lt_or_ge (numDigits M.base x) 2 with h | h
    · have h1 : numDigits M.base x ≤ 1 := by omega
      have h3 := (numDigits_le_iff M.base M.two_le_base 1 x).1 h1
      rw [Nat.pow_one] at h3
      omega
    · exact h
  show numDigits (M.base ^ 2) x < numDigits M.base x
  omega

/-! ## A concrete problem: divisibility by three -/

/-- The decision problem: "is `x` divisible by `3`?" -/
def divBy3 (x : Nat) : Bool := decide (x % 3 = 0)

/-- A base-`4` streaming machine deciding divisibility by three: since `4 ≡ 1 mod 3`,
it suffices to add up the digits modulo `3`. -/
def mod3Machine : DigitMachine where
  base := 4
  two_le_base := by omega
  State := Fin 3
  states := [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩]
  states_complete := by
    intro s
    obtain ⟨v, hv⟩ := s
    match v, hv with
    | 0, _ => simp
    | 1, _ => simp
    | 2, _ => simp
  start := ⟨0, by omega⟩
  step := fun s d => ⟨(s.val + d) % 3, Nat.mod_lt _ (by omega)⟩
  out := fun s => decide (s.val = 0)

theorem mod3Machine_foldl :
    ∀ (L : List Nat) (r : Fin 3),
      (L.foldl mod3Machine.step r).val = (r.val + ofDigits 4 L) % 3 := by
  intro L
  induction L with
  | nil =>
      intro r
      show r.val = (r.val + 0) % 3
      have : r.val < 3 := r.isLt
      omega
  | cons d L ih =>
      intro r
      have h := ih (mod3Machine.step r d)
      show (L.foldl mod3Machine.step (mod3Machine.step r d)).val
        = (r.val + (d + 4 * ofDigits 4 L)) % 3
      rw [h]
      show ((r.val + d) % 3 + ofDigits 4 L) % 3 = (r.val + (d + 4 * ofDigits 4 L)) % 3
      omega

theorem mod3Machine_solves : mod3Machine.Solves divBy3 := by
  intro L _
  have h := mod3Machine_foldl L mod3Machine.start
  have hs : (mod3Machine.start : Fin 3).val = 0 := rfl
  show decide ((L.foldl mod3Machine.step mod3Machine.start).val = 0)
    = divBy3 (ofDigits 4 L)
  rw [h, hs]
  show decide ((0 + ofDigits 4 L) % 3 = 0) = decide (ofDigits 4 L % 3 = 0)
  rw [Nat.zero_add]

/-! ## No algorithm in this model is fastest -/

/-- Every machine is strictly beaten, on all sufficiently large inputs, by the machine
that reads two digits at a time. -/
theorem exists_faster (f : Nat → Bool) (M : DigitMachine) (hM : M.Solves f) :
    ∃ N : DigitMachine, N.Solves f ∧ ∃ x₀ : Nat, ∀ x ≥ x₀, N.cost x < M.cost x :=
  ⟨M.compress 2 (by omega), M.compress_solves 2 (by omega) f hM,
    M.base, fun x hx => M.compress_cost_lt x hx⟩

/-- **No algorithm is fastest**: whatever the problem `f` and whatever machine `M`
solves it, `M` is not a fastest algorithm for `f`. -/
theorem no_fastest_algorithm (f : Nat → Bool) (M : DigitMachine) : ¬ M.Fastest f := by
  rintro ⟨hM, hfast⟩
  obtain ⟨N, hN, x₀, hx₀⟩ := exists_faster f M hM
  obtain ⟨x₁, hx₁⟩ := hfast N hN
  have h1 := hx₀ (max x₀ x₁) (Nat.le_max_left _ _)
  have h2 := hx₁ (max x₀ x₁) (Nat.le_max_right _ _)
  omega

/-! ## Main theorem -/

/-- **There exist problems with no fastest algorithm** (Blum-style speedup).

There is a decision problem `f` (namely, divisibility by three) which is solvable in
the model of finite-state digit-streaming machines, such that:

* every machine solving `f` is strictly beaten, on all but finitely many inputs, by
  another machine solving `f`;
* the speedup can be arranged by an arbitrarily large factor `k`
  (`k * N.cost x ≤ M.cost x + k` for all inputs);
* consequently no machine is a fastest algorithm for `f`.
-/
theorem blum_speedup :
    ∃ f : Nat → Bool,
      (∃ M : DigitMachine, M.Solves f) ∧
      (∀ M : DigitMachine, M.Solves f →
        ∃ N : DigitMachine, N.Solves f ∧ ∃ x₀ : Nat, ∀ x ≥ x₀, N.cost x < M.cost x) ∧
      (∀ M : DigitMachine, M.Solves f → ∀ k : Nat, 1 ≤ k →
        ∃ N : DigitMachine, N.Solves f ∧ ∀ x : Nat, k * N.cost x ≤ M.cost x + k) ∧
      (∀ M : DigitMachine, ¬ M.Fastest f) := by
  refine ⟨divBy3, ⟨mod3Machine, mod3Machine_solves⟩, ?_, ?_, ?_⟩
  · exact fun M hM => exists_faster divBy3 M hM
  · intro M hM k hk
    exact ⟨M.compress k hk, M.compress_solves k hk divBy3 hM,
      fun x => M.compress_cost k hk x⟩
  · exact fun M => no_fastest_algorithm divBy3 M

end CS

import RequestProject.BlumSpeedup
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

