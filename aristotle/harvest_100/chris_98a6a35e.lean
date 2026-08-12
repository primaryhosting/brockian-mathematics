/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Statement: NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` commands to precede every declaration, including module
docstrings, so the header above is a plain block comment.)
-/
import Mathlib
import RequestProject.Savitch.Model
import RequestProject.Savitch.Walk
import RequestProject.Savitch.Sim
import RequestProject.Savitch.Semantics
import RequestProject.Savitch.Space

/-!
The space-bounded machine model, the classes `CS.NSPACE`, `CS.DSPACE`,
`CS.PSPACE` and `CS.NPSPACE`, and the simulator used in the proof are defined in
the files `RequestProject/Savitch/*.lean`.

A machine reads its input through a head whose position is determined by its
memory value, and it works in space `g` if on inputs of length `n` all reachable
memory values lie in a set of at most `2 ^ g n` values depending only on `n`
(the standard correspondence between `s` tape cells and `2 ^ O(s)`
configurations).  The classes `NSPACE g` and `DSPACE g` are closed under
constant factors by definition, as usual for space classes.

Savitch's theorem is proved for space bounds `f` with `n + 1 ≤ 2 ^ f n`
(i.e. `f n ≥ log₂ (n+1)`), the standard hypothesis `f (n) ≥ log n`.
-/

namespace CS

/-- **Savitch's theorem**: a language recognized by a nondeterministic machine in
space `f` (with `f n ≥ log₂ (n + 1)`) is recognized by a deterministic machine in
space `O(f²)`, i.e. `NSPACE f ⊆ DSPACE (f²)`. -/
theorem savitch (f : ℕ → ℕ) (hf : ∀ n, n + 1 ≤ 2 ^ f n) :
    NSPACE f ⊆ DSPACE (fun n => (f n) ^ 2) := by
  classical
  rintro L ⟨N, c, hc, ⟨S, hS, hcard⟩, hLN⟩
  set g : ℕ → ℕ := fun n => c * f n + c with hg
  refine ⟨simMachine N S g, 10 * c ^ 2 + 20 * c + 6, by positivity, simMachine_det N S g,
    ⟨Dset N S g, ?_, ?_⟩, ?_⟩
  · -- every reachable memory value of the simulator lies in `Dset`
    intro x m hm
    obtain ⟨t, ht⟩ := (simReach_iff m).mp hm
    subst ht
    exact mem_Dset (SInv_iter (x := x) (n := x.length) rfl t)
  · -- the cardinality bound
    intro n
    have hn : n + 1 ≤ 2 ^ g n := by
      refine le_trans (hf n) (Nat.pow_le_pow_right (by omega) ?_)
      have : f n ≤ c * f n := Nat.le_mul_of_pos_left _ hc
      simp only [hg]
      omega
    refine le_trans (card_Dset_le (hcard n) hn) (Nat.pow_le_pow_right (by omega) ?_)
    have hgn : g n = c * f n + c := rfl
    rw [hgn]
    have h2F : 2 * f n ≤ (f n) ^ 2 + 1 := by
      cases hfn : f n with
      | zero => simp
      | succ m =>
        have : (m + 1) ^ 2 = m * m + 2 * m + 1 := by ring
        omega
    have h1 : 5 * c ^ 2 * (2 * f n) ≤ 5 * c ^ 2 * ((f n) ^ 2 + 1) :=
      Nat.mul_le_mul_left _ h2F
    have h2 : 5 * c * (2 * f n) ≤ 5 * c * ((f n) ^ 2 + 1) :=
      Nat.mul_le_mul_left _ h2F
    nlinarith [h1, h2, Nat.zero_le (c * (f n) ^ 2), Nat.zero_le c]
  · -- correctness
    intro x
    rw [hLN x, simAccepts_iff_CY, CY_search_iff_accepts hS hcard]

/-- Deterministic and nondeterministic polynomial space coincide. -/
theorem PSPACE_eq_NPSPACE : PSPACE = NPSPACE := by
  apply Set.eq_of_subset_of_subset
  · rintro L ⟨k, hk⟩
    exact ⟨k, DSPACE_subset_NSPACE _ hk⟩
  · rintro L ⟨k, hk⟩
    have hmono : L ∈ NSPACE (fun n => (n + 1) ^ (k + 1)) := by
      refine NSPACE_mono (fun n => ?_) hk
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hf : ∀ n, n + 1 ≤ 2 ^ ((n + 1) ^ (k + 1)) := by
      intro n
      refine le_trans (le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by omega) ?_)
      exact Nat.le_self_pow (by omega) _
    have hd := savitch (fun n => (n + 1) ^ (k + 1)) hf hmono
    refine ⟨2 * (k + 1), ?_⟩
    have hfun : (fun n => ((n + 1) ^ (k + 1)) ^ 2) = (fun n : ℕ => (n + 1) ^ (2 * (k + 1))) := by
      funext n
      rw [← pow_mul, Nat.mul_comm]
    rwa [hfun] at hd

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

/-
# The Savitch predicate computes reachability

`CY n k a b` (the value computed by the simulator) holds exactly when `b` is
reachable from `a` in at most `2 ^ k` steps of `N`, using only intermediate
configurations from the candidate list.  Combined with the elementary distance
bound this shows that the simulator accepts exactly when `N` accepts.
-/
import Mathlib
import RequestProject.Savitch.Model
import RequestProject.Savitch.Walk
import RequestProject.Savitch.Sim

namespace CS

attribute [local instance] Classical.propDecidable

noncomputable section

variable {N : Machine} {S : ℕ → Finset N.Mem} {g : ℕ → ℕ} {x : List Bool}

theorem reach_iff_walk (m : N.Mem) :
    Reach N x m ↔ ∃ t, Walk (stepR N x) t N.start m := by
  constructor
  · intro h
    induction h with
    | start => exact ⟨0, rfl⟩
    | @step a b _ hab iha =>
      obtain ⟨t, ht⟩ := iha
      exact ⟨t + 1, ⟨a, ht, hab⟩⟩
  · rintro ⟨t, ht⟩
    induction t generalizing m with
    | zero => cases ht; exact Reach.start
    | succ t iht =>
      obtain ⟨c, hc, hcm⟩ := ht
      exact Reach.step (iht c hc) hcm

theorem reach_of_walk {a b : N.Mem} (ha : Reach N x a) :
    ∀ (t : ℕ), Walk (stepR N x) t a b → Reach N x b := by
  intro t
  induction t generalizing b with
  | zero => intro h; cases h; exact ha
  | succ t iht =>
    rintro ⟨c, hc, hcb⟩
    exact Reach.step (iht hc) hcb

/-- Soundness: the Savitch predicate only reports genuine reachability. -/
theorem CY_sound (n : ℕ) :
    ∀ (k : ℕ) (a b : N.Mem), CY N S x n k a b → ∃ t, Walk (stepR N x) t a b := by
  intro k
  induction k with
  | zero =>
    intro a b h
    rcases h with rfl | h
    · exact ⟨0, rfl⟩
    · exact ⟨1, ⟨a, rfl, h⟩⟩
  | succ k ihk =>
    rintro a b ⟨m, -, h1, h2⟩
    obtain ⟨t1, ht1⟩ := ihk a m h1
    obtain ⟨t2, ht2⟩ := ihk m b h2
    exact ⟨t1 + t2, ht1.trans ht2⟩

/-- Completeness: a short walk between reachable configurations is found by the
Savitch predicate. -/
theorem CY_complete (hS : ∀ (y : List Bool) (m : N.Mem), Reach N y m → m ∈ S y.length) :
    ∀ (k t : ℕ) (a b : N.Mem), Reach N x a → Walk (stepR N x) t a b → t ≤ 2 ^ k →
      CY N S x x.length k a b := by
  intro k
  induction k with
  | zero =>
    intro t a b _ hw ht
    interval_cases t
    · exact Or.inl hw
    · obtain ⟨c, hc, hcb⟩ := hw
      cases hc
      exact Or.inr hcb
  | succ k ihk =>
    intro t a b ha hw ht
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    set i := min t (2 ^ k) with hi
    have hile : i ≤ t := Nat.min_le_left _ _
    obtain ⟨c, hac, hcb⟩ := hw.split i hile
    have hc_reach : Reach N x c := reach_of_walk ha i hac
    have hc_mem : c ∈ cands N S x.length := by
      rw [cands, Finset.mem_toList]
      exact hS x c hc_reach
    have h1 : i ≤ 2 ^ k := Nat.min_le_right _ _
    have h2 : t - i ≤ 2 ^ k := by omega
    exact ⟨c, hc_mem, ihk i a c ha hac h1, ihk (t - i) c b hc_reach hcb h2⟩

/-- The Savitch search succeeds exactly when `N` accepts. -/
theorem CY_search_iff_accepts
    (hS : ∀ (y : List Bool) (m : N.Mem), Reach N y m → m ∈ S y.length)
    (hcard : ∀ n, (S n).card ≤ 2 ^ g n) :
    (∃ b ∈ cands N S x.length, N.acc b ∧ CY N S x x.length (g x.length) N.start b) ↔
      Accepts N x := by
  constructor
  · rintro ⟨b, -, hb, hcy⟩
    obtain ⟨t, ht⟩ := CY_sound (S := S) x.length (g x.length) N.start b hcy
    exact ⟨b, reach_of_walk Reach.start t ht, hb⟩
  · rintro ⟨m, hm, hacc⟩
    have hwalks : ∀ (c : N.Mem) (t : ℕ), Walk (stepR N x) t N.start c → c ∈ S x.length := by
      intro c t hw
      exact hS x c ((reach_iff_walk c).mpr ⟨t, hw⟩)
    obtain ⟨t, htlt, hw⟩ :=
      exists_short_walk (S x.length) N.start m hwalks ((reach_iff_walk m).mp hm)
    have htle : t ≤ 2 ^ g x.length := le_trans (Nat.le_of_lt_succ (by omega)) (hcard x.length)
    refine ⟨m, ?_, hacc, ?_⟩
    · rw [cands, Finset.mem_toList]
      exact hS x m hm
    · exact CY_complete hS (g x.length) t N.start m Reach.start hw htle

end

end CS

/-
# The Savitch simulator

Given a nondeterministic machine `N` whose reachable memory values on inputs of
length `n` are contained in a finite set `S n` of size at most `2 ^ g n`, we
build a deterministic machine which decides acceptance of `N` by the recursive
midpoint search of Savitch's theorem, implemented as an explicit stack machine.
-/
import Mathlib
import RequestProject.Savitch.Model
import RequestProject.Savitch.Walk

namespace CS

attribute [local instance] Classical.propDecidable

noncomputable section

variable (N : Machine) (S : ℕ → Finset N.Mem) (g : ℕ → ℕ)

/-- A stack frame of the recursive midpoint search: we are computing
`CanYield a b (k+1)` by trying the midpoints `cur :: rest` in order; `second`
records whether we are checking the first or the second half. -/
structure Frame (α : Type) where
  /-- Source configuration of the subproblem. -/
  a : α
  /-- Target configuration of the subproblem. -/
  b : α
  /-- Level of the two recursive subcalls. -/
  k : ℕ
  /-- The midpoint currently being tried. -/
  cur : α
  /-- The midpoints still to be tried. -/
  rest : List α
  /-- `false`: checking `a ⇝ cur`; `true`: checking `cur ⇝ b`. -/
  second : Bool

/-- Memory values of the simulator. -/
inductive SMem (α : Type) where
  /-- Scanning the input to determine its length. -/
  | scan (i : ℕ)
  /-- Looking for an accepting target among `todo`. -/
  | outer (n : ℕ) (todo : List α)
  /-- Evaluating `CanYield a b k` with the given stack of pending frames. -/
  | call (n : ℕ) (todo : List α) (a b : α) (k : ℕ) (st : List (Frame α))
  /-- Returning the value `v` to the stack. -/
  | ret (n : ℕ) (todo : List α) (v : Bool) (st : List (Frame α))
  /-- The accepting (absorbing) memory value. -/
  | acc

/-- The list of candidate configurations on inputs of length `n`. -/
def cands (n : ℕ) : List N.Mem := (S n).toList

/-- The transition function of the simulator. -/
def stepD (m : SMem N.Mem) (o : Option Bool) : SMem N.Mem :=
  match m with
  | .scan i => match o with
      | some _ => .scan (i + 1)
      | none => .outer i (cands N S i)
  | .outer n todo => match todo with
      | [] => .outer n []
      | b :: bs => if N.acc b then .call n bs N.start b (g n) [] else .outer n bs
  | .call n todo a b k st => match k with
      | 0 => .ret n todo (decide (a = b ∨ b ∈ N.next a o)) st
      | k + 1 => match cands N S n with
          | [] => .ret n todo false st
          | m :: ms => .call n todo a m k (⟨a, b, k, m, ms, false⟩ :: st)
  | .ret n todo v st => match st with
      | [] => if v then .acc else .outer n todo
      | fr :: st' =>
          if v then
            (if fr.second then .ret n todo true st'
             else .call n todo fr.cur fr.b fr.k
                    (⟨fr.a, fr.b, fr.k, fr.cur, fr.rest, true⟩ :: st'))
          else
            match fr.rest with
            | [] => .ret n todo false st'
            | m :: ms => .call n todo fr.a m fr.k (⟨fr.a, fr.b, fr.k, m, ms, false⟩ :: st')
  | .acc => .acc

/-- The input position read by the simulator. -/
def headD : SMem N.Mem → ℕ
  | .scan i => i
  | .call _ _ a _ 0 _ => N.head a
  | _ => 0

/-- The deterministic simulator machine. -/
def simMachine : Machine where
  Mem := SMem N.Mem
  start := .scan 0
  head := headD N
  next := fun m o => {stepD N S g m o}
  acc := fun m => m = .acc

theorem simMachine_det : Deterministic (simMachine N S g) := fun _ _ => ⟨_, rfl⟩

section Correctness

variable (x : List Bool)

/-- One deterministic step of the simulator on input `x`. -/
def dstep (m : SMem N.Mem) : SMem N.Mem := stepD N S g m x[headD N m]?

/-- The step relation of `N` on input `x`. -/
def stepR (a b : N.Mem) : Prop := b ∈ N.next a x[N.head a]?

/-- The Savitch predicate: `CY n k a b` says that `b` can be reached from `a`
in at most `2 ^ k` steps, using midpoints from the candidate list. -/
def CY (n : ℕ) : ℕ → N.Mem → N.Mem → Prop
  | 0, a, b => a = b ∨ stepR N x a b
  | (k + 1), a, b => ∃ m ∈ cands N S n, CY n k a m ∧ CY n k m b

/-- Reachability for the (deterministic) simulator on input `x`. -/
def SReach (m m' : SMem N.Mem) : Prop := ∃ t, (dstep N S g x)^[t] m = m'

variable {N S g x}

theorem SReach.rfl' (m : SMem N.Mem) : SReach N S g x m m := ⟨0, rfl⟩

theorem SReach.one (m : SMem N.Mem) : SReach N S g x m (dstep N S g x m) := ⟨1, rfl⟩

theorem SReach.one' {m m' : SMem N.Mem} (h : dstep N S g x m = m') : SReach N S g x m m' :=
  ⟨1, h⟩

theorem SReach.trans' {m₁ m₂ m₃ : SMem N.Mem} (h₁ : SReach N S g x m₁ m₂)
    (h₂ : SReach N S g x m₂ m₃) : SReach N S g x m₁ m₃ := by
  obtain ⟨t₁, ht₁⟩ := h₁
  obtain ⟨t₂, ht₂⟩ := h₂
  exact ⟨t₂ + t₁, by rw [Function.iterate_add_apply, ht₁, ht₂]⟩

theorem dstep_scan_some {i : ℕ} (h : (x[i]? : Option Bool).isSome) :
    dstep N S g x (.scan i) = .scan (i + 1) := by
  simp only [dstep, headD, stepD]
  cases hx : x[i]? with
  | none => rw [hx] at h; simp at h
  | some b => simp

theorem dstep_scan_none {i : ℕ} (h : x[i]? = none) :
    dstep N S g x (.scan i) = .outer i (cands N S i) := by
  simp only [dstep, headD, stepD, h]

theorem dstep_outer_nil {n : ℕ} : dstep N S g x (.outer n []) = .outer n [] := rfl

theorem dstep_outer_cons_acc {n : ℕ} {b : N.Mem} {bs : List N.Mem} (h : N.acc b) :
    dstep N S g x (.outer n (b :: bs)) = .call n bs N.start b (g n) [] := by
  simp only [dstep, stepD, if_pos h]

theorem dstep_outer_cons_not_acc {n : ℕ} {b : N.Mem} {bs : List N.Mem} (h : ¬ N.acc b) :
    dstep N S g x (.outer n (b :: bs)) = .outer n bs := by
  simp only [dstep, stepD, if_neg h]

theorem dstep_call_zero {n : ℕ} {todo : List N.Mem} {a b : N.Mem} {st : List (Frame N.Mem)} :
    dstep N S g x (.call n todo a b 0 st)
      = .ret n todo (decide (a = b ∨ stepR N x a b)) st := rfl

theorem dstep_call_succ_nil {n k : ℕ} {todo : List N.Mem} {a b : N.Mem}
    {st : List (Frame N.Mem)} (h : cands N S n = []) :
    dstep N S g x (.call n todo a b (k + 1) st) = .ret n todo false st := by
  simp only [dstep, stepD, h]

theorem dstep_call_succ_cons {n k : ℕ} {todo : List N.Mem} {a b m : N.Mem}
    {ms : List N.Mem} {st : List (Frame N.Mem)} (h : cands N S n = m :: ms) :
    dstep N S g x (.call n todo a b (k + 1) st)
      = .call n todo a m k (⟨a, b, k, m, ms, false⟩ :: st) := by
  simp only [dstep, stepD, h]

theorem dstep_ret_nil_true {n : ℕ} {todo : List N.Mem} :
    dstep N S g x (.ret n todo true []) = .acc := rfl

theorem dstep_ret_nil_false {n : ℕ} {todo : List N.Mem} :
    dstep N S g x (.ret n todo false []) = .outer n todo := rfl

theorem dstep_ret_true_second {n : ℕ} {todo : List N.Mem} {fr : Frame N.Mem}
    {st : List (Frame N.Mem)} (h : fr.second = true) :
    dstep N S g x (.ret n todo true (fr :: st)) = .ret n todo true st := by
  simp only [dstep, stepD, h, if_pos]

theorem dstep_ret_true_first {n : ℕ} {todo : List N.Mem} {fr : Frame N.Mem}
    {st : List (Frame N.Mem)} (h : fr.second = false) :
    dstep N S g x (.ret n todo true (fr :: st))
      = .call n todo fr.cur fr.b fr.k (⟨fr.a, fr.b, fr.k, fr.cur, fr.rest, true⟩ :: st) := by
  simp only [dstep, stepD, h, if_true, Bool.false_eq_true, if_false]

theorem dstep_ret_false_nil {n : ℕ} {todo : List N.Mem} {fr : Frame N.Mem}
    {st : List (Frame N.Mem)} (h : fr.rest = []) :
    dstep N S g x (.ret n todo false (fr :: st)) = .ret n todo false st := by
  simp only [dstep, stepD, h, Bool.false_eq_true, if_false]

theorem dstep_ret_false_cons {n : ℕ} {todo : List N.Mem} {fr : Frame N.Mem} {m : N.Mem}
    {ms : List N.Mem} {st : List (Frame N.Mem)} (h : fr.rest = m :: ms) :
    dstep N S g x (.ret n todo false (fr :: st))
      = .call n todo fr.a m fr.k (⟨fr.a, fr.b, fr.k, m, ms, false⟩ :: st) := by
  simp only [dstep, stepD, h, Bool.false_eq_true, if_false]

theorem dstep_acc : dstep N S g x (SMem.acc : SMem N.Mem) = .acc := rfl

/-- The inner loop over midpoints: starting from the state that tests the first
half for midpoint `m`, the machine returns whether some midpoint in `m :: ms`
works. -/
theorem loop_eval {n k : ℕ}
    (ih : ∀ (todo : List N.Mem) (a b : N.Mem) (st : List (Frame N.Mem)),
      SReach N S g x (.call n todo a b k st) (.ret n todo (decide (CY N S x n k a b)) st)) :
    ∀ (ms : List N.Mem) (todo : List N.Mem) (a b m : N.Mem) (st : List (Frame N.Mem)),
      SReach N S g x (.call n todo a m k (⟨a, b, k, m, ms, false⟩ :: st))
        (.ret n todo (decide (∃ mm ∈ m :: ms, CY N S x n k a mm ∧ CY N S x n k mm b)) st) := by
  intro ms
  induction ms with
  | nil =>
    intro todo a b m st
    by_cases hP : CY N S x n k a m
    · have s1 : SReach N S g x (.call n todo a m k (⟨a, b, k, m, [], false⟩ :: st))
          (.ret n todo true (⟨a, b, k, m, [], false⟩ :: st)) := by
        have h := ih todo a m (⟨a, b, k, m, [], false⟩ :: st)
        rwa [decide_eq_true hP] at h
      have s2 : SReach N S g x (.ret n todo true ((⟨a, b, k, m, [], false⟩ : Frame N.Mem) :: st))
          (.call n todo m b k (⟨a, b, k, m, [], true⟩ :: st)) :=
        SReach.one' (dstep_ret_true_first rfl)
      by_cases hQ : CY N S x n k m b
      · have s3 : SReach N S g x (.call n todo m b k (⟨a, b, k, m, [], true⟩ :: st))
            (.ret n todo true (⟨a, b, k, m, [], true⟩ :: st)) := by
          have h := ih todo m b (⟨a, b, k, m, [], true⟩ :: st)
          rwa [decide_eq_true hQ] at h
        have s4 : SReach N S g x (.ret n todo true ((⟨a, b, k, m, [], true⟩ : Frame N.Mem) :: st))
            (.ret n todo true st) := SReach.one' (dstep_ret_true_second rfl)
        have hval : (decide (∃ mm ∈ [m], CY N S x n k a mm ∧ CY N S x n k mm b)) = true :=
          decide_eq_true ⟨m, by simp, hP, hQ⟩
        rw [hval]
        exact s1.trans' (s2.trans' (s3.trans' s4))
      · have s3 : SReach N S g x (.call n todo m b k (⟨a, b, k, m, [], true⟩ :: st))
            (.ret n todo false (⟨a, b, k, m, [], true⟩ :: st)) := by
          have h := ih todo m b (⟨a, b, k, m, [], true⟩ :: st)
          rwa [decide_eq_false hQ] at h
        have s4 : SReach N S g x (.ret n todo false ((⟨a, b, k, m, [], true⟩ : Frame N.Mem) :: st))
            (.ret n todo false st) := SReach.one' (dstep_ret_false_nil rfl)
        have hval : (decide (∃ mm ∈ [m], CY N S x n k a mm ∧ CY N S x n k mm b)) = false := by
          refine decide_eq_false ?_
          rintro ⟨mm, hmm, -, h2⟩
          rw [List.mem_singleton] at hmm
          subst hmm
          exact hQ h2
        rw [hval]
        exact s1.trans' (s2.trans' (s3.trans' s4))
    · have s1 : SReach N S g x (.call n todo a m k (⟨a, b, k, m, [], false⟩ :: st))
          (.ret n todo false (⟨a, b, k, m, [], false⟩ :: st)) := by
        have h := ih todo a m (⟨a, b, k, m, [], false⟩ :: st)
        rwa [decide_eq_false hP] at h
      have s2 : SReach N S g x (.ret n todo false ((⟨a, b, k, m, [], false⟩ : Frame N.Mem) :: st))
          (.ret n todo false st) := SReach.one' (dstep_ret_false_nil rfl)
      have hval : (decide (∃ mm ∈ [m], CY N S x n k a mm ∧ CY N S x n k mm b)) = false := by
        refine decide_eq_false ?_
        rintro ⟨mm, hmm, h1, -⟩
        rw [List.mem_singleton] at hmm
        subst hmm
        exact hP h1
      rw [hval]
      exact s1.trans' s2
  | cons m2 ms2 ihms =>
    intro todo a b m st
    by_cases hP : CY N S x n k a m
    · have s1 : SReach N S g x (.call n todo a m k (⟨a, b, k, m, m2 :: ms2, false⟩ :: st))
          (.ret n todo true (⟨a, b, k, m, m2 :: ms2, false⟩ :: st)) := by
        have h := ih todo a m (⟨a, b, k, m, m2 :: ms2, false⟩ :: st)
        rwa [decide_eq_true hP] at h
      have s2 : SReach N S g x
          (.ret n todo true ((⟨a, b, k, m, m2 :: ms2, false⟩ : Frame N.Mem) :: st))
          (.call n todo m b k (⟨a, b, k, m, m2 :: ms2, true⟩ :: st)) :=
        SReach.one' (dstep_ret_true_first rfl)
      by_cases hQ : CY N S x n k m b
      · have s3 : SReach N S g x (.call n todo m b k (⟨a, b, k, m, m2 :: ms2, true⟩ :: st))
            (.ret n todo true (⟨a, b, k, m, m2 :: ms2, true⟩ :: st)) := by
          have h := ih todo m b (⟨a, b, k, m, m2 :: ms2, true⟩ :: st)
          rwa [decide_eq_true hQ] at h
        have s4 : SReach N S g x
            (.ret n todo true ((⟨a, b, k, m, m2 :: ms2, true⟩ : Frame N.Mem) :: st))
            (.ret n todo true st) := SReach.one' (dstep_ret_true_second rfl)
        have hval :
            (decide (∃ mm ∈ m :: m2 :: ms2, CY N S x n k a mm ∧ CY N S x n k mm b)) = true :=
          decide_eq_true ⟨m, by simp, hP, hQ⟩
        rw [hval]
        exact s1.trans' (s2.trans' (s3.trans' s4))
      · have s3 : SReach N S g x (.call n todo m b k (⟨a, b, k, m, m2 :: ms2, true⟩ :: st))
            (.ret n todo false (⟨a, b, k, m, m2 :: ms2, true⟩ :: st)) := by
          have h := ih todo m b (⟨a, b, k, m, m2 :: ms2, true⟩ :: st)
          rwa [decide_eq_false hQ] at h
        have s4 : SReach N S g x
            (.ret n todo false ((⟨a, b, k, m, m2 :: ms2, true⟩ : Frame N.Mem) :: st))
            (.call n todo a m2 k (⟨a, b, k, m2, ms2, false⟩ :: st)) :=
          SReach.one' (dstep_ret_false_cons rfl)
        have hiff : (∃ mm ∈ m :: m2 :: ms2, CY N S x n k a mm ∧ CY N S x n k mm b) ↔
            (∃ mm ∈ m2 :: ms2, CY N S x n k a mm ∧ CY N S x n k mm b) := by
          constructor
          · rintro ⟨mm, hmm, h1, h2⟩
            rcases List.mem_cons.mp hmm with rfl | hmm'
            · exact absurd h2 hQ
            · exact ⟨mm, hmm', h1, h2⟩
          · rintro ⟨mm, hmm, h1, h2⟩
            exact ⟨mm, List.mem_cons_of_mem _ hmm, h1, h2⟩
        rw [decide_eq_decide.mpr hiff]
        exact s1.trans' (s2.trans' (s3.trans' (s4.trans' (ihms todo a b m2 st))))
    · have s1 : SReach N S g x (.call n todo a m k (⟨a, b, k, m, m2 :: ms2, false⟩ :: st))
          (.ret n todo false (⟨a, b, k, m, m2 :: ms2, false⟩ :: st)) := by
        have h := ih todo a m (⟨a, b, k, m, m2 :: ms2, false⟩ :: st)
        rwa [decide_eq_false hP] at h
      have s2 : SReach N S g x
          (.ret n todo false ((⟨a, b, k, m, m2 :: ms2, false⟩ : Frame N.Mem) :: st))
          (.call n todo a m2 k (⟨a, b, k, m2, ms2, false⟩ :: st)) :=
        SReach.one' (dstep_ret_false_cons rfl)
      have hiff : (∃ mm ∈ m :: m2 :: ms2, CY N S x n k a mm ∧ CY N S x n k mm b) ↔
          (∃ mm ∈ m2 :: ms2, CY N S x n k a mm ∧ CY N S x n k mm b) := by
        constructor
        · rintro ⟨mm, hmm, h1, h2⟩
          rcases List.mem_cons.mp hmm with rfl | hmm'
          · exact absurd h1 hP
          · exact ⟨mm, hmm', h1, h2⟩
        · rintro ⟨mm, hmm, h1, h2⟩
          exact ⟨mm, List.mem_cons_of_mem _ hmm, h1, h2⟩
      rw [decide_eq_decide.mpr hiff]
      exact s1.trans' (s2.trans' (ihms todo a b m2 st))

/-- Correctness of the recursive procedure: a call at level `k` returns the
truth value of `CY n k a b`. -/
theorem eval (n : ℕ) : ∀ (k : ℕ) (todo : List N.Mem) (a b : N.Mem) (st : List (Frame N.Mem)),
    SReach N S g x (.call n todo a b k st) (.ret n todo (decide (CY N S x n k a b)) st) := by
  intro k
  induction k with
  | zero =>
    intro todo a b st
    have hval : (decide (CY N S x n 0 a b)) = decide (a = b ∨ stepR N x a b) :=
      decide_eq_decide.mpr Iff.rfl
    rw [hval]
    exact SReach.one' dstep_call_zero
  | succ k ihk =>
    intro todo a b st
    cases hc : cands N S n with
    | nil =>
      have hval : (decide (CY N S x n (k + 1) a b)) = false := by
        refine decide_eq_false ?_
        rintro ⟨mm, hmm, -⟩
        rw [hc] at hmm
        exact absurd hmm (List.not_mem_nil)
      rw [hval]
      exact SReach.one' (dstep_call_succ_nil hc)
    | cons m ms =>
      have s1 : SReach N S g x (.call n todo a b (k + 1) st)
          (.call n todo a m k (⟨a, b, k, m, ms, false⟩ :: st)) :=
        SReach.one' (dstep_call_succ_cons hc)
      have s2 := loop_eval ihk ms todo a b m st
      have hiff : CY N S x n (k + 1) a b ↔
          (∃ mm ∈ m :: ms, CY N S x n k a mm ∧ CY N S x n k mm b) := by
        rw [CY, hc]
      rw [decide_eq_decide.mpr hiff]
      exact s1.trans' s2

/-! ### The outer loop and the scanning phase -/

theorem iter_acc (t : ℕ) : (dstep N S g x)^[t] (SMem.acc : SMem N.Mem) = .acc :=
  Function.iterate_fixed dstep_acc t

theorem iter_acc_mono {m : SMem N.Mem} {i j : ℕ} (h : (dstep N S g x)^[i] m = .acc)
    (hij : i ≤ j) : (dstep N S g x)^[j] m = .acc := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  have hcomm : i + d = d + i := by omega
  rw [hcomm, Function.iterate_add_apply, h, iter_acc]

/-- If some target in `todo` is accepting and reachable, the simulator accepts. -/
theorem outer_accept {n : ℕ} :
    ∀ (todo : List N.Mem), (∃ b ∈ todo, N.acc b ∧ CY N S x n (g n) N.start b) →
      SReach N S g x (.outer n todo) .acc := by
  intro todo
  induction todo with
  | nil => rintro ⟨b, hb, -⟩; exact absurd hb (List.not_mem_nil)
  | cons b bs ih =>
    rintro ⟨b', hb', hacc', hcy'⟩
    by_cases hb : N.acc b
    · have s1 : SReach N S g x (.outer n (b :: bs)) (.call n bs N.start b (g n) []) :=
        SReach.one' (dstep_outer_cons_acc hb)
      have s2 := eval (N := N) (S := S) (g := g) (x := x) n (g n) bs N.start b []
      by_cases hcy : CY N S x n (g n) N.start b
      · rw [decide_eq_true hcy] at s2
        exact s1.trans' (s2.trans' (SReach.one' dstep_ret_nil_true))
      · rw [decide_eq_false hcy] at s2
        have s3 : SReach N S g x (.ret n bs false ([] : List (Frame N.Mem))) (.outer n bs) :=
          SReach.one' dstep_ret_nil_false
        refine s1.trans' (s2.trans' (s3.trans' (ih ?_)))
        rcases List.mem_cons.mp hb' with rfl | hb''
        · exact absurd hcy' hcy
        · exact ⟨b', hb'', hacc', hcy'⟩
    · have s1 : SReach N S g x (.outer n (b :: bs)) (.outer n bs) :=
        SReach.one' (dstep_outer_cons_not_acc hb)
      refine s1.trans' (ih ?_)
      rcases List.mem_cons.mp hb' with rfl | hb''
      · exact absurd hacc' hb
      · exact ⟨b', hb'', hacc', hcy'⟩

/-- If no target in `todo` is accepting and reachable, the simulator never
accepts from the outer loop. -/
theorem outer_reject {n : ℕ} :
    ∀ (todo : List N.Mem), (∀ b ∈ todo, ¬ (N.acc b ∧ CY N S x n (g n) N.start b)) →
      ∀ t, (dstep N S g x)^[t] (.outer n todo) ≠ .acc := by
  intro todo
  induction todo with
  | nil =>
    intro _ t
    rw [Function.iterate_fixed dstep_outer_nil t]
    simp
  | cons b bs ih =>
    intro hno t
    have hbs : ∀ b' ∈ bs, ¬ (N.acc b' ∧ CY N S x n (g n) N.start b') := fun b' hb' =>
      hno b' (List.mem_cons_of_mem _ hb')
    by_cases hb : N.acc b
    · have hcy : ¬ CY N S x n (g n) N.start b := fun h => hno b List.mem_cons_self ⟨hb, h⟩
      obtain ⟨t0, ht0⟩ := eval (N := N) (S := S) (g := g) (x := x) n (g n) bs N.start b []
      rw [decide_eq_false hcy] at ht0
      have e1 : (dstep N S g x)^[1] (SMem.outer n (b :: bs))
          = .call n bs N.start b (g n) [] := by
        simpa using dstep_outer_cons_acc (S := S) (g := g) (x := x) hb
      have e2 : (dstep N S g x)^[1 + t0] (SMem.call n bs N.start b (g n) [])
          = .outer n bs := by
        rw [Function.iterate_add_apply, ht0]
        simpa using dstep_ret_nil_false (N := N) (S := S) (g := g) (x := x) (n := n) (todo := bs)
      have hstep : (dstep N S g x)^[(1 + t0) + 1] (SMem.outer n (b :: bs)) = .outer n bs := by
        rw [Function.iterate_add_apply, e1, e2]
      rcases Nat.lt_or_ge t ((1 + t0) + 1) with hlt | hge
      · intro hcon
        have hacc := iter_acc_mono hcon (le_of_lt hlt)
        rw [hstep] at hacc
        simp at hacc
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hge
        have hcomm : (1 + t0) + 1 + d = d + ((1 + t0) + 1) := by omega
        rw [hcomm, Function.iterate_add_apply, hstep]
        exact ih hbs d
    · cases t with
      | zero => simp
      | succ t =>
        rw [Function.iterate_succ_apply, dstep_outer_cons_not_acc hb]
        exact ih hbs t

theorem scan_iter : ∀ j ≤ x.length, (dstep N S g x)^[j] (SMem.scan 0 : SMem N.Mem) = .scan j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hjl : j < x.length := by omega
    have h1 : (dstep N S g x)^[j] (SMem.scan 0 : SMem N.Mem) = .scan j := ih (by omega)
    rw [Function.iterate_succ_apply', h1]
    refine dstep_scan_some ?_
    rw [List.getElem?_eq_getElem hjl]
    simp

theorem scan_done : (dstep N S g x)^[x.length + 1] (SMem.scan 0 : SMem N.Mem)
    = .outer x.length (cands N S x.length) := by
  rw [Function.iterate_succ_apply', scan_iter x.length le_rfl]
  exact dstep_scan_none (List.getElem?_eq_none le_rfl)

theorem simReach_iff (m : SMem N.Mem) :
    Reach (simMachine N S g) x m ↔ ∃ t, (dstep N S g x)^[t] (SMem.scan 0 : SMem N.Mem) = m :=
  reach_det_iff (M := simMachine N S g) (dstep N S g x) (fun _ => rfl) m

theorem simAccepts_iff :
    Accepts (simMachine N S g) x ↔
      ∃ t, (dstep N S g x)^[t] (SMem.scan 0 : SMem N.Mem) = .acc := by
  constructor
  · rintro ⟨m, hm, hacc⟩
    have hm' : m = SMem.acc := hacc
    subst hm'
    exact (simReach_iff _).mp hm
  · rintro ⟨t, ht⟩
    exact ⟨SMem.acc, (simReach_iff _).mpr ⟨t, ht⟩, rfl⟩

/-- The simulator accepts exactly when some accepting candidate configuration is
found by the Savitch search. -/
theorem simAccepts_iff_CY :
    Accepts (simMachine N S g) x ↔
      ∃ b ∈ cands N S x.length, N.acc b ∧ CY N S x x.length (g x.length) N.start b := by
  rw [simAccepts_iff]
  constructor
  · intro h
    by_contra hno
    push_neg at hno
    have hno' : ∀ b ∈ cands N S x.length,
        ¬ (N.acc b ∧ CY N S x x.length (g x.length) N.start b) := by
      intro b hb ⟨h1, h2⟩
      exact hno b hb h1 h2
    obtain ⟨t, ht⟩ := h
    rcases Nat.lt_or_ge t (x.length + 1) with hlt | hge
    · rw [scan_iter t (by omega)] at ht
      simp at ht
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hge
      have hcomm : x.length + 1 + d = d + (x.length + 1) := by omega
      rw [hcomm, Function.iterate_add_apply, scan_done] at ht
      exact outer_reject _ hno' d ht
  · intro h
    obtain ⟨t, ht⟩ := outer_accept (g := g) _ h
    refine ⟨t + (x.length + 1), ?_⟩
    rw [Function.iterate_add_apply, scan_done, ht]

end Correctness

end

end CS

/-
# A machine model for space-bounded computation

We use the standard "bounded-memory machine with a read-only random-access
input" model of space-bounded computation:

* a machine has a memory type `Mem` with a distinguished initial memory `start`;
* the memory determines a position `head m` of the input which the machine
  currently reads;
* the transition `next m o` gives the set of possible successor memories, where
  `o : Option Bool` is the bit read (`none` if the head is past the end of the
  input, so that the machine can detect the length of its input);
* `acc` marks the accepting memory values, and the machine accepts `x` if some
  accepting memory is reachable.

Space is measured in the standard way: a machine works in space `g` if on every
input of length `n` all reachable memory values lie in a fixed set of at most
`2 ^ g n` values (a machine using `s` tape cells over a finite alphabet has
`2 ^ O(s)` configurations, and conversely).
-/
import Mathlib

namespace CS

/-- A (nondeterministic) space-bounded machine with read-only random access
to the input. -/
structure Machine where
  /-- The type of memory values (configurations) of the machine. -/
  Mem : Type
  /-- The initial memory value. -/
  start : Mem
  /-- The input position that the machine reads in a given memory value. -/
  head : Mem → ℕ
  /-- The possible successor memory values, given the bit currently read
  (`none` if the head is beyond the end of the input). -/
  next : Mem → Option Bool → Set Mem
  /-- The accepting memory values. -/
  acc : Mem → Prop

/-- The memory values reachable by `M` on input `x`. -/
inductive Reach (M : Machine) (x : List Bool) : M.Mem → Prop
  | start : Reach M x M.start
  | step {a b : M.Mem} : Reach M x a → b ∈ M.next a x[M.head a]? → Reach M x b

/-- `M` accepts `x` if some accepting memory value is reachable. -/
def Accepts (M : Machine) (x : List Bool) : Prop :=
  ∃ m, Reach M x m ∧ M.acc m

/-- For a machine whose transition on input `x` is given by the function `f`,
the reachable memory values are exactly the iterates of `f` on `start`. -/
theorem reach_det_iff {M : Machine} {x : List Bool} (f : M.Mem → M.Mem)
    (hf : ∀ m, M.next m x[M.head m]? = {f m}) (m : M.Mem) :
    Reach M x m ↔ ∃ t, f^[t] M.start = m := by
  constructor
  · intro h
    induction h with
    | start => exact ⟨0, rfl⟩
    | @step a b _ hab iha =>
      obtain ⟨t, ht⟩ := iha
      rw [hf a] at hab
      refine ⟨t + 1, ?_⟩
      rw [Function.iterate_succ_apply', ht]
      exact (Set.mem_singleton_iff.mp hab).symm
  · rintro ⟨t, rfl⟩
    induction t with
    | zero => exact Reach.start
    | succ t iht =>
      rw [Function.iterate_succ_apply']
      refine Reach.step iht ?_
      rw [hf]
      exact Set.mem_singleton _

/-- A machine is deterministic if every transition has exactly one successor. -/
def Deterministic (M : Machine) : Prop :=
  ∀ m o, ∃ m', M.next m o = {m'}

/-- `M` works in space `g`: on inputs of length `n` all reachable memory values
lie in a set of size at most `2 ^ g n` depending only on `n`. -/
def InSpace (M : Machine) (g : ℕ → ℕ) : Prop :=
  ∃ S : ℕ → Finset M.Mem,
    (∀ x : List Bool, ∀ m, Reach M x m → m ∈ S x.length) ∧ ∀ n, (S n).card ≤ 2 ^ g n

/-- The class `NSPACE g`: languages recognized by a nondeterministic machine
working in space `O(g)`. -/
def NSPACE (g : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ (M : Machine) (c : ℕ), 0 < c ∧ InSpace M (fun n => c * g n + c) ∧
        ∀ x, x ∈ L ↔ Accepts M x}

/-- The class `DSPACE g`: languages recognized by a deterministic machine
working in space `O(g)`. -/
def DSPACE (g : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ (M : Machine) (c : ℕ), 0 < c ∧ Deterministic M ∧
        InSpace M (fun n => c * g n + c) ∧ ∀ x, x ∈ L ↔ Accepts M x}

/-- Polynomial space. -/
def PSPACE : Set (Set (List Bool)) :=
  {L | ∃ k : ℕ, L ∈ DSPACE (fun n => (n + 1) ^ k)}

/-- Nondeterministic polynomial space. -/
def NPSPACE : Set (Set (List Bool)) :=
  {L | ∃ k : ℕ, L ∈ NSPACE (fun n => (n + 1) ^ k)}

theorem DSPACE_subset_NSPACE (g : ℕ → ℕ) : DSPACE g ⊆ NSPACE g := by
  rintro L ⟨M, c, hc, -, hsp, hL⟩
  exact ⟨M, c, hc, hsp, hL⟩

theorem InSpace_mono {M : Machine} {g g' : ℕ → ℕ} (h : ∀ n, g n ≤ g' n)
    (hM : InSpace M g) : InSpace M g' := by
  obtain ⟨S, hS, hcard⟩ := hM
  exact ⟨S, hS, fun n => le_trans (hcard n) (Nat.pow_le_pow_right (by omega) (h n))⟩

theorem NSPACE_mono {g g' : ℕ → ℕ} (h : ∀ n, g n ≤ g' n) : NSPACE g ⊆ NSPACE g' := by
  rintro L ⟨M, c, hc, hsp, hL⟩
  exact ⟨M, c, hc, InSpace_mono (fun n => by have := h n; nlinarith) hsp, hL⟩

theorem DSPACE_mono {g g' : ℕ → ℕ} (h : ∀ n, g n ≤ g' n) : DSPACE g ⊆ DSPACE g' := by
  rintro L ⟨M, c, hc, hdet, hsp, hL⟩
  exact ⟨M, c, hc, hdet, InSpace_mono (fun n => by have := h n; nlinarith) hsp, hL⟩

end CS

/-
# The space bound for the Savitch simulator

The reachable memory values of the simulator on inputs of length `n` are
described by an explicit invariant: a stack of at most `g n` frames whose
entries range over the candidate configurations.  Counting these gives the
bound `2 ^ O((g n)^2)` on the number of reachable memory values.
-/
import Mathlib
import RequestProject.Savitch.Model
import RequestProject.Savitch.Walk
import RequestProject.Savitch.Sim

namespace CS

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Lists of bounded length over a finite set -/

/-- The finite set of lists of length at most `k` with entries in `A`. -/
def listsLE {β : Type} : ℕ → Finset β → Finset (List β)
  | 0, _ => {[]}
  | (k + 1), A => insert [] ((A ×ˢ listsLE k A).image (fun p => p.1 :: p.2))

theorem mem_listsLE {β : Type} {A : Finset β} :
    ∀ (k : ℕ) (l : List β), l.length ≤ k → (∀ y ∈ l, y ∈ A) → l ∈ listsLE k A := by
  intro k
  induction k with
  | zero =>
    intro l hl _
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [listsLE]
  | succ k ih =>
    intro l hl hmem
    cases l with
    | nil => simp [listsLE]
    | cons y ys =>
      refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(y, ys), ?_, rfl⟩)
      refine Finset.mem_product.mpr ⟨hmem y List.mem_cons_self, ?_⟩
      exact ih ys (by simpa using hl) (fun z hz => hmem z (List.mem_cons_of_mem _ hz))

theorem card_listsLE {β : Type} (A : Finset β) :
    ∀ k, (listsLE k A).card ≤ (A.card + 1) ^ k := by
  intro k
  induction k with
  | zero => simp [listsLE]
  | succ k ih =>
    have h1 : (listsLE (k + 1) A).card
        ≤ ((A ×ˢ listsLE k A).image (fun p => p.1 :: p.2)).card + 1 := by
      rw [listsLE]
      exact Finset.card_insert_le _ _
    have h2 : ((A ×ˢ listsLE k A).image (fun p => p.1 :: p.2)).card
        ≤ A.card * (listsLE k A).card := by
      calc ((A ×ˢ listsLE k A).image (fun p => p.1 :: p.2)).card
          ≤ (A ×ˢ listsLE k A).card := Finset.card_image_le
        _ = A.card * (listsLE k A).card := Finset.card_product _ _
    have h3 : (1 : ℕ) ≤ (A.card + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    have h4 : A.card * (listsLE k A).card ≤ A.card * (A.card + 1) ^ k :=
      Nat.mul_le_mul_left _ ih
    have : (A.card + 1) ^ (k + 1) = A.card * (A.card + 1) ^ k + (A.card + 1) ^ k := by
      ring
    omega

/-! ### The invariant -/

variable (N : Machine) (S : ℕ → Finset N.Mem) (g : ℕ → ℕ)

/-- Configurations that can occur as endpoints of subproblems. -/
def Bset (n : ℕ) : Finset N.Mem := insert N.start (S n)

/-- Validity of a stack frame. -/
def FrameOK (n : ℕ) (fr : Frame N.Mem) : Prop :=
  fr.a ∈ Bset N S n ∧ fr.b ∈ Bset N S n ∧ fr.cur ∈ Bset N S n ∧ fr.rest <:+ cands N S n

/-- `StackAt n k st`: `st` is a valid stack for a pending call at level `k`. -/
def StackAt (n : ℕ) : ℕ → List (Frame N.Mem) → Prop
  | k, [] => k = g n
  | k, fr :: st => fr.k = k ∧ FrameOK N S n fr ∧ StackAt n (k + 1) st

/-- The invariant satisfied by all memory values reachable on inputs of
length `n`. -/
def SInv (n : ℕ) : SMem N.Mem → Prop
  | .scan i => i ≤ n
  | .outer m todo => m = n ∧ todo <:+ cands N S n
  | .call m todo a b k st => m = n ∧ todo <:+ cands N S n ∧ a ∈ Bset N S n ∧
      b ∈ Bset N S n ∧ StackAt N S g n k st
  | .ret m todo _ st => m = n ∧ todo <:+ cands N S n ∧ ∃ k, StackAt N S g n k st
  | .acc => True

variable {N S g}

theorem mem_Bset_of_mem_cands {n : ℕ} {y : N.Mem} (h : y ∈ cands N S n) : y ∈ Bset N S n := by
  rw [cands, Finset.mem_toList] at h
  exact Finset.mem_insert_of_mem h

theorem mem_Bset_of_suffix {n : ℕ} {l : List N.Mem} (hl : l <:+ cands N S n) {y : N.Mem}
    (hy : y ∈ l) : y ∈ Bset N S n :=
  mem_Bset_of_mem_cands (hl.mem hy)

theorem stackAt_length {n : ℕ} : ∀ (st : List (Frame N.Mem)) (k : ℕ),
    StackAt N S g n k st → k + st.length = g n := by
  intro st
  induction st with
  | nil => intro k h; simpa using h
  | cons fr st ih =>
    intro k h
    obtain ⟨-, -, hst⟩ := h
    have := ih (k + 1) hst
    simp only [List.length_cons]
    omega

theorem stackAt_frames {n : ℕ} : ∀ (st : List (Frame N.Mem)) (k : ℕ),
    StackAt N S g n k st → ∀ fr ∈ st, FrameOK N S n fr ∧ fr.k ≤ g n := by
  intro st
  induction st with
  | nil => intro k _ fr hfr; exact absurd hfr (List.not_mem_nil)
  | cons fr0 st ih =>
    intro k h fr hfr
    have hlen := stackAt_length (fr0 :: st) k h
    obtain ⟨hk, hok, hst⟩ := h
    rcases List.mem_cons.mp hfr with rfl | hfr'
    · refine ⟨hok, ?_⟩
      simp only [List.length_cons] at hlen
      omega
    · exact ih (k + 1) hst fr hfr'

/-! ### The invariant is preserved -/

theorem SInv_step {x : List Bool} {n : ℕ} (hn : x.length = n) (m : SMem N.Mem)
    (h : SInv N S g n m) : SInv N S g n (dstep N S g x m) := by
  cases m with
  | scan i =>
    have hi : i ≤ n := h
    cases hx : x[i]? with
    | some c =>
      have hlt : i < x.length := by
        by_contra hc
        push_neg at hc
        rw [List.getElem?_eq_none hc] at hx
        simp at hx
      rw [dstep_scan_some (by rw [hx]; simp)]
      show i + 1 ≤ n
      omega
    | none =>
      have hge : x.length ≤ i := by
        by_contra hc
        push_neg at hc
        rw [List.getElem?_eq_getElem hc] at hx
        simp at hx
      have : i = n := by omega
      subst this
      rw [dstep_scan_none hx]
      exact ⟨rfl, List.suffix_rfl⟩
  | outer m todo =>
    obtain ⟨rfl, hsuf⟩ := h
    cases todo with
    | nil => rw [dstep_outer_nil]; exact ⟨rfl, hsuf⟩
    | cons b bs =>
      have hbs : bs <:+ cands N S m := (List.suffix_cons b bs).trans hsuf
      by_cases hb : N.acc b
      · rw [dstep_outer_cons_acc hb]
        exact ⟨rfl, hbs, Finset.mem_insert_self _ _,
          mem_Bset_of_suffix hsuf List.mem_cons_self, rfl⟩
      · rw [dstep_outer_cons_not_acc hb]
        exact ⟨rfl, hbs⟩
  | call m todo a b k st =>
    obtain ⟨rfl, hsuf, ha, hb, hst⟩ := h
    cases k with
    | zero =>
      rw [dstep_call_zero]
      exact ⟨rfl, hsuf, 0, hst⟩
    | succ k =>
      cases hc : cands N S m with
      | nil =>
        rw [dstep_call_succ_nil hc]
        exact ⟨rfl, hsuf, k + 1, hst⟩
      | cons m0 ms =>
        rw [dstep_call_succ_cons hc]
        have hm0 : m0 ∈ Bset N S m := mem_Bset_of_mem_cands (by rw [hc]; exact List.mem_cons_self)
        have hms : ms <:+ cands N S m := by
          rw [hc]; exact List.suffix_cons m0 ms
        exact ⟨rfl, hsuf, ha, hm0, rfl, ⟨ha, hb, hm0, hms⟩, hst⟩
  | ret m todo v st =>
    obtain ⟨rfl, hsuf, k, hst⟩ := h
    cases st with
    | nil =>
      cases v with
      | true => rw [dstep_ret_nil_true]; trivial
      | false => rw [dstep_ret_nil_false]; exact ⟨rfl, hsuf⟩
    | cons fr st' =>
      obtain ⟨hk, hok, hst'⟩ := hst
      cases v with
      | true =>
        cases hs : fr.second with
        | true =>
          rw [dstep_ret_true_second hs]
          exact ⟨rfl, hsuf, k + 1, hst'⟩
        | false =>
          rw [dstep_ret_true_first hs]
          refine ⟨rfl, hsuf, hok.2.2.1, hok.2.1, rfl, ⟨hok.1, hok.2.1, hok.2.2.1, hok.2.2.2⟩, ?_⟩
          rw [hk]
          exact hst'
      | false =>
        cases hr : fr.rest with
        | nil =>
          rw [dstep_ret_false_nil hr]
          exact ⟨rfl, hsuf, k + 1, hst'⟩
        | cons m0 ms =>
          rw [dstep_ret_false_cons hr]
          have hm0 : m0 ∈ Bset N S m :=
            mem_Bset_of_suffix hok.2.2.2 (by rw [hr]; exact List.mem_cons_self)
          have hms : ms <:+ cands N S m := (List.suffix_cons m0 ms).trans (by rw [← hr]; exact hok.2.2.2)
          refine ⟨rfl, hsuf, hok.1, hm0, rfl, ⟨hok.1, hok.2.1, hm0, hms⟩, ?_⟩
          rw [hk]
          exact hst'
  | acc => trivial

theorem SInv_iter {x : List Bool} {n : ℕ} (hn : x.length = n) (t : ℕ) :
    SInv N S g n ((dstep N S g x)^[t] (SMem.scan 0 : SMem N.Mem)) := by
  induction t with
  | zero => exact Nat.zero_le n
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact SInv_step hn _ ih

/-! ### Counting the memory values allowed by the invariant -/

variable (N S g)

/-- Suffixes of the candidate list. -/
def LSset (n : ℕ) : Finset (List N.Mem) := (cands N S n).tails.toFinset

/-- Valid stack frames. -/
def FFset (n : ℕ) : Finset (Frame N.Mem) :=
  ((Bset N S n) ×ˢ (Bset N S n) ×ˢ (Finset.range (g n + 1)) ×ˢ (Bset N S n) ×ˢ
      (LSset N S n) ×ˢ ({false, true} : Finset Bool)).image
    (fun p => (⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩ : Frame N.Mem))

/-- Valid stacks. -/
def STKset (n : ℕ) : Finset (List (Frame N.Mem)) := listsLE (g n) (FFset N S g n)

/-- A finite set containing every memory value allowed by the invariant. -/
def Dset (n : ℕ) : Finset (SMem N.Mem) :=
  ((Finset.range (n + 1)).image SMem.scan) ∪
  ((LSset N S n).image (fun todo => SMem.outer n todo)) ∪
  (((LSset N S n) ×ˢ (Bset N S n) ×ˢ (Bset N S n) ×ˢ (Finset.range (g n + 1)) ×ˢ
      (STKset N S g n)).image
    (fun p => SMem.call n p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) ∪
  (((LSset N S n) ×ˢ ({false, true} : Finset Bool) ×ˢ (STKset N S g n)).image
    (fun p => SMem.ret n p.1 p.2.1 p.2.2)) ∪
  {SMem.acc}

variable {N S g}

theorem mem_LSset {n : ℕ} {l : List N.Mem} (h : l <:+ cands N S n) : l ∈ LSset N S n := by
  rw [LSset, List.mem_toFinset]
  exact (List.mem_tails _ _).mpr h

theorem mem_FFset {n : ℕ} {fr : Frame N.Mem} (h : FrameOK N S n fr) (hk : fr.k ≤ g n) :
    fr ∈ FFset N S g n := by
  refine Finset.mem_image.mpr ⟨(fr.a, fr.b, fr.k, fr.cur, fr.rest, fr.second), ?_, rfl⟩
  refine Finset.mem_product.mpr ⟨h.1, Finset.mem_product.mpr ⟨h.2.1, ?_⟩⟩
  refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr (show fr.k < g n + 1 by omega), ?_⟩
  refine Finset.mem_product.mpr ⟨h.2.2.1, ?_⟩
  refine Finset.mem_product.mpr ⟨mem_LSset h.2.2.2, ?_⟩
  cases fr.second <;> simp

theorem mem_STKset {n k : ℕ} {st : List (Frame N.Mem)} (h : StackAt N S g n k st) :
    st ∈ STKset N S g n := by
  refine mem_listsLE _ st ?_ ?_
  · have := stackAt_length st k h
    omega
  · intro fr hfr
    obtain ⟨hok, hk⟩ := stackAt_frames st k h fr hfr
    exact mem_FFset hok hk

theorem mem_Dset {n : ℕ} {m : SMem N.Mem} (h : SInv N S g n m) : m ∈ Dset N S g n := by
  cases m with
  | scan i =>
    have hi : i ≤ n := h
    refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ ?_)))
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  | outer m todo =>
    obtain ⟨rfl, hsuf⟩ := h
    refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ ?_)))
    exact Finset.mem_image.mpr ⟨todo, mem_LSset hsuf, rfl⟩
  | call m todo a b k st =>
    obtain ⟨rfl, hsuf, ha, hb, hst⟩ := h
    refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
    refine Finset.mem_image.mpr ⟨(todo, a, b, k, st), ?_, rfl⟩
    have hk : k ≤ g m := by have := stackAt_length st k hst; omega
    refine Finset.mem_product.mpr ⟨mem_LSset hsuf, Finset.mem_product.mpr ⟨ha, ?_⟩⟩
    exact Finset.mem_product.mpr ⟨hb, Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (show k < g m + 1 by omega), mem_STKset hst⟩⟩
  | ret m todo v st =>
    obtain ⟨rfl, hsuf, k, hst⟩ := h
    refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
    refine Finset.mem_image.mpr ⟨(todo, v, st), ?_, rfl⟩
    refine Finset.mem_product.mpr ⟨mem_LSset hsuf, Finset.mem_product.mpr ⟨?_, mem_STKset hst⟩⟩
    cases v <;> simp
  | acc =>
    refine Finset.mem_union_right _ ?_
    simp

/-! ### The cardinality bound -/

theorem mul_le_two_pow {a b p q : ℕ} (ha : a ≤ 2 ^ p) (hb : b ≤ 2 ^ q) : a * b ≤ 2 ^ (p + q) := by
  rw [pow_add]
  exact Nat.mul_le_mul ha hb

theorem card_Bset_le {n : ℕ} (hS : (S n).card ≤ 2 ^ g n) :
    (Bset N S n).card ≤ 2 ^ (g n + 1) := by
  have h1 : (Bset N S n).card ≤ (S n).card + 1 := Finset.card_insert_le _ _
  have h2 : (1 : ℕ) ≤ 2 ^ g n := Nat.one_le_two_pow
  have : 2 ^ (g n + 1) = 2 ^ g n + 2 ^ g n := by ring
  omega

theorem card_LSset_le {n : ℕ} (hS : (S n).card ≤ 2 ^ g n) :
    (LSset N S n).card ≤ 2 ^ (g n + 1) := by
  have h1 : (LSset N S n).card ≤ (cands N S n).tails.length :=
    List.toFinset_card_le _
  have h2 : (cands N S n).tails.length = (S n).card + 1 := by
    rw [List.length_tails, cands, Finset.length_toList]
  have h3 : (1 : ℕ) ≤ 2 ^ g n := Nat.one_le_two_pow
  have : 2 ^ (g n + 1) = 2 ^ g n + 2 ^ g n := by ring
  omega

theorem card_FFset_le {n : ℕ} (hS : (S n).card ≤ 2 ^ g n) :
    (FFset N S g n).card ≤ 2 ^ (5 * g n + 5) := by
  have hB := card_Bset_le (N := N) (S := S) (g := g) (n := n) hS
  have hL := card_LSset_le (N := N) (S := S) (g := g) (n := n) hS
  have hR : (Finset.range (g n + 1)).card ≤ 2 ^ g n := by
    rw [Finset.card_range]
    exact Nat.lt_two_pow_self
  have hBool : ({false, true} : Finset Bool).card ≤ 2 ^ 1 := by decide
  have hprod : ((Bset N S n) ×ˢ (Bset N S n) ×ˢ (Finset.range (g n + 1)) ×ˢ (Bset N S n) ×ˢ
      (LSset N S n) ×ˢ ({false, true} : Finset Bool)).card ≤ 2 ^ (5 * g n + 5) := by
    have e : (5 * g n + 5)
        = (g n + 1) + ((g n + 1) + (g n + ((g n + 1) + ((g n + 1) + 1)))) := by ring
    rw [e]
    simp only [Finset.card_product]
    exact mul_le_two_pow hB (mul_le_two_pow hB (mul_le_two_pow hR
      (mul_le_two_pow hB (mul_le_two_pow hL hBool))))
  exact le_trans Finset.card_image_le hprod

theorem card_STKset_le {n : ℕ} (hS : (S n).card ≤ 2 ^ g n) :
    (STKset N S g n).card ≤ 2 ^ (5 * g n * g n + 6 * g n) := by
  have hFF := card_FFset_le (N := N) (S := S) (g := g) (n := n) hS
  have h1 : (STKset N S g n).card ≤ ((FFset N S g n).card + 1) ^ g n :=
    card_listsLE _ _
  have h2 : (FFset N S g n).card + 1 ≤ 2 ^ (5 * g n + 6) := by
    have : 2 ^ (5 * g n + 6) = 2 ^ (5 * g n + 5) + 2 ^ (5 * g n + 5) := by ring
    have h3 : (1 : ℕ) ≤ 2 ^ (5 * g n + 5) := Nat.one_le_two_pow
    omega
  have h4 : ((FFset N S g n).card + 1) ^ g n ≤ (2 ^ (5 * g n + 6)) ^ g n :=
    Nat.pow_le_pow_left h2 _
  have h5 : (2 ^ (5 * g n + 6)) ^ g n = 2 ^ (5 * g n * g n + 6 * g n) := by
    rw [← pow_mul]
    congr 1
    ring
  omega

theorem card_Dset_le {n : ℕ} (hS : (S n).card ≤ 2 ^ g n) (hn : n + 1 ≤ 2 ^ g n) :
    (Dset N S g n).card ≤ 2 ^ (5 * g n * g n + 10 * g n + 6) := by
  set K := g n with hK
  set E := 5 * K * K + 10 * K + 3 with hE
  have hB := card_Bset_le (N := N) (S := S) (g := g) (n := n) hS
  have hL := card_LSset_le (N := N) (S := S) (g := g) (n := n) hS
  have hSTK := card_STKset_le (N := N) (S := S) (g := g) (n := n) hS
  have hR : (Finset.range (K + 1)).card ≤ 2 ^ K := by
    rw [Finset.card_range]
    exact Nat.lt_two_pow_self
  have hBool : ({false, true} : Finset Bool).card ≤ 2 ^ 1 := by decide
  -- the five pieces
  have p1 : ((Finset.range (n + 1)).image (SMem.scan : ℕ → SMem N.Mem)).card ≤ 2 ^ E := by
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_range]
    exact le_trans hn (Nat.pow_le_pow_right (by omega) (by omega))
  have p2 : ((LSset N S n).image (fun todo => SMem.outer n todo)).card ≤ 2 ^ E := by
    refine le_trans Finset.card_image_le ?_
    exact le_trans hL (Nat.pow_le_pow_right (by omega) (by omega))
  have p3 : (((LSset N S n) ×ˢ (Bset N S n) ×ˢ (Bset N S n) ×ˢ (Finset.range (K + 1)) ×ˢ
      (STKset N S g n)).image
      (fun p => SMem.call n p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)).card ≤ 2 ^ E := by
    refine le_trans Finset.card_image_le ?_
    have e : E = (K + 1) + ((K + 1) + ((K + 1) + (K + (5 * K * K + 6 * K)))) := by
      rw [hE]; ring
    rw [e]
    simp only [Finset.card_product]
    exact mul_le_two_pow hL (mul_le_two_pow hB (mul_le_two_pow hB
      (mul_le_two_pow hR hSTK)))
  have p4 : (((LSset N S n) ×ˢ ({false, true} : Finset Bool) ×ˢ (STKset N S g n)).image
      (fun p => SMem.ret n p.1 p.2.1 p.2.2)).card ≤ 2 ^ E := by
    refine le_trans Finset.card_image_le ?_
    have hle : (K + 1) + (1 + (5 * K * K + 6 * K)) ≤ E := by rw [hE]; omega
    refine le_trans ?_ (Nat.pow_le_pow_right (by omega) hle)
    simp only [Finset.card_product]
    exact mul_le_two_pow hL (mul_le_two_pow hBool hSTK)
  have p5 : ({SMem.acc} : Finset (SMem N.Mem)).card ≤ 2 ^ E := by
    rw [Finset.card_singleton]
    exact Nat.one_le_two_pow
  have hunion : (Dset N S g n).card ≤
      ((Finset.range (n + 1)).image (SMem.scan : ℕ → SMem N.Mem)).card +
      ((LSset N S n).image (fun todo => SMem.outer n todo)).card +
      (((LSset N S n) ×ˢ (Bset N S n) ×ˢ (Bset N S n) ×ˢ (Finset.range (K + 1)) ×ˢ
        (STKset N S g n)).image
        (fun p => SMem.call n p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)).card +
      (((LSset N S n) ×ˢ ({false, true} : Finset Bool) ×ˢ (STKset N S g n)).image
        (fun p => SMem.ret n p.1 p.2.1 p.2.2)).card +
      ({SMem.acc} : Finset (SMem N.Mem)).card := by
    refine le_trans (Finset.card_union_le _ _) ?_
    gcongr
    refine le_trans (Finset.card_union_le _ _) ?_
    gcongr
    refine le_trans (Finset.card_union_le _ _) ?_
    gcongr
    exact Finset.card_union_le _ _
  have hfin : 2 ^ (5 * K * K + 10 * K + 6) = 8 * 2 ^ E := by
    rw [hE, pow_add]
    ring
  omega

end

end CS

/-
# Walks in a relation, and the elementary distance bound

If every vertex reachable from `a` lies in a finite set `S`, then any vertex
reachable from `a` is reachable by a walk of length `< S.card`.
-/
import Mathlib

namespace CS

variable {α : Type}

/-- `Walk r t a b` : there is a walk of length exactly `t` from `a` to `b`. -/
def Walk (r : α → α → Prop) : ℕ → α → α → Prop
  | 0, a, b => a = b
  | (t + 1), a, b => ∃ c, Walk r t a c ∧ r c b

theorem Walk.zero {r : α → α → Prop} (a : α) : Walk r 0 a a := rfl

theorem Walk.trans {r : α → α → Prop} :
    ∀ {t₁ t₂ : ℕ} {a b c : α}, Walk r t₁ a b → Walk r t₂ b c → Walk r (t₁ + t₂) a c := by
  intro t₁ t₂
  induction t₂ with
  | zero =>
      intro a b c h₁ h₂
      cases h₂
      simpa using h₁
  | succ t ih =>
      intro a b c h₁ h₂
      obtain ⟨d, hd, hdc⟩ := h₂
      exact ⟨d, ih h₁ hd, hdc⟩

theorem Walk.exists_path {r : α → α → Prop} :
    ∀ {t : ℕ} {a b : α}, Walk r t a b →
      ∃ p : ℕ → α, p 0 = a ∧ p t = b ∧ ∀ i < t, r (p i) (p (i + 1)) := by
  intro t
  induction t with
  | zero =>
      intro a b h
      cases h
      exact ⟨fun _ => a, rfl, rfl, by omega⟩
  | succ t ih =>
      intro a b h
      obtain ⟨c, hc, hcb⟩ := h
      obtain ⟨p, hp0, hpt, hstep⟩ := ih hc
      refine ⟨fun i => if i ≤ t then p i else b, ?_, ?_, ?_⟩
      · simp [hp0]
      · simp
      · intro i hi
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h' | h'
        · have h1 : i ≤ t := le_of_lt h'
          have h2 : i + 1 ≤ t := h'
          simp only [h1, h2, if_pos]
          exact hstep i h'
        · subst h'
          have h2 : ¬ (i + 1 ≤ i) := by omega
          simp only [le_refl, if_pos, h2, if_neg, not_false_iff]
          simpa [hpt] using hcb

/-- Sub-walks of a path. -/
theorem walk_of_path {r : α → α → Prop} {p : ℕ → α} {t : ℕ}
    (hp : ∀ i < t, r (p i) (p (i + 1))) :
    ∀ j ≤ t, ∀ i ≤ j, Walk r (j - i) (p i) (p j) := by
  intro j
  induction j with
  | zero => intro _ i hi; interval_cases i; exact Walk.zero _
  | succ j ih =>
      intro hj i hi
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · have hij : i ≤ j := by omega
        have h1 : Walk r (j - i) (p i) (p j) := ih (by omega) i hij
        have h2 : r (p j) (p (j + 1)) := hp j (by omega)
        have : Walk r ((j - i) + 1) (p i) (p (j + 1)) := ⟨p j, h1, h2⟩
        have he : j + 1 - i = (j - i) + 1 := by omega
        rwa [he]
      · have hij : i = j + 1 := by omega
        subst hij
        simp only [Nat.sub_self]
        exact Walk.zero _

/-- Any walk splits at any intermediate time. -/
theorem Walk.split {r : α → α → Prop} {t : ℕ} {a b : α} (h : Walk r t a b) (i : ℕ) (hi : i ≤ t) :
    ∃ c, Walk r i a c ∧ Walk r (t - i) c b := by
  obtain ⟨p, hp0, hpt, hstep⟩ := h.exists_path
  refine ⟨p i, ?_, ?_⟩
  · have := walk_of_path hstep i hi 0 (Nat.zero_le _)
    simpa [hp0] using this
  · have := walk_of_path hstep t le_rfl i hi
    rwa [hpt] at this

/-- If all vertices reachable from `a` lie in a finite set `S`, then any vertex
reachable from `a` is reachable by a walk of length `< S.card`. -/
theorem exists_short_walk {r : α → α → Prop} (S : Finset α) (a b : α)
    (hS : ∀ (c : α) (t : ℕ), Walk r t a c → c ∈ S) (h : ∃ t, Walk r t a b) :
    ∃ t, t < S.card ∧ Walk r t a b := by
  classical
  set T := Nat.find h with hTdef
  have hT : Walk r T a b := Nat.find_spec h
  obtain ⟨p, hp0, hpT, hstep⟩ := hT.exists_path
  have hpre : ∀ i ≤ T, Walk r i a (p i) := by
    intro i hi
    have := walk_of_path hstep i hi 0 (Nat.zero_le _)
    simpa [hp0] using this
  have hsuf : ∀ i ≤ T, Walk r (T - i) (p i) b := by
    intro i hi
    have := walk_of_path hstep T le_rfl i hi
    rwa [hpT] at this
  have hmaps : ∀ i ∈ Finset.range (T + 1), p i ∈ S := by
    intro i hi
    simp only [Finset.mem_range] at hi
    exact hS _ i (hpre i (by omega))
  have hinj : Set.InjOn p (Finset.range (T + 1)) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_ge i j with hlt | hge
    · have h1 : Walk r i a (p i) := hpre i (by omega)
      have h2 : Walk r (T - j) (p j) b := hsuf j (by omega)
      rw [← hij] at h2
      have : Walk r (i + (T - j)) a b := h1.trans h2
      have hlt' : i + (T - j) < T := by omega
      exact absurd this (Nat.find_min h hlt')
    · have hlt : j < i := by omega
      have h1 : Walk r j a (p j) := hpre j (by omega)
      have h2 : Walk r (T - i) (p i) b := hsuf i (by omega)
      rw [hij] at h2
      have : Walk r (j + (T - i)) a b := h1.trans h2
      have hlt' : j + (T - i) < T := by omega
      exact absurd this (Nat.find_min h hlt')
  have hcard : T + 1 ≤ S.card := by
    have := Finset.card_le_card_of_injOn p (by simpa [Set.MapsTo] using hmaps) hinj
    simpa using this
  exact ⟨T, by omega, Nat.find_spec h⟩

end CS

/-
# A sanity check: the classes are not degenerate

We exhibit a language that genuinely depends on its input and show it lies in
`PSPACE` (hence, by `CS.PSPACE_eq_NPSPACE`, in `NPSPACE`).  This checks that the
machine model of `RequestProject/Savitch/Model.lean` can actually read its input
and that the space classes are inhabited by non-trivial languages.
-/
import Mathlib
import RequestProject.Savitch.Model
import RequestProject.Savitch

namespace CS

/-- The language of bit strings containing a `true`. -/
def containsTrue : Set (List Bool) := {x | true ∈ x}

/-- The transition of the scanning machine as a function. -/
def scanStep (x : List Bool) : Option ℕ → Option ℕ
  | none => none
  | some i => match x[i]? with
      | some true => none
      | some false => some (i + 1)
      | none => some i

/-- A deterministic machine scanning its input for a `true` bit; the memory is
the current head position, and `none` is the accepting memory value. -/
@[reducible] def scanMachine : Machine where
  Mem := Option ℕ
  start := some 0
  head := fun m => match m with
    | some i => i
    | none => 0
  next := fun m o => match m with
    | none => {none}
    | some i => match o with
        | some true => {none}
        | some false => {some (i + 1)}
        | none => {some i}
  acc := fun m => m = none

theorem scanMachine_det : Deterministic scanMachine := by
  rintro (_ | i) (_ | b)
  · exact ⟨none, rfl⟩
  · exact ⟨none, rfl⟩
  · exact ⟨some i, rfl⟩
  · cases b
    · exact ⟨some (i + 1), rfl⟩
    · exact ⟨none, rfl⟩

theorem scanMachine_next (x : List Bool) (m : Option ℕ) :
    scanMachine.next m x[scanMachine.head m]? = {scanStep x m} := by
  cases m with
  | none => rfl
  | some i =>
    cases h : x[i]? with
    | none => simp [scanMachine, scanStep, h]
    | some b => cases b <;> simp [scanMachine, scanStep, h]

theorem scanReach_iff (x : List Bool) (m : Option ℕ) :
    Reach scanMachine x m ↔ ∃ t, (scanStep x)^[t] (some 0) = m :=
  reach_det_iff (M := scanMachine) (scanStep x) (scanMachine_next x) m

/-- The head position never runs past the end of the input. -/
theorem scanIter_bound (x : List Bool) (t : ℕ) :
    (scanStep x)^[t] (some 0) = none ∨
      ∃ i ≤ x.length, (scanStep x)^[t] (some 0) = some i := by
  induction t with
  | zero => exact Or.inr ⟨0, Nat.zero_le _, rfl⟩
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | ⟨i, hi, h⟩
    · rw [h]; exact Or.inl rfl
    · rw [h]
      cases hx : x[i]? with
      | none => exact Or.inr ⟨i, hi, by simp [scanStep, hx]⟩
      | some b =>
        cases b with
        | true => exact Or.inl (by simp [scanStep, hx])
        | false =>
          have hlt : i < x.length := by
            by_contra hc
            push_neg at hc
            rw [List.getElem?_eq_none hc] at hx
            simp at hx
          exact Or.inr ⟨i + 1, by omega, by simp [scanStep, hx]⟩

theorem scanMachine_inSpace : InSpace scanMachine (fun n => 1 * (n + 1) ^ 1 + 1) := by
  refine ⟨fun n => insert none ((Finset.range (n + 1)).image some), ?_, ?_⟩
  · intro x m hm
    obtain ⟨t, ht⟩ := (scanReach_iff x m).mp hm
    rcases scanIter_bound x t with h | ⟨i, hi, h⟩
    · rw [← ht, h]; exact Finset.mem_insert_self _ _
    · rw [← ht, h]
      exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (show i < x.length + 1 by omega), rfl⟩)
  · intro n
    have h1 : (insert none ((Finset.range (n + 1)).image (some : ℕ → Option ℕ))).card
        ≤ ((Finset.range (n + 1)).image (some : ℕ → Option ℕ)).card + 1 :=
      Finset.card_insert_le _ _
    have h2 : ((Finset.range (n + 1)).image (some : ℕ → Option ℕ)).card ≤ n + 1 := by
      refine le_trans Finset.card_image_le ?_
      simp
    have h3 : n + 2 < 2 ^ (n + 2) := Nat.lt_two_pow_self
    show (insert none ((Finset.range (n + 1)).image (some : ℕ → Option ℕ))).card
      ≤ 2 ^ (1 * (n + 1) ^ 1 + 1)
    have h4 : 1 * (n + 1) ^ 1 + 1 = n + 2 := by ring
    rw [h4]
    omega

theorem scan_accepts_imp (x : List Bool) :
    ∀ t, (scanStep x)^[t] (some 0) = none → true ∈ x := by
  intro t
  induction t with
  | zero => intro h; exact absurd h (by simp)
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    cases hm : (scanStep x)^[t] (some 0) with
    | none => intro _; exact ih hm
    | some i =>
      intro h
      cases hx : x[i]? with
      | none => rw [show scanStep x (some i) = some i by simp [scanStep, hx]] at h; simp at h
      | some b =>
        cases b with
        | true => exact List.mem_of_getElem? hx
        | false =>
          rw [show scanStep x (some i) = some (i + 1) by simp [scanStep, hx]] at h
          simp at h

theorem scan_reaches_none (x : List Bool) :
    ∀ (d i : ℕ), x[i + d]? = some true → ∃ t, (scanStep x)^[t] (some i) = none := by
  intro d
  induction d with
  | zero =>
    intro i hx
    exact ⟨1, by simp [scanStep, (by simpa using hx : x[i]? = some true)]⟩
  | succ d ih =>
    intro i hx
    cases hxi : x[i]? with
    | none =>
      have hle : x.length ≤ i := by
        by_contra hc
        push_neg at hc
        rw [List.getElem?_eq_getElem hc] at hxi
        simp at hxi
      rw [List.getElem?_eq_none (by omega)] at hx
      simp at hx
    | some b =>
      cases b with
      | true => exact ⟨1, by simp [scanStep, hxi]⟩
      | false =>
        have hx' : x[(i + 1) + d]? = some true := by
          have : (i + 1) + d = i + (d + 1) := by omega
          rw [this]; exact hx
        obtain ⟨t, ht⟩ := ih (i + 1) hx'
        refine ⟨t + 1, ?_⟩
        rw [Function.iterate_succ_apply]
        have : scanStep x (some i) = some (i + 1) := by simp [scanStep, hxi]
        rw [this, ht]

theorem scanMachine_accepts (x : List Bool) : Accepts scanMachine x ↔ true ∈ x := by
  constructor
  · rintro ⟨m, hm, hacc⟩
    have hm' : m = none := hacc
    subst hm'
    obtain ⟨t, ht⟩ := (scanReach_iff x none).mp hm
    exact scan_accepts_imp x t ht
  · intro h
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
    obtain ⟨t, ht⟩ := scan_reaches_none x j 0 (by simpa using hj)
    exact ⟨none, (scanReach_iff x none).mpr ⟨t, ht⟩, rfl⟩

/-- The language of strings containing a `true` bit lies in `PSPACE`; in
particular `PSPACE` contains languages that genuinely depend on the input. -/
theorem containsTrue_mem_PSPACE : containsTrue ∈ PSPACE :=
  ⟨1, scanMachine, 1, Nat.one_pos, scanMachine_det, scanMachine_inSpace,
    fun x => (scanMachine_accepts x).symm⟩

/-- Consequently it lies in `NPSPACE` as well. -/
theorem containsTrue_mem_NPSPACE : containsTrue ∈ NPSPACE := by
  rw [← PSPACE_eq_NPSPACE]
  exact containsTrue_mem_PSPACE

end CS

