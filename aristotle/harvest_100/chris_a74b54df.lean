/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.Savitch.Model
import RequestProject.Savitch.Reach
import RequestProject.Savitch.Interp
import RequestProject.Savitch.BigStep
import RequestProject.Savitch.Invariant
import RequestProject.Savitch.Encode

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Statement

`NSPACE(f) ⊆ DSPACE(f²)`, and consequently `PSPACE = NPSPACE` (Savitch's theorem).

The model of computation is the standard configuration-graph model, set up in
`RequestProject.Savitch.Model`: configurations are natural numbers (binary strings), a machine
runs in space `f` on input `x` if all configurations reachable on `x` are `< 2 ^ f |x|`, and
one step may depend on the current configuration together with the single input symbol scanned
by the input head, whose position is determined by the configuration.  The initial
configuration may depend on the input length (the usual assumption that the space bound is
constructible).  No computability assumption is imposed on the transition functions.

The deterministic simulator is built explicitly: it performs the depth-first evaluation of
Savitch's divide-and-conquer recursion, its states are recursion stacks of depth at most `s`,
each frame holding boundedly many numbers `< 2 ^ s`, and the whole state is encoded as a
natural number `< 2 ^ (42 * (s + 1) ^ 2)`.  Hence a nondeterministic machine running in space
`f` is simulated deterministically in space `42 * (f + 1) ^ 2`.
-/

namespace CS

open Classical

variable {Γ : Type}

/-! ### Deterministic machines are nondeterministic machines -/

/-- A deterministic machine, viewed as a nondeterministic one. -/
def DMachine.toNMachine (M : DMachine Γ) : NMachine Γ where
  start := M.start
  head := M.head
  next c σ := if M.result c = none then {M.next c σ} else ∅
  accept c := M.result c = some true

theorem DMachine.run_stationary (M : DMachine Γ) (x : List Γ) {t : ℕ} {b : Bool}
    (h : M.result (M.run x t) = some b) : ∀ t', t ≤ t' → M.run x t' = M.run x t := by
  intro t' ht'
  induction t', ht' using Nat.le_induction with
  | base => rfl
  | succ t' ht' ih =>
      rw [DMachine.run, ih, if_neg (by rw [h]; simp)]

theorem DMachine.reachable_toNMachine (M : DMachine Γ) (x : List Γ) :
    M.toNMachine.Reachable x = M.Reachable x := by
  apply Set.eq_of_subset_of_subset
  · intro c hc
    simp only [NMachine.Reachable, Set.mem_setOf_eq] at hc
    induction hc with
    | refl => exact ⟨0, rfl⟩
    | @tail d e _ hde ih =>
        obtain ⟨t, ht⟩ := ih
        simp only [NMachine.stepRel, DMachine.toNMachine] at hde
        by_cases hres : M.result d = none
        · rw [if_pos hres] at hde
          refine ⟨t + 1, ?_⟩
          rw [DMachine.run, ht, if_pos hres]
          exact (Set.mem_singleton_iff.mp hde).symm
        · rw [if_neg hres] at hde
          simp at hde
  · rintro c ⟨t, rfl⟩
    simp only [NMachine.Reachable, Set.mem_setOf_eq]
    induction t with
    | zero => exact Relation.ReflTransGen.refl
    | succ t ih =>
        by_cases hres : M.result (M.run x t) = none
        · refine ih.tail ?_
          simp only [NMachine.stepRel, DMachine.toNMachine]
          rw [if_pos hres, DMachine.run, if_pos hres]
          rfl
        · rw [DMachine.run, if_neg hres]
          exact ih

theorem DSPACE_subset_NSPACE (g : ℕ → ℕ) : DSPACE Γ g ⊆ NSPACE Γ g := by
  rintro L ⟨M, hsp, hdec⟩
  refine ⟨M.toNMachine, ?_, ?_⟩
  · intro x c hc
    rw [DMachine.reachable_toNMachine] at hc
    exact hsp x c hc
  · intro x
    constructor
    · rintro ⟨c, hc, hacc⟩
      rw [DMachine.reachable_toNMachine] at hc
      obtain ⟨t, rfl⟩ := hc
      have hacc' : M.result (M.run x t) = some true := hacc
      by_contra hx
      obtain ⟨t', ht'⟩ := (hdec x).2 hx
      rcases Nat.le_total t t' with hle | hle
      · rw [M.run_stationary x hacc' t' hle, hacc'] at ht'
        simp at ht'
      · rw [M.run_stationary x ht' t hle, ht'] at hacc'
        simp at hacc'
    · intro hx
      obtain ⟨t, ht⟩ := (hdec x).1 hx
      refine ⟨M.run x t, ?_, ht⟩
      rw [DMachine.reachable_toNMachine]
      exact ⟨t, rfl⟩

/-! ### The deterministic simulator -/

/-- Steps other than the base case of the recursion do not look at the input. -/
theorem step_symb_irrelevant (N : NMachine Γ) (σ σ' : Option Γ) (st : St)
    (h : ∀ a b, st.ctrl ≠ .eval a b 0) : step N σ st = step N σ' st := by
  obtain ⟨s, a₀, tg, ctrl, stack⟩ := st
  cases ctrl with
  | init => rw [step_init, step_init]
  | eval a b k =>
      cases k with
      | zero => exact absurd rfl (h a b)
      | succ k => rw [step_eval_succ, step_eval_succ]
  | ret v =>
      cases stack with
      | nil => rw [step_ret_nil, step_ret_nil]
      | cons fr rest => rw [step_ret_cons, step_ret_cons]
  | halt v => rw [step_halt, step_halt]

/-- A halting state is stationary. -/
theorem stepx_halt_of (N : NMachine Γ) (x : List Γ) (st : St) {v : Bool}
    (h : st.ctrl = .halt v) : stepx N x st = st := by
  obtain ⟨s, a₀, tg, ctrl, stack⟩ := st
  simp only at h
  subst h
  rw [stepx_halt]

/-- The deterministic machine simulating the nondeterministic machine `N` running in space
`f`, by depth-first evaluation of Savitch's recursion. -/
noncomputable def savitchMachine (N : NMachine Γ) (f : ℕ → ℕ) : DMachine Γ where
  start n := encSt ⟨f n, N.start n, 0, .init, []⟩
  head c :=
    match (decSt c).ctrl with
    | .eval a _ 0 => N.head a
    | _ => 0
  next c σ := encSt (step N σ (decSt c))
  result c :=
    match (decSt c).ctrl with
    | .halt v => some v
    | _ => none

theorem savitchMachine_result_of_good (N : NMachine Γ) (f : ℕ → ℕ) {st : St} (h : Good st) :
    (savitchMachine N f).result (encSt st) =
      match st.ctrl with
      | .halt v => some v
      | _ => none := by
  simp only [savitchMachine, decSt_encSt h]

theorem savitchMachine_step_of_good (N : NMachine Γ) (f : ℕ → ℕ) (x : List Γ) {st : St}
    (h : Good st) :
    (savitchMachine N f).next (encSt st) x[(savitchMachine N f).head (encSt st)]? =
      encSt (stepx N x st) := by
  obtain ⟨s, a₀, tg, ctrl, stack⟩ := st
  simp only [savitchMachine, decSt_encSt h]
  cases ctrl with
  | eval a b k =>
      cases k with
      | zero => rfl
      | succ k =>
          exact congrArg encSt (step_symb_irrelevant N _ _ _ (by intro a' b'; simp))
  | init => exact congrArg encSt (step_symb_irrelevant N _ _ _ (by intro a' b'; simp))
  | ret v => exact congrArg encSt (step_symb_irrelevant N _ _ _ (by intro a' b'; simp))
  | halt v => exact congrArg encSt (step_symb_irrelevant N _ _ _ (by intro a' b'; simp))

/-- The run of the simulator tracks the run of the abstract stack machine. -/
theorem savitchMachine_run (N : NMachine Γ) (f : ℕ → ℕ) (x : List Γ)
    (h : Good (⟨f x.length, N.start x.length, 0, .init, []⟩ : St)) (t : ℕ) :
    (savitchMachine N f).run x t =
      encSt (iter N x t ⟨f x.length, N.start x.length, 0, .init, []⟩) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      set st₀ : St := ⟨f x.length, N.start x.length, 0, .init, []⟩ with hst₀
      have hgood : Good (iter N x t st₀) := good_iter N x t st₀ h
      have hiter : iter N x (t + 1) st₀ = stepx N x (iter N x t st₀) := iter_succ_of N x rfl
      rw [DMachine.run, ih, hiter]
      by_cases hhalt : ∃ v, (iter N x t st₀).ctrl = .halt v
      · obtain ⟨v, hv⟩ := hhalt
        have hres : (savitchMachine N f).result (encSt (iter N x t st₀)) = some v := by
          rw [savitchMachine_result_of_good N f hgood, hv]
        rw [if_neg (by rw [hres]; simp)]
        exact congrArg encSt (stepx_halt_of N x _ hv).symm
      · have hres : (savitchMachine N f).result (encSt (iter N x t st₀)) = none := by
          rw [savitchMachine_result_of_good N f hgood]
          cases hc : (iter N x t st₀).ctrl with
          | init => rfl
          | eval a b k => rfl
          | ret v => rfl
          | halt v => exact absurd ⟨v, hc⟩ hhalt
        rw [if_pos hres]
        exact savitchMachine_step_of_good N f x hgood

/-! ### Savitch's theorem -/

/-- **Savitch's theorem**: a language accepted by a nondeterministic machine running in space
`f` is decided by a deterministic machine running in space `42 * (f + 1) ^ 2`. -/
theorem savitch (f : ℕ → ℕ) : NSPACE Γ f ⊆ DSPACE Γ (fun n => 42 * (f n + 1) ^ 2) := by
  rintro L ⟨N, hsp, hacc⟩
  have hstart : ∀ x : List Γ, N.start x.length < 2 ^ f x.length :=
    fun x => hsp x _ (N.start_mem_reachable x)
  have hgood0 : ∀ x : List Γ,
      Good (⟨f x.length, N.start x.length, 0, .init, []⟩ : St) :=
    fun x => good_start (hstart x)
  refine ⟨savitchMachine N f, ?_, ?_⟩
  · -- the space bound
    rintro x c ⟨t, rfl⟩
    rw [savitchMachine_run N f x (hgood0 x) t]
    have hg := good_iter N x t _ (hgood0 x)
    have hlt := encSt_lt hg
    rwa [iter_s N x t _] at hlt
  · -- correctness
    intro x
    obtain ⟨t, v, tg', ht, hv⟩ := bigstep_run N x (f x.length) (N.start x.length)
    have hgt : Good (iter N x t ⟨f x.length, N.start x.length, 0, .init, []⟩) :=
      good_iter N x t _ (hgood0 x)
    have hres : (savitchMachine N f).result ((savitchMachine N f).run x t) = some v := by
      rw [savitchMachine_run N f x (hgood0 x) t, savitchMachine_result_of_good N f hgt, ht]
    have hiff : v = true ↔ x ∈ L := by
      rw [hv, ← hacc x]
      constructor
      · rintro ⟨c, -, hc2, hc3⟩
        exact ⟨c, Reach.sound hc3, hc2⟩
      · rintro ⟨c, hc1, hc2⟩
        exact ⟨c, hsp x c hc1, hc2, Reach.complete (fun c' hc' => hsp x c' hc') hc1⟩
    refine ⟨fun hx => ⟨t, ?_⟩, fun hx => ⟨t, ?_⟩⟩
    · rw [hres, hiff.mpr hx]
    · have : v = false := by
        rcases Bool.eq_false_or_eq_true v with hvt | hvf
        · exact absurd (hiff.mp hvt) hx
        · exact hvf
      rw [hres, this]

/-- Savitch's theorem in `O`-form: nondeterministic space `f` is contained in deterministic
space `O(f²)`. -/
theorem savitch_bigO (f : ℕ → ℕ) (L : Set (List Γ)) (hL : L ∈ NSPACE Γ f) :
    ∃ c : ℕ, L ∈ DSPACE Γ (fun n => c * (f n + 1) ^ 2) :=
  ⟨42, savitch f hL⟩

/-- **Corollary**: polynomial nondeterministic space equals polynomial deterministic space. -/
theorem pspace_eq_npspace : PSPACE Γ = NPSPACE Γ := by
  apply Set.eq_of_subset_of_subset
  · rintro L ⟨c, k, hL⟩
    exact ⟨c, k, DSPACE_subset_NSPACE _ hL⟩
  · rintro L ⟨c, k, hL⟩
    refine ⟨42 * (c + 1) ^ 2, 2 * k, ?_⟩
    refine DSPACE_mono ?_ (savitch (fun n => c * (n + 1) ^ k) hL)
    intro n
    have h1 : c * (n + 1) ^ k + 1 ≤ (c + 1) * (n + 1) ^ k := by
      have : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
      nlinarith
    calc 42 * (c * (n + 1) ^ k + 1) ^ 2
        ≤ 42 * ((c + 1) * (n + 1) ^ k) ^ 2 := by
          exact Nat.mul_le_mul_left 42 (Nat.pow_le_pow_left h1 2)
      _ = 42 * (c + 1) ^ 2 * (n + 1) ^ (2 * k) := by
          rw [mul_pow, ← pow_mul]; ring_nf

/-! ### Non-degeneracy of the model

The following two lemmas record that the space measure is meaningful: with zero space, i.e.
a single configuration, only the two trivial languages can be recognised. -/

/-- A nondeterministic machine with a single configuration recognises only `∅` or everything. -/
theorem NSPACE_zero_trivial {L : Set (List Γ)} (hL : L ∈ NSPACE Γ (fun _ => 0)) :
    L = ∅ ∨ L = Set.univ := by
  obtain ⟨N, hsp, hacc⟩ := hL
  have hz : ∀ x : List Γ, N.Accepts x ↔ N.accept 0 := by
    intro x
    constructor
    · rintro ⟨c, hc, ha⟩
      have hc0 : c < 2 ^ (0 : ℕ) := hsp x c hc
      have : c = 0 := by simpa using hc0
      rwa [this] at ha
    · intro h
      have hs : N.start x.length < 2 ^ (0 : ℕ) := hsp x _ (N.start_mem_reachable x)
      have h0 : N.start x.length = 0 := by simpa using hs
      exact ⟨0, h0 ▸ N.start_mem_reachable x, h⟩
  by_cases h : N.accept 0
  · right
    ext x
    simp only [Set.mem_univ, iff_true, ← hacc x, hz x]
    exact h
  · left
    ext x
    simp only [Set.mem_empty_iff_false, iff_false, ← hacc x, hz x]
    exact h

/-- A deterministic machine with a single configuration decides only `∅` or everything. -/
theorem DSPACE_zero_trivial {L : Set (List Γ)} (hL : L ∈ DSPACE Γ (fun _ => 0)) :
    L = ∅ ∨ L = Set.univ := by
  obtain ⟨M, hsp, hdec⟩ := hL
  have hrun : ∀ (x : List Γ) (t : ℕ), M.run x t = 0 := by
    intro x t
    have : M.run x t < 2 ^ (0 : ℕ) := hsp x _ ⟨t, rfl⟩
    simpa using this
  by_cases h : M.result 0 = some true
  · right
    ext x
    simp only [Set.mem_univ, iff_true]
    by_contra hx
    obtain ⟨t, ht⟩ := (hdec x).2 hx
    rw [hrun x t, h] at ht
    simp at ht
  · left
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    obtain ⟨t, ht⟩ := (hdec x).1 hx
    rw [hrun x t] at ht
    exact h ht

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

import RequestProject.Savitch.Interp

/-!
# The space invariant of the Savitch simulator

The simulator only ever visits states whose recursion stack has depth at most `s` and all of
whose numerical components are at most `2 ^ s`.  This is the content of the predicate
`CS.Good`, which we prove to be preserved by the transition function.
-/

namespace CS

open Classical

variable {Γ : Type}

/-- `GoodStack s k l`: `l` is a legitimate recursion stack whose topmost frame awaits a value
at recursion level `k`. -/
def GoodStack (s : ℕ) : ℕ → List Frame → Prop
  | k, [] => k = s
  | k, fr :: rest =>
      fr.k = k ∧ fr.a < 2 ^ s ∧ fr.b < 2 ^ s ∧ fr.m < 2 ^ s ∧ GoodStack s (k + 1) rest

theorem GoodStack_nil {s k : ℕ} : GoodStack s k [] ↔ k = s := Iff.rfl

theorem GoodStack_cons {s k : ℕ} {fr : Frame} {rest : List Frame} :
    GoodStack s k (fr :: rest) ↔
      (fr.k = k ∧ fr.a < 2 ^ s ∧ fr.b < 2 ^ s ∧ fr.m < 2 ^ s ∧ GoodStack s (k + 1) rest) :=
  Iff.rfl

/-- The stack depth plus the current recursion level is exactly the space bound. -/
theorem GoodStack_length {s : ℕ} : ∀ (k : ℕ) (l : List Frame), GoodStack s k l → l.length + k = s
  | k, [], h => by simpa [GoodStack] using h
  | k, fr :: rest, h => by
      have := GoodStack_length (k + 1) rest h.2.2.2.2
      simp only [List.length_cons]
      omega

/-- Every frame of a legitimate stack has small components. -/
theorem GoodStack_mem {s : ℕ} : ∀ (k : ℕ) (l : List Frame), GoodStack s k l →
    ∀ fr ∈ l, fr.k < s ∧ fr.a < 2 ^ s ∧ fr.b < 2 ^ s ∧ fr.m < 2 ^ s
  | _, [], _, fr, hfr => by simp at hfr
  | k, fr :: rest, h, fr', hfr' => by
      rcases List.mem_cons.mp hfr' with rfl | hmem
      · have hlen := GoodStack_length (k + 1) rest h.2.2.2.2
        have hk : fr'.k = k := h.1
        exact ⟨by omega, h.2.1, h.2.2.1, h.2.2.2.1⟩
      · exact GoodStack_mem (k + 1) rest h.2.2.2.2 fr' hmem

/-- The invariant satisfied by all states visited by the simulator. -/
def Good (st : St) : Prop :=
  st.a₀ < 2 ^ st.s ∧
    (match st.ctrl with
      | .init => st.stack = [] ∧ st.target ≤ 2 ^ st.s
      | .eval a b k =>
          a < 2 ^ st.s ∧ b < 2 ^ st.s ∧ st.target < 2 ^ st.s ∧ GoodStack st.s k st.stack
      | .ret _ => st.target < 2 ^ st.s ∧ ∃ k, GoodStack st.s k st.stack
      | .halt _ => st.stack = [] ∧ st.target ≤ 2 ^ st.s)

theorem good_start {s a₀ : ℕ} (h : a₀ < 2 ^ s) : Good ⟨s, a₀, 0, .init, []⟩ :=
  ⟨h, rfl, Nat.zero_le _⟩

theorem step_s (N : NMachine Γ) (σ : Option Γ) (st : St) : (step N σ st).s = st.s := by
  obtain ⟨s, a₀, tg, ctrl, stack⟩ := st
  cases ctrl with
  | init => rw [step_init]; split <;> [split; skip] <;> rfl
  | eval a b k =>
      cases k with
      | zero => rw [step_eval_zero]
      | succ k => rw [step_eval_succ]
  | ret v =>
      cases stack with
      | nil => rw [step_ret_nil]; split <;> rfl
      | cons fr rest => rw [step_ret_cons]; split <;> [split; split] <;> rfl
  | halt v => rw [step_halt]

theorem step_a₀ (N : NMachine Γ) (σ : Option Γ) (st : St) : (step N σ st).a₀ = st.a₀ := by
  obtain ⟨s, a₀, tg, ctrl, stack⟩ := st
  cases ctrl with
  | init => rw [step_init]; split <;> [split; skip] <;> rfl
  | eval a b k =>
      cases k with
      | zero => rw [step_eval_zero]
      | succ k => rw [step_eval_succ]
  | ret v =>
      cases stack with
      | nil => rw [step_ret_nil]; split <;> rfl
      | cons fr rest => rw [step_ret_cons]; split <;> [split; split] <;> rfl
  | halt v => rw [step_halt]

/-- The invariant is preserved by the transition function. -/
theorem good_step (N : NMachine Γ) (σ : Option Γ) (st : St) (h : Good st) :
    Good (step N σ st) := by
  obtain ⟨s, a₀, tg, ctrl, stack⟩ := st
  obtain ⟨ha₀, hrest⟩ := h
  simp only at ha₀ hrest
  cases ctrl with
  | init =>
      obtain ⟨hstack, htg⟩ := hrest
      subst hstack
      rw [step_init]
      by_cases h1 : tg < 2 ^ s
      · rw [if_pos h1]
        by_cases h2 : N.accept tg
        · rw [if_pos h2]
          exact ⟨ha₀, ha₀, h1, h1, rfl⟩
        · rw [if_neg h2]
          exact ⟨ha₀, rfl, show tg + 1 ≤ 2 ^ s by omega⟩
      · rw [if_neg h1]
        exact ⟨ha₀, rfl, htg⟩
  | eval a b k =>
      obtain ⟨hA, hB, htg, hstk⟩ := hrest
      cases k with
      | zero =>
          rw [step_eval_zero]
          exact ⟨ha₀, htg, 0, hstk⟩
      | succ k =>
          rw [step_eval_succ]
          refine ⟨ha₀, hA, Nat.two_pow_pos s, htg, ?_⟩
          exact ⟨rfl, hA, hB, Nat.two_pow_pos s, hstk⟩
  | ret v =>
      obtain ⟨htg, k, hstk⟩ := hrest
      cases stack with
      | nil =>
          rw [step_ret_nil]
          by_cases hv : v = true
          · subst hv
            simp only [if_pos]
            exact ⟨ha₀, rfl, le_of_lt htg⟩
          · have : v = false := by simpa using hv
            subst this
            simp only [Bool.false_eq_true, if_false]
            exact ⟨ha₀, rfl, show tg + 1 ≤ 2 ^ s by omega⟩
      | cons fr rest =>
          obtain ⟨hk, hA, hB, hM, hrst⟩ := hstk
          rw [step_ret_cons]
          by_cases hv : v = true
          · subst hv
            simp only [if_pos]
            by_cases hph : fr.ph = true
            · rw [if_pos hph]
              exact ⟨ha₀, htg, k + 1, hrst⟩
            · have : fr.ph = false := by simpa using hph
              rw [if_neg (by simp [this])]
              exact ⟨ha₀, hM, hB, htg, ⟨rfl, hA, hB, hM, by rw [hk]; exact hrst⟩⟩
          · have hvf : v = false := by simpa using hv
            subst hvf
            simp only [Bool.false_eq_true, if_false]
            by_cases hm : fr.m + 1 < 2 ^ s
            · rw [if_pos hm]
              exact ⟨ha₀, hA, hm, htg, ⟨rfl, hA, hB, hm, by rw [hk]; exact hrst⟩⟩
            · rw [if_neg hm]
              exact ⟨ha₀, htg, k + 1, hrst⟩
  | halt v =>
      rw [step_halt]
      exact ⟨ha₀, hrest⟩

theorem good_stepx (N : NMachine Γ) (x : List Γ) (st : St) (h : Good st) :
    Good (stepx N x st) := good_step N _ st h

theorem good_iter (N : NMachine Γ) (x : List Γ) :
    ∀ (t : ℕ) (st : St), Good st → Good (iter N x t st) := by
  intro t
  induction t with
  | zero => intro st h; exact h
  | succ t ih => intro st h; exact ih _ (good_stepx N x st h)

theorem iter_s (N : NMachine Γ) (x : List Γ) : ∀ (t : ℕ) (st : St), (iter N x t st).s = st.s := by
  intro t
  induction t with
  | zero => intro st; rfl
  | succ t ih => intro st; rw [iter]; rw [ih]; exact step_s N _ st

theorem iter_a₀ (N : NMachine Γ) (x : List Γ) :
    ∀ (t : ℕ) (st : St), (iter N x t st).a₀ = st.a₀ := by
  intro t
  induction t with
  | zero => intro st; rfl
  | succ t ih => intro st; rw [iter]; rw [ih]; exact step_a₀ N _ st

end CS

import RequestProject.Savitch.Model
import RequestProject.Savitch.Reach

/-!
# The Savitch simulator, as an abstract stack machine

Given a nondeterministic machine `N` we describe a *deterministic* procedure which decides
acceptance of `N` by depth-first evaluation of the Savitch recursion, using an explicit
stack of recursion frames.  This file defines the states of that procedure and its one-step
transition function, and proves the "big-step" correctness lemmas: from a state which asks
for the value of `Reach s edge k a b`, the procedure reaches, after finitely many steps, the
state which returns the correct boolean, with the rest of the stack untouched.
-/

namespace CS

open Classical

/-- A recursion frame: we are computing `Reach s edge (k+1) a b`, currently trying the
midpoint `m`; `ph = false` means we await the value of `Reach s edge k a m`, and `ph = true`
means the first half succeeded and we await `Reach s edge k m b`. -/
structure Frame where
  /-- source vertex -/
  a : ℕ
  /-- target vertex -/
  b : ℕ
  /-- recursion level of the awaited value -/
  k : ℕ
  /-- current midpoint -/
  m : ℕ
  /-- phase of the frame -/
  ph : Bool
deriving DecidableEq

/-- The control state of the simulator. -/
inductive Ctrl where
  /-- start the test of the current target configuration -/
  | init : Ctrl
  /-- compute `Reach s edge k a b` -/
  | eval : ℕ → ℕ → ℕ → Ctrl
  /-- return the value `v` to the top frame -/
  | ret : Bool → Ctrl
  /-- halt with verdict `v` -/
  | halt : Bool → Ctrl
deriving DecidableEq

/-- A state of the simulator: the space bound `s`, the initial configuration `a₀` of the
simulated machine, the target configuration currently being tested, the control state, and
the recursion stack. -/
structure St where
  /-- space bound of the simulated machine -/
  s : ℕ
  /-- initial configuration of the simulated machine -/
  a₀ : ℕ
  /-- configuration currently tested for acceptance -/
  target : ℕ
  /-- control state -/
  ctrl : Ctrl
  /-- recursion stack -/
  stack : List Frame
deriving DecidableEq

variable {Γ : Type}

/-- One step of the simulator, given the currently scanned input symbol `σ`. -/
noncomputable def step (N : NMachine Γ) (σ : Option Γ) (st : St) : St :=
  match st.ctrl with
  | .init =>
      if st.target < 2 ^ st.s then
        if N.accept st.target then { st with ctrl := .eval st.a₀ st.target st.s }
        else { st with target := st.target + 1 }
      else { st with ctrl := .halt false }
  | .eval a b 0 => { st with ctrl := .ret (decide (a = b ∨ b ∈ N.next a σ)) }
  | .eval a b (k + 1) =>
      { st with ctrl := .eval a 0 k, stack := ⟨a, b, k, 0, false⟩ :: st.stack }
  | .ret v =>
      match st.stack with
      | [] =>
          if v then { st with ctrl := .halt true }
          else { st with target := st.target + 1, ctrl := .init }
      | fr :: rest =>
          if v then
            if fr.ph then { st with ctrl := .ret true, stack := rest }
            else { st with ctrl := .eval fr.m fr.b fr.k, stack := { fr with ph := true } :: rest }
          else
            if fr.m + 1 < 2 ^ st.s then
              { st with ctrl := .eval fr.a (fr.m + 1) fr.k,
                        stack := { fr with m := fr.m + 1, ph := false } :: rest }
            else { st with ctrl := .ret false, stack := rest }
  | .halt _ => st

/-- The input symbol scanned in a given state. -/
def symb (N : NMachine Γ) (x : List Γ) (st : St) : Option Γ :=
  match st.ctrl with
  | .eval a _ 0 => x[N.head a]?
  | _ => none

/-- One step of the simulator on input `x`. -/
noncomputable def stepx (N : NMachine Γ) (x : List Γ) (st : St) : St :=
  step N (symb N x st) st

/-- `t` steps of the simulator on input `x`. -/
noncomputable def iter (N : NMachine Γ) (x : List Γ) : ℕ → St → St
  | 0, st => st
  | t + 1, st => iter N x t (stepx N x st)

theorem iter_add (N : NMachine Γ) (x : List Γ) (t₁ t₂ : ℕ) (st : St) :
    iter N x (t₁ + t₂) st = iter N x t₂ (iter N x t₁ st) := by
  induction t₁ generalizing st with
  | zero => simp [iter]
  | succ t ih => rw [show t + 1 + t₂ = (t + t₂) + 1 from by ring]; simp only [iter]; exact ih _

theorem iter_one (N : NMachine Γ) (x : List Γ) (st : St) :
    iter N x 1 st = stepx N x st := by simp [iter]

theorem iter_succ_of (N : NMachine Γ) (x : List Γ) {t : ℕ} {st st1 : St}
    (h : iter N x t st = st1) : iter N x (t + 1) st = stepx N x st1 := by
  rw [iter_add, h, iter_one]

theorem iter_trans (N : NMachine Γ) (x : List Γ) {t1 t2 : ℕ} {st st1 st2 : St}
    (h1 : iter N x t1 st = st1) (h2 : iter N x t2 st1 = st2) :
    iter N x (t1 + t2) st = st2 := by rw [iter_add, h1, h2]

section StepLemmas

variable (N : NMachine Γ) (σ : Option Γ) (s a₀ tg a b k m : ℕ) (S : List Frame) (v : Bool)
  (fr : Frame)

theorem step_init :
    step N σ ⟨s, a₀, tg, .init, S⟩ =
      if tg < 2 ^ s then
        (if N.accept tg then ⟨s, a₀, tg, .eval a₀ tg s, S⟩ else ⟨s, a₀, tg + 1, .init, S⟩)
      else ⟨s, a₀, tg, .halt false, S⟩ := by
  simp only [step]

theorem step_eval_zero :
    step N σ ⟨s, a₀, tg, .eval a b 0, S⟩ =
      ⟨s, a₀, tg, .ret (decide (a = b ∨ b ∈ N.next a σ)), S⟩ := rfl

theorem step_eval_succ :
    step N σ ⟨s, a₀, tg, .eval a b (k + 1), S⟩ =
      ⟨s, a₀, tg, .eval a 0 k, ⟨a, b, k, 0, false⟩ :: S⟩ := rfl

theorem step_ret_nil :
    step N σ ⟨s, a₀, tg, .ret v, []⟩ =
      (if v then ⟨s, a₀, tg, .halt true, []⟩ else ⟨s, a₀, tg + 1, .init, []⟩) := by
  simp only [step]

theorem step_ret_cons :
    step N σ ⟨s, a₀, tg, .ret v, fr :: S⟩ =
      (if v then
        (if fr.ph then ⟨s, a₀, tg, .ret true, S⟩
         else ⟨s, a₀, tg, .eval fr.m fr.b fr.k, { fr with ph := true } :: S⟩)
      else
        (if fr.m + 1 < 2 ^ s then
          ⟨s, a₀, tg, .eval fr.a (fr.m + 1) fr.k, { fr with m := fr.m + 1, ph := false } :: S⟩
         else ⟨s, a₀, tg, .ret false, S⟩)) := by
  simp only [step]

theorem step_halt : step N σ ⟨s, a₀, tg, .halt v, S⟩ = ⟨s, a₀, tg, .halt v, S⟩ := rfl

theorem symb_eval_zero (x : List Γ) :
    symb N x ⟨s, a₀, tg, .eval a b 0, S⟩ = x[N.head a]? := rfl

theorem stepx_eval_zero (x : List Γ) :
    stepx N x ⟨s, a₀, tg, .eval a b 0, S⟩ =
      ⟨s, a₀, tg, .ret (decide (a = b ∨ N.stepRel x a b)), S⟩ := rfl

theorem stepx_init (x : List Γ) :
    stepx N x ⟨s, a₀, tg, .init, S⟩ =
      if tg < 2 ^ s then
        (if N.accept tg then ⟨s, a₀, tg, .eval a₀ tg s, S⟩ else ⟨s, a₀, tg + 1, .init, S⟩)
      else ⟨s, a₀, tg, .halt false, S⟩ := step_init N none s a₀ tg S

theorem stepx_eval_succ (x : List Γ) :
    stepx N x ⟨s, a₀, tg, .eval a b (k + 1), S⟩ =
      ⟨s, a₀, tg, .eval a 0 k, ⟨a, b, k, 0, false⟩ :: S⟩ := rfl

theorem stepx_ret_nil (x : List Γ) :
    stepx N x ⟨s, a₀, tg, .ret v, []⟩ =
      (if v then ⟨s, a₀, tg, .halt true, []⟩ else ⟨s, a₀, tg + 1, .init, []⟩) :=
  step_ret_nil N none s a₀ tg v

theorem stepx_ret_cons (x : List Γ) :
    stepx N x ⟨s, a₀, tg, .ret v, fr :: S⟩ =
      (if v then
        (if fr.ph then ⟨s, a₀, tg, .ret true, S⟩
         else ⟨s, a₀, tg, .eval fr.m fr.b fr.k, { fr with ph := true } :: S⟩)
      else
        (if fr.m + 1 < 2 ^ s then
          ⟨s, a₀, tg, .eval fr.a (fr.m + 1) fr.k, { fr with m := fr.m + 1, ph := false } :: S⟩
         else ⟨s, a₀, tg, .ret false, S⟩)) := step_ret_cons N none s a₀ tg S v fr

theorem stepx_halt (x : List Γ) :
    stepx N x ⟨s, a₀, tg, .halt v, S⟩ = ⟨s, a₀, tg, .halt v, S⟩ := rfl

end StepLemmas

end CS

import Mathlib

/-!
# A configuration-graph model of space-bounded computation

This file sets up the model of space-bounded computation used to state and prove
Savitch's theorem.

A machine works on inputs `x : List Γ`.  Its *configurations* are natural numbers,
thought of as binary strings: a machine "uses space `s`" on `x` if every configuration
reachable on input `x` is `< 2 ^ s` (i.e. fits in `s` bits).  A configuration determines
the position `head c` of the read-only input head, and the machine's transition may
depend on the configuration together with the single input symbol currently scanned
(`none` if the head is outside the input).  The initial configuration may depend on the
length of the input (this is the usual assumption that the space bound is constructible).

No computability assumption is placed on the transition functions; the model is therefore
the standard configuration-graph abstraction of space-bounded computation.
-/

namespace CS



/-- A nondeterministic space-bounded machine over input alphabet `Γ`. -/
structure NMachine (Γ : Type) where
  /-- Initial configuration, as a function of the input length. -/
  start : ℕ → ℕ
  /-- Position of the input head in a given configuration. -/
  head : ℕ → ℕ
  /-- Successor configurations, given the current configuration and the scanned symbol. -/
  next : ℕ → Option Γ → Set ℕ
  /-- Accepting configurations. -/
  accept : ℕ → Prop

/-- A deterministic space-bounded machine over input alphabet `Γ`. -/
structure DMachine (Γ : Type) where
  /-- Initial configuration, as a function of the input length. -/
  start : ℕ → ℕ
  /-- Position of the input head in a given configuration. -/
  head : ℕ → ℕ
  /-- Successor configuration, given the current configuration and the scanned symbol. -/
  next : ℕ → Option Γ → ℕ
  /-- `some b` on halting configurations with verdict `b`, `none` otherwise. -/
  result : ℕ → Option Bool

namespace NMachine

variable {Γ : Type}

/-- One computation step on input `x`. -/
def stepRel (M : NMachine Γ) (x : List Γ) (c c' : ℕ) : Prop :=
  c' ∈ M.next c x[M.head c]?

/-- The configurations reachable on input `x`. -/
def Reachable (M : NMachine Γ) (x : List Γ) : Set ℕ :=
  {c | Relation.ReflTransGen (M.stepRel x) (M.start x.length) c}

/-- The machine accepts `x` if some accepting configuration is reachable. -/
def Accepts (M : NMachine Γ) (x : List Γ) : Prop :=
  ∃ c ∈ M.Reachable x, M.accept c

/-- `M` runs in space `f`: on every input `x`, all reachable configurations fit in
`f x.length` bits. -/
def SpaceBounded (M : NMachine Γ) (f : ℕ → ℕ) : Prop :=
  ∀ x : List Γ, ∀ c ∈ M.Reachable x, c < 2 ^ f x.length

theorem start_mem_reachable (M : NMachine Γ) (x : List Γ) :
    M.start x.length ∈ M.Reachable x := Relation.ReflTransGen.refl

theorem reachable_step {M : NMachine Γ} {x : List Γ} {c c' : ℕ}
    (hc : c ∈ M.Reachable x) (h : M.stepRel x c c') : c' ∈ M.Reachable x :=
  Relation.ReflTransGen.tail hc h

end NMachine

namespace DMachine

variable {Γ : Type}

/-- The configuration of `M` on input `x` after `t` steps (halting configurations
are stationary). -/
def run (M : DMachine Γ) (x : List Γ) : ℕ → ℕ
  | 0 => M.start x.length
  | t + 1 =>
      if M.result (M.run x t) = none then
        M.next (M.run x t) x[M.head (M.run x t)]?
      else M.run x t

/-- The configurations reachable on input `x`. -/
def Reachable (M : DMachine Γ) (x : List Γ) : Set ℕ := Set.range (M.run x)

/-- `M` halts on `x` with verdict `b`. -/
def Outputs (M : DMachine Γ) (x : List Γ) (b : Bool) : Prop :=
  ∃ t, M.result (M.run x t) = some b

/-- `M` decides the language `L`. -/
def Decides (M : DMachine Γ) (L : Set (List Γ)) : Prop :=
  ∀ x : List Γ, (x ∈ L → M.Outputs x true) ∧ (x ∉ L → M.Outputs x false)

/-- `M` runs in space `g`: on every input `x`, all reachable configurations fit in
`g x.length` bits. -/
def SpaceBounded (M : DMachine Γ) (g : ℕ → ℕ) : Prop :=
  ∀ x : List Γ, ∀ c ∈ M.Reachable x, c < 2 ^ g x.length

end DMachine

variable (Γ : Type)

/-- Languages decided by a deterministic machine running in space `g`. -/
def DSPACE (g : ℕ → ℕ) : Set (Set (List Γ)) :=
  {L | ∃ M : DMachine Γ, M.SpaceBounded g ∧ M.Decides L}

/-- Languages accepted by a nondeterministic machine running in space `f`. -/
def NSPACE (f : ℕ → ℕ) : Set (Set (List Γ)) :=
  {L | ∃ M : NMachine Γ, M.SpaceBounded f ∧ ∀ x, (M.Accepts x ↔ x ∈ L)}

/-- Polynomial deterministic space. -/
def PSPACE : Set (Set (List Γ)) :=
  {L | ∃ c k : ℕ, L ∈ DSPACE Γ (fun n => c * (n + 1) ^ k)}

/-- Polynomial nondeterministic space. -/
def NPSPACE : Set (Set (List Γ)) :=
  {L | ∃ c k : ℕ, L ∈ NSPACE Γ (fun n => c * (n + 1) ^ k)}

variable {Γ}

theorem DSPACE_mono {g g' : ℕ → ℕ} (h : ∀ n, g n ≤ g' n) :
    DSPACE Γ g ⊆ DSPACE Γ g' := by
  rintro L ⟨M, hsp, hdec⟩
  exact ⟨M, fun x c hc => lt_of_lt_of_le (hsp x c hc) (Nat.pow_le_pow_right (by norm_num) (h _)),
    hdec⟩

theorem NSPACE_mono {f f' : ℕ → ℕ} (h : ∀ n, f n ≤ f' n) :
    NSPACE Γ f ⊆ NSPACE Γ f' := by
  rintro L ⟨M, hsp, hacc⟩
  exact ⟨M, fun x c hc => lt_of_lt_of_le (hsp x c hc) (Nat.pow_le_pow_right (by norm_num) (h _)),
    hacc⟩

end CS

import RequestProject.Savitch.Invariant

/-!
# Encoding simulator states as natural numbers

The deterministic machines of our model have natural numbers as configurations, so the states
of the Savitch simulator have to be encoded.  We use a plain positional encoding of the list
of numerical components of a state, in a base large enough to accommodate them, paired with
the space bound `s`.

The two facts we need are that the encoding is injective on states satisfying the invariant
`CS.Good`, and that such states have codes below `2 ^ (42 * (s + 1) ^ 2)`.
-/

namespace CS

open Classical

/-- Positional encoding of a list of numbers `< B` in base `B + 1`. -/
def encList (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => (a + 1) + (B + 1) * encList B l

theorem encList_nil (B : ℕ) : encList B [] = 0 := rfl

theorem encList_cons (B a : ℕ) (l : List ℕ) :
    encList B (a :: l) = (a + 1) + (B + 1) * encList B l := rfl

private theorem digit_unique {M r r' q q' : ℕ} (hr : r < M) (hr' : r' < M)
    (h : r + M * q = r' + M * q') : r = r' ∧ q = q' := by
  have hq : q = q' := by
    rcases Nat.lt_trichotomy q q' with h1 | h1 | h1
    · exfalso
      have : M * q + M ≤ M * q' := by
        calc M * q + M = M * (q + 1) := by ring
        _ ≤ M * q' := Nat.mul_le_mul_left M h1
      omega
    · exact h1
    · exfalso
      have : M * q' + M ≤ M * q := by
        calc M * q' + M = M * (q' + 1) := by ring
        _ ≤ M * q := Nat.mul_le_mul_left M h1
      omega
  subst hq
  omega

theorem encList_injective (B : ℕ) : ∀ (l l' : List ℕ), (∀ a ∈ l, a < B) → (∀ a ∈ l', a < B) →
    encList B l = encList B l' → l = l' := by
  intro l
  induction l with
  | nil =>
      intro l' _ _ h
      cases l' with
      | nil => rfl
      | cons a' l' => rw [encList_nil, encList_cons] at h; omega
  | cons a l ih =>
      intro l' hl hl' h
      cases l' with
      | nil => rw [encList_nil, encList_cons] at h; omega
      | cons a' l' =>
          rw [encList_cons, encList_cons] at h
          have ha : a < B := hl a (by simp)
          have ha' : a' < B := hl' a' (by simp)
          obtain ⟨h1, h2⟩ :=
            digit_unique (M := B + 1) (r := a + 1) (r' := a' + 1) (by omega) (by omega) h
          have : a = a' := by omega
          subst this
          rw [ih l' (fun c hc => hl c (by simp [hc])) (fun c hc => hl' c (by simp [hc])) h2]

theorem encList_lt (B : ℕ) : ∀ (d : ℕ) (l : List ℕ), (∀ a ∈ l, a < B) → l.length ≤ d →
    encList B l < (B + 1) ^ d := by
  intro d
  induction d with
  | zero =>
      intro l _ hlen
      have : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst this
      simp [encList_nil]
  | succ d ih =>
      intro l hb hlen
      cases l with
      | nil => simp only [encList_nil]; positivity
      | cons a l =>
          have h1 : encList B l < (B + 1) ^ d :=
            ih l (fun c hc => hb c (by simp [hc])) (by simp at hlen; omega)
          have ha : a < B := hb a (by simp)
          rw [encList_cons, pow_succ]
          have hstep : (B + 1) * (encList B l + 1) = (B + 1) * encList B l + (B + 1) := by ring
          calc (a + 1) + (B + 1) * encList B l
              < (B + 1) * (encList B l + 1) := by omega
            _ ≤ (B + 1) * (B + 1) ^ d := Nat.mul_le_mul_left _ (by omega)
            _ = (B + 1) ^ d * (B + 1) := by ring

/-- The numerical components of a frame. -/
def frameNums (fr : Frame) : List ℕ := [fr.a, fr.b, fr.k, fr.m, if fr.ph then 1 else 0]

/-- The numerical components of a control state (always four of them). -/
def ctrlNums : Ctrl → List ℕ
  | .init => [0, 0, 0, 0]
  | .eval a b k => [1, a, b, k]
  | .ret v => [2, if v then 1 else 0, 0, 0]
  | .halt v => [3, if v then 1 else 0, 0, 0]

theorem ctrlNums_length (c : Ctrl) : (ctrlNums c).length = 4 := by
  cases c <;> rfl

private theorem bool_ite_inj {v v' : Bool} (h : (if v then 1 else 0) = (if v' then 1 else 0)) :
    v = v' := by
  cases v <;> cases v' <;> simp_all

theorem ctrlNums_injective : ∀ c c' : Ctrl, ctrlNums c = ctrlNums c' → c = c' := by
  intro c c' h
  cases c <;> cases c' <;>
    simp only [ctrlNums, List.cons.injEq, and_true] at h <;>
    first
      | rfl
      | (exfalso; omega)
      | (obtain ⟨-, h1, h2, h3⟩ := h; subst h1; subst h2; subst h3; rfl)
      | (obtain ⟨-, h1⟩ := h; rw [bool_ite_inj h1])

theorem frameNums_injective : ∀ l l' : List Frame,
    l.flatMap frameNums = l'.flatMap frameNums → l = l' := by
  intro l
  induction l with
  | nil =>
      intro l' h
      cases l' with
      | nil => rfl
      | cons fr' l' => simp [frameNums] at h
  | cons fr l ih =>
      intro l' h
      cases l' with
      | nil => simp [frameNums] at h
      | cons fr' l' =>
          simp only [List.flatMap_cons, frameNums, List.cons_append, List.nil_append,
            List.cons.injEq] at h
          obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
          have hph : fr.ph = fr'.ph := by
            by_cases p : fr.ph <;> by_cases p' : fr'.ph <;> simp [p, p'] at h5 ⊢
          have : fr = fr' := by
            cases fr; cases fr'; simp_all
          rw [this, ih l' h6]

/-- The numerical components of a simulator state (other than the space bound). -/
def stNums (st : St) : List ℕ :=
  st.a₀ :: st.target :: (ctrlNums st.ctrl ++ st.stack.flatMap frameNums)

theorem stNums_injective {st st' : St} (hs : st.s = st'.s) (h : stNums st = stNums st') :
    st = st' := by
  obtain ⟨s, a₀, tg, c, S⟩ := st
  obtain ⟨s', a₀', tg', c', S'⟩ := st'
  simp only at hs
  subst hs
  simp only [stNums, List.cons.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨hc, hS⟩ := List.append_inj h3 (by rw [ctrlNums_length, ctrlNums_length])
  rw [h1, h2, ctrlNums_injective _ _ hc, frameNums_injective _ _ hS]

/-- The code of a simulator state. -/
def encSt (st : St) : ℕ := Nat.pair st.s (encList (2 ^ st.s + st.s + 4) (stNums st))

/-- Under the invariant, all components of a state are below the base used for encoding. -/
theorem good_nums_lt {st : St} (h : Good st) :
    ∀ a ∈ stNums st, a < 2 ^ st.s + st.s + 4 := by
  obtain ⟨ha₀, hrest⟩ := h
  intro a ha
  simp only [stNums, List.mem_cons, List.mem_append] at ha
  have hstack : ∀ fr ∈ st.stack, fr.k < st.s ∧ fr.a < 2 ^ st.s ∧ fr.b < 2 ^ st.s ∧
      fr.m < 2 ^ st.s := by
    revert hrest
    cases hc : st.ctrl with
    | init => intro h; rw [h.1]; simp
    | eval a b k => intro h; exact GoodStack_mem k st.stack h.2.2.2
    | ret v => intro h; obtain ⟨-, k, hk⟩ := h; exact GoodStack_mem k st.stack hk
    | halt v => intro h; rw [h.1]; simp
  have htarget : st.target ≤ 2 ^ st.s := by
    revert hrest
    cases hc : st.ctrl with
    | init => intro h; exact h.2
    | eval a b k => intro h; exact le_of_lt h.2.2.1
    | ret v => intro h; exact le_of_lt h.1
    | halt v => intro h; exact h.2
  have hctrl : ∀ a ∈ ctrlNums st.ctrl, a < 2 ^ st.s + st.s + 4 := by
    revert hrest
    cases hc : st.ctrl with
    | init => intro h a ha; simp only [ctrlNums, List.mem_cons, List.not_mem_nil] at ha
              rcases ha with rfl | rfl | rfl | rfl | h' <;> first | positivity | exact h'.elim
    | eval a' b' k =>
        intro h a ha
        have hlen : k ≤ st.s := by
          have := GoodStack_length k st.stack h.2.2.2
          omega
        simp only [ctrlNums, List.mem_cons, List.not_mem_nil] at ha
        rcases ha with rfl | rfl | rfl | rfl | h' 
        · have : (0:ℕ) < 2 ^ st.s := Nat.two_pow_pos _
          omega
        · have := h.1; omega
        · have := h.2.1; omega
        · omega
        · exact h'.elim
    | ret v =>
        intro h a ha
        simp only [ctrlNums, List.mem_cons, List.not_mem_nil] at ha
        have : (0:ℕ) < 2 ^ st.s := Nat.two_pow_pos _
        rcases ha with rfl | rfl | rfl | rfl | h'
        · omega
        · split <;> omega
        · omega
        · omega
        · exact h'.elim
    | halt v =>
        intro h a ha
        simp only [ctrlNums, List.mem_cons, List.not_mem_nil] at ha
        have : (0:ℕ) < 2 ^ st.s := Nat.two_pow_pos _
        rcases ha with rfl | rfl | rfl | rfl | h'
        · omega
        · split <;> omega
        · omega
        · omega
        · exact h'.elim
  rcases ha with rfl | rfl | ha | ha
  · omega
  · omega
  · exact hctrl a ha
  · obtain ⟨fr, hfr, hmem⟩ := List.mem_flatMap.mp ha
    obtain ⟨h1, h2, h3, h4⟩ := hstack fr hfr
    simp only [frameNums, List.mem_cons, List.not_mem_nil] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | h'
    · omega
    · omega
    · omega
    · omega
    · split <;> omega
    · exact h'.elim

theorem good_stNums_length {st : St} (h : Good st) : (stNums st).length ≤ 5 * st.s + 6 := by
  obtain ⟨-, hrest⟩ := h
  have hlen : st.stack.length ≤ st.s := by
    revert hrest
    cases hc : st.ctrl with
    | init => intro h; rw [h.1]; simp
    | eval a b k => intro h; have := GoodStack_length k st.stack h.2.2.2; omega
    | ret v => intro h; obtain ⟨-, k, hk⟩ := h; have := GoodStack_length k st.stack hk; omega
    | halt v => intro h; rw [h.1]; simp
  simp only [stNums, List.length_cons, List.length_append, ctrlNums_length]
  have : (st.stack.flatMap frameNums).length = 5 * st.stack.length := by
    induction st.stack with
    | nil => simp
    | cons fr l ih => simp only [List.flatMap_cons, List.length_append, ih, frameNums,
        List.length_cons, List.length_nil]; ring
  omega

/-- The encoding is injective on states satisfying the invariant. -/
theorem encSt_injective {st st' : St} (h : Good st) (h' : Good st')
    (he : encSt st = encSt st') : st = st' := by
  have hpair := Nat.pair_eq_pair.mp he
  have hs : st.s = st'.s := hpair.1
  refine stNums_injective hs ?_
  have hb : encList (2 ^ st.s + st.s + 4) (stNums st)
      = encList (2 ^ st.s + st.s + 4) (stNums st') := by rw [hpair.2, hs]
  exact encList_injective _ _ _ (good_nums_lt h) (by rw [hs]; exact good_nums_lt h') hb

/-- Under the invariant, codes are bounded by `2 ^ (42 * (s + 1) ^ 2)`. -/
theorem encSt_lt {st : St} (h : Good st) : encSt st < 2 ^ (42 * (st.s + 1) ^ 2) := by
  set s := st.s with hs
  set B := 2 ^ s + s + 4 with hB
  set d := 5 * s + 6 with hd
  have hP : encList B (stNums st) < (B + 1) ^ d :=
    encList_lt B d (stNums st) (good_nums_lt h) (good_stNums_length h)
  set P := encList B (stNums st) with hPdef
  have hpair : Nat.pair s P < (max s P + 1) ^ 2 := Nat.pair_lt_max_add_one_sq s P
  have hmax : max s P + 1 ≤ (B + 1) ^ (d + 1) := by
    have h3 : s + 1 ≤ B := by
      have : s < 2 ^ s := Nat.lt_two_pow_self
      omega
    have e1 : (B + 1) ^ d ≤ (B + 1) ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have e2 : B + 1 ≤ (B + 1) ^ (d + 1) := Nat.le_self_pow (by omega) _
    rcases le_total s P with hle | hle
    · rw [max_eq_right hle]; omega
    · rw [max_eq_left hle]; omega
  have hbase : B + 1 ≤ 2 ^ (s + 3) := by
    have h1 : s < 2 ^ s := Nat.lt_two_pow_self
    have h2 : 2 ^ (s + 3) = 8 * 2 ^ s := by ring
    omega
  calc encSt st = Nat.pair s P := rfl
    _ < (max s P + 1) ^ 2 := hpair
    _ ≤ ((B + 1) ^ (d + 1)) ^ 2 := Nat.pow_le_pow_left hmax 2
    _ = (B + 1) ^ (2 * (d + 1)) := by rw [← pow_mul]; ring_nf
    _ ≤ (2 ^ (s + 3)) ^ (2 * (d + 1)) := Nat.pow_le_pow_left hbase _
    _ = 2 ^ ((s + 3) * (2 * (d + 1))) := by rw [← pow_mul]
    _ ≤ 2 ^ (42 * (s + 1) ^ 2) := by
        apply Nat.pow_le_pow_right (by norm_num)
        have : (s + 3) * (2 * (5 * s + 6 + 1)) ≤ 42 * (s + 1) ^ 2 := by nlinarith
        simpa [hd] using this

/-- A left inverse of the encoding on states satisfying the invariant. -/
noncomputable def decSt (n : ℕ) : St :=
  if h : ∃ st, Good st ∧ encSt st = n then h.choose else ⟨0, 0, 0, .init, []⟩

theorem decSt_encSt {st : St} (h : Good st) : decSt (encSt st) = st := by
  have hex : ∃ st', Good st' ∧ encSt st' = encSt st := ⟨st, h, rfl⟩
  rw [decSt, dif_pos hex]
  obtain ⟨hgood, heq⟩ := hex.choose_spec
  exact encSt_injective hgood h heq

end CS

import Mathlib

/-!
# The divide-and-conquer reachability predicate

For a directed graph `edge` on the natural numbers and a "space bound" `s`, we define
`Reach s edge k a b`, the Savitch predicate: `b` can be reached from `a` by a path of
length at most `2 ^ k` all of whose intermediate vertices are `< 2 ^ s`.  It obeys the
divide-and-conquer recursion which is the heart of Savitch's theorem.

The main results are:

* `CS.Reach.sound`: `Reach s edge k a b` implies `b` is reachable from `a`;
* `CS.Reach.complete`: if every vertex reachable from `a` is `< 2 ^ s`, then reachability
  from `a` implies `Reach s edge s a b`.
-/

namespace CS

/-- The Savitch reachability predicate: `Reach s edge k a b` says that `b` can be reached
from `a` by a path of length at most `2 ^ k` whose intermediate vertices are all `< 2 ^ s`. -/
def Reach (s : ℕ) (edge : ℕ → ℕ → Prop) : ℕ → ℕ → ℕ → Prop
  | 0, a, b => a = b ∨ edge a b
  | k + 1, a, b => ∃ m, m < 2 ^ s ∧ Reach s edge k a m ∧ Reach s edge k m b

theorem Reach_zero (s : ℕ) (edge : ℕ → ℕ → Prop) (a b : ℕ) :
    Reach s edge 0 a b ↔ (a = b ∨ edge a b) := Iff.rfl

theorem Reach_succ (s : ℕ) (edge : ℕ → ℕ → Prop) (k a b : ℕ) :
    Reach s edge (k + 1) a b ↔ ∃ m, m < 2 ^ s ∧ Reach s edge k a m ∧ Reach s edge k m b :=
  Iff.rfl

variable {s : ℕ} {edge : ℕ → ℕ → Prop}

/-- Soundness: the Savitch predicate only asserts genuine reachability. -/
theorem Reach.sound : ∀ {k a b : ℕ}, Reach s edge k a b → Relation.ReflTransGen edge a b := by
  intro k
  induction k with
  | zero =>
      rintro a b (rfl | h)
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single h
  | succ k ih =>
      rintro a b ⟨m, _, h1, h2⟩
      exact (ih h1).trans (ih h2)

/-- `IsPath edge p t a b` says that `p 0, p 1, …, p t` is a walk from `a` to `b`. -/
def IsPath (edge : ℕ → ℕ → Prop) (p : ℕ → ℕ) (t a b : ℕ) : Prop :=
  p 0 = a ∧ p t = b ∧ ∀ i, i < t → edge (p i) (p (i + 1))

/-- Every vertex of a walk starting at `a` is reachable from `a`. -/
theorem IsPath.reachable_vertex {p : ℕ → ℕ} {t a b : ℕ} (h : IsPath edge p t a b) :
    ∀ i, i ≤ t → Relation.ReflTransGen edge a (p i) := by
  intro i hi
  induction i with
  | zero => rw [h.1]
  | succ i ih => exact (ih (by omega)).tail (h.2.2 i (by omega))

theorem IsPath.reflTransGen {p : ℕ → ℕ} {t a b : ℕ} (h : IsPath edge p t a b) :
    Relation.ReflTransGen edge a b := by
  have := h.reachable_vertex t le_rfl
  rwa [h.2.1] at this

/-- Reachability is witnessed by a walk. -/
theorem exists_isPath_of_reflTransGen {a b : ℕ} (h : Relation.ReflTransGen edge a b) :
    ∃ p t, IsPath edge p t a b := by
  induction h with
  | refl => exact ⟨fun _ => a, 0, rfl, rfl, by omega⟩
  | @tail c d _ hcd ih =>
      obtain ⟨p, t, h0, ht, hstep⟩ := ih
      refine ⟨fun i => if i ≤ t then p i else d, t + 1, ?_, ?_, ?_⟩
      · simpa using h0
      · simp
      · intro i hi
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
        · have h1 : i ≤ t := le_of_lt h
          have h2 : i + 1 ≤ t := h
          simp only [h1, h2, if_pos]
          exact hstep i h
        · subst h
          have h1 : ¬ (i + 1 ≤ i) := by omega
          simp only [le_refl, if_pos, if_neg h1]
          rw [ht]
          exact hcd

/-- A walk of length at most `2 ^ k` whose vertices are all `< 2 ^ s` witnesses the
Savitch predicate at level `k`. -/
theorem Reach.of_isPath :
    ∀ (k : ℕ) (p : ℕ → ℕ) (t a b : ℕ), IsPath edge p t a b → t ≤ 2 ^ k →
      (∀ i, i ≤ t → p i < 2 ^ s) → Reach s edge k a b := by
  intro k
  induction k with
  | zero =>
      intro p t a b hp ht _
      obtain ⟨h0, htb, hstep⟩ := hp
      simp only [pow_zero] at ht
      interval_cases t
      · exact Or.inl (by rw [← h0, htb])
      · refine Or.inr ?_
        have := hstep 0 (by omega)
        rwa [h0, show (0 : ℕ) + 1 = 1 from rfl, htb] at this
  | succ k ih =>
      intro p t a b hp ht hb
      obtain ⟨h0, htb, hstep⟩ := hp
      set t1 := min t (2 ^ k) with ht1
      have ht1t : t1 ≤ t := min_le_left _ _
      refine ⟨p t1, hb t1 ht1t, ?_, ?_⟩
      · refine ih p t1 a (p t1) ⟨h0, rfl, ?_⟩ (min_le_right _ _) (fun i hi => hb i (by omega))
        intro i hi
        exact hstep i (by omega)
      · refine ih (fun i => p (t1 + i)) (t - t1) (p t1) b ⟨by simp, ?_, ?_⟩ ?_ ?_
        · simp only []
          rw [show t1 + (t - t1) = t from by omega]
          exact htb
        · intro i hi
          have : t1 + i < t := by omega
          have := hstep (t1 + i) this
          simpa [Nat.add_assoc] using this
        · have hk : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
          omega
        · intro i hi
          exact hb (t1 + i) (by omega)

/-- Any walk whose vertices lie below `2 ^ s` can be shortened to one of length at most
`2 ^ s`. -/
theorem exists_short_isPath :
    ∀ (t : ℕ) (p : ℕ → ℕ) (a b : ℕ), IsPath edge p t a b → (∀ i, i ≤ t → p i < 2 ^ s) →
      ∃ (t' : ℕ) (p' : ℕ → ℕ), t' ≤ 2 ^ s ∧ IsPath edge p' t' a b ∧
        (∀ i, i ≤ t' → p' i < 2 ^ s) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro p a b hp hbnd
    by_cases ht : t ≤ 2 ^ s
    · exact ⟨t, p, ht, hp, hbnd⟩
    · push_neg at ht
      -- pigeonhole: two vertices of the walk coincide
      have hmaps : ∀ i ∈ Finset.range (t + 1), p i ∈ Finset.range (2 ^ s) := by
        intro i hi
        simp only [Finset.mem_range] at hi ⊢
        exact hbnd i (by omega)
      have hcard : (Finset.range (2 ^ s)).card < (Finset.range (t + 1)).card := by
        simp only [Finset.card_range]; omega
      obtain ⟨i, hi, j, hj, hij, hpij⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
      simp only [Finset.mem_range] at hi hj
      -- WLOG `i < j`
      obtain ⟨i, j, hi, hj, hij, hpij⟩ :
          ∃ i j : ℕ, i < t + 1 ∧ j < t + 1 ∧ i < j ∧ p i = p j := by
        rcases lt_or_gt_of_ne hij with h | h
        · exact ⟨i, j, hi, hj, h, hpij⟩
        · exact ⟨j, i, hj, hi, h, hpij.symm⟩
      obtain ⟨h0, htb, hstep⟩ := hp
      set d := j - i with hd
      have hd0 : 0 < d := by omega
      set q : ℕ → ℕ := fun n => if n ≤ i then p n else p (n + d) with hq
      have hqle : ∀ n, n ≤ i → q n = p n := by intro n hn; simp [hq, hn]
      have hqgt : ∀ n, i < n → q n = p (n + d) := by
        intro n hn; simp [hq, Nat.not_le.mpr hn]
      have hlen : t - d < t := by omega
      have hpath : IsPath edge q (t - d) a b := by
        refine ⟨?_, ?_, ?_⟩
        · rw [hqle 0 (by omega)]; exact h0
        · rcases Nat.lt_or_ge i (t - d) with h2 | h2
          · rw [hqgt _ h2, show t - d + d = t from by omega]; exact htb
          · have : t - d = i := by omega
            rw [this, hqle i le_rfl, hpij, show j = t from by omega]
            exact htb
        · intro n hn
          rcases lt_or_ge n i with h | h
          · rw [hqle n (by omega), hqle (n + 1) (by omega)]
            exact hstep n (by omega)
          rcases eq_or_lt_of_le h with h' | h'
          · rw [hqle n (by omega), hqgt (n + 1) (by omega), ← h', hpij,
              show i + 1 + d = j + 1 from by omega]
            exact hstep j (by omega)
          · rw [hqgt n h', hqgt (n + 1) (by omega), show n + 1 + d = (n + d) + 1 from by omega]
            exact hstep (n + d) (by omega)
      have hqbnd : ∀ n, n ≤ t - d → q n < 2 ^ s := by
        intro n hn
        rcases Nat.lt_or_ge i n with h | h
        · rw [hqgt n h]; exact hbnd (n + d) (by omega)
        · rw [hqle n h]; exact hbnd n (by omega)
      exact ih (t - d) hlen q a b hpath hqbnd

/-- Completeness: if all configurations reachable from `a` fit in `s` bits, then
reachability is captured by the Savitch predicate at level `s`. -/
theorem Reach.complete {a b : ℕ} (hbound : ∀ c, Relation.ReflTransGen edge a c → c < 2 ^ s)
    (h : Relation.ReflTransGen edge a b) : Reach s edge s a b := by
  obtain ⟨p, t, hp⟩ := exists_isPath_of_reflTransGen h
  have hbnd : ∀ i, i ≤ t → p i < 2 ^ s := fun i hi => hbound _ (hp.reachable_vertex i hi)
  obtain ⟨t', p', ht', hp', hbnd'⟩ := exists_short_isPath t p a b hp hbnd
  exact Reach.of_isPath s p' t' a b hp' ht' hbnd'

/-- The Savitch predicate at level `s` characterises reachability, when the reachable set
fits in `s` bits. -/
theorem Reach.iff_reflTransGen {a b : ℕ}
    (hbound : ∀ c, Relation.ReflTransGen edge a c → c < 2 ^ s) :
    Reach s edge s a b ↔ Relation.ReflTransGen edge a b :=
  ⟨Reach.sound, Reach.complete hbound⟩

end CS

import RequestProject.Savitch.Interp

/-!
# Big-step correctness of the Savitch simulator

We show that the depth-first evaluation of the Savitch recursion implemented by `CS.step`
computes the predicate `CS.Reach`, and that the outer loop over target configurations halts
with the verdict "some accepting configuration below `2 ^ s` is reachable".
-/

namespace CS

open Classical

variable {Γ : Type}

/-- The inner loop over midpoints.  Given that the recursive calls at level `k` work
(hypothesis `ih`), the loop starting at midpoint `m` returns whether some midpoint
`m' ∈ [m, 2 ^ s)` splits the path. -/
theorem bigstep_loop (N : NMachine Γ) (x : List Γ) (s a₀ k : ℕ)
    (ih : ∀ (a b tg : ℕ) (S : List Frame), ∃ (t : ℕ) (v : Bool),
      iter N x t ⟨s, a₀, tg, .eval a b k, S⟩ = ⟨s, a₀, tg, .ret v, S⟩ ∧
        (v = true ↔ Reach s (N.stepRel x) k a b)) :
    ∀ (j a b tg m : ℕ) (S : List Frame), m < 2 ^ s → 2 ^ s - m ≤ j →
      ∃ (t : ℕ) (v : Bool),
        iter N x t ⟨s, a₀, tg, .eval a m k, ⟨a, b, k, m, false⟩ :: S⟩ =
            ⟨s, a₀, tg, .ret v, S⟩ ∧
          (v = true ↔ ∃ m', m ≤ m' ∧ m' < 2 ^ s ∧
              Reach s (N.stepRel x) k a m' ∧ Reach s (N.stepRel x) k m' b) := by
  intro j
  induction j with
  | zero => intro a b tg m S hm hj; omega
  | succ j ihj =>
    intro a b tg m S hm hj
    obtain ⟨t1, v1, ht1, hv1⟩ := ih a m tg (⟨a, b, k, m, false⟩ :: S)
    by_cases hR1 : Reach s (N.stepRel x) k a m
    · -- the first half succeeded; go on to the second half
      have hv1t : v1 = true := hv1.mpr hR1
      subst hv1t
      have e2 : iter N x (t1 + 1) ⟨s, a₀, tg, .eval a m k, ⟨a, b, k, m, false⟩ :: S⟩ =
          ⟨s, a₀, tg, .eval m b k, ⟨a, b, k, m, true⟩ :: S⟩ := by
        rw [iter_succ_of N x ht1, stepx_ret_cons]; simp
      obtain ⟨t2, v2, ht2, hv2⟩ := ih m b tg (⟨a, b, k, m, true⟩ :: S)
      have e3 : iter N x (t1 + 1 + t2) ⟨s, a₀, tg, .eval a m k, ⟨a, b, k, m, false⟩ :: S⟩ =
          ⟨s, a₀, tg, .ret v2, ⟨a, b, k, m, true⟩ :: S⟩ := iter_trans N x e2 ht2
      by_cases hR2 : Reach s (N.stepRel x) k m b
      · have hv2t : v2 = true := hv2.mpr hR2
        subst hv2t
        refine ⟨t1 + 1 + t2 + 1, true, ?_, ?_⟩
        · rw [iter_succ_of N x e3, stepx_ret_cons]; simp
        · simp only [true_iff]
          exact ⟨m, le_rfl, hm, hR1, hR2⟩
      · have hv2f : v2 = false := by
          by_contra hcon
          exact hR2 (hv2.mp (by simpa using hcon))
        subst hv2f
        by_cases hnext : m + 1 < 2 ^ s
        · have e4 : iter N x (t1 + 1 + t2 + 1)
              ⟨s, a₀, tg, .eval a m k, ⟨a, b, k, m, false⟩ :: S⟩ =
              ⟨s, a₀, tg, .eval a (m + 1) k, ⟨a, b, k, m + 1, false⟩ :: S⟩ := by
            rw [iter_succ_of N x e3, stepx_ret_cons]; simp [hnext]
          obtain ⟨t3, v3, ht3, hv3⟩ := ihj a b tg (m + 1) S hnext (by omega)
          refine ⟨t1 + 1 + t2 + 1 + t3, v3, iter_trans N x e4 ht3, ?_⟩
          rw [hv3]
          constructor
          · rintro ⟨m', hm1, hm2, hm3, hm4⟩; exact ⟨m', by omega, hm2, hm3, hm4⟩
          · rintro ⟨m', hm1, hm2, hm3, hm4⟩
            rcases eq_or_lt_of_le hm1 with h | h
            · exact absurd (h ▸ hm4) hR2
            · exact ⟨m', by omega, hm2, hm3, hm4⟩
        · refine ⟨t1 + 1 + t2 + 1, false, ?_, ?_⟩
          · rw [iter_succ_of N x e3, stepx_ret_cons]; simp [hnext]
          · simp only [Bool.false_eq_true, false_iff]
            rintro ⟨m', hm1, hm2, hm3, hm4⟩
            have : m' = m := by omega
            exact absurd (this ▸ hm4) hR2
    · -- the first half failed; move to the next midpoint
      have hv1f : v1 = false := by
        by_contra hcon
        exact hR1 (hv1.mp (by simpa using hcon))
      subst hv1f
      by_cases hnext : m + 1 < 2 ^ s
      · have e2 : iter N x (t1 + 1) ⟨s, a₀, tg, .eval a m k, ⟨a, b, k, m, false⟩ :: S⟩ =
            ⟨s, a₀, tg, .eval a (m + 1) k, ⟨a, b, k, m + 1, false⟩ :: S⟩ := by
          rw [iter_succ_of N x ht1, stepx_ret_cons]; simp [hnext]
        obtain ⟨t3, v3, ht3, hv3⟩ := ihj a b tg (m + 1) S hnext (by omega)
        refine ⟨t1 + 1 + t3, v3, iter_trans N x e2 ht3, ?_⟩
        rw [hv3]
        constructor
        · rintro ⟨m', hm1, hm2, hm3, hm4⟩; exact ⟨m', by omega, hm2, hm3, hm4⟩
        · rintro ⟨m', hm1, hm2, hm3, hm4⟩
          rcases eq_or_lt_of_le hm1 with h | h
          · exact absurd (h ▸ hm3) hR1
          · exact ⟨m', by omega, hm2, hm3, hm4⟩
      · refine ⟨t1 + 1, false, ?_, ?_⟩
        · rw [iter_succ_of N x ht1, stepx_ret_cons]; simp [hnext]
        · simp only [Bool.false_eq_true, false_iff]
          rintro ⟨m', hm1, hm2, hm3, hm4⟩
          have : m' = m := by omega
          exact absurd (this ▸ hm3) hR1

/-- Big-step correctness of the recursive evaluation: from a state asking for
`Reach s edge k a b`, the simulator returns the right boolean, leaving the stack intact. -/
theorem bigstep_eval (N : NMachine Γ) (x : List Γ) (s a₀ : ℕ) :
    ∀ (k a b tg : ℕ) (S : List Frame), ∃ (t : ℕ) (v : Bool),
      iter N x t ⟨s, a₀, tg, .eval a b k, S⟩ = ⟨s, a₀, tg, .ret v, S⟩ ∧
        (v = true ↔ Reach s (N.stepRel x) k a b) := by
  intro k
  induction k with
  | zero =>
      intro a b tg S
      refine ⟨1, decide (a = b ∨ N.stepRel x a b), ?_, ?_⟩
      · rw [iter_one]; rfl
      · rw [Reach_zero]; exact decide_eq_true_iff
  | succ k ih =>
      intro a b tg S
      have hpos : (0 : ℕ) < 2 ^ s := Nat.two_pow_pos s
      obtain ⟨t, v, ht, hv⟩ :=
        bigstep_loop N x s a₀ k ih (2 ^ s) a b tg 0 S hpos (by omega)
      have e1 : iter N x 1 ⟨s, a₀, tg, .eval a b (k + 1), S⟩ =
          ⟨s, a₀, tg, .eval a 0 k, ⟨a, b, k, 0, false⟩ :: S⟩ := by
        rw [iter_one, stepx_eval_succ]
      refine ⟨1 + t, v, iter_trans N x e1 ht, ?_⟩
      rw [hv, Reach_succ]
      constructor
      · rintro ⟨m, -, hm2, hm3, hm4⟩; exact ⟨m, hm2, hm3, hm4⟩
      · rintro ⟨m, hm2, hm3, hm4⟩; exact ⟨m, Nat.zero_le _, hm2, hm3, hm4⟩

/-- Big-step correctness of the outer loop over candidate accepting configurations. -/
theorem bigstep_init (N : NMachine Γ) (x : List Γ) (s a₀ : ℕ) :
    ∀ (j tg : ℕ), 2 ^ s - tg ≤ j →
      ∃ (t : ℕ) (v : Bool) (tg' : ℕ),
        iter N x t ⟨s, a₀, tg, .init, []⟩ = ⟨s, a₀, tg', .halt v, []⟩ ∧
          (v = true ↔ ∃ c, tg ≤ c ∧ c < 2 ^ s ∧ N.accept c ∧
            Reach s (N.stepRel x) s a₀ c) := by
  intro j
  induction j with
  | zero =>
      intro tg hj
      have htg : ¬ tg < 2 ^ s := by omega
      refine ⟨1, false, tg, ?_, ?_⟩
      · rw [iter_one, stepx_init, if_neg htg]
      · simp only [Bool.false_eq_true, false_iff]
        rintro ⟨c, hc1, hc2, -, -⟩
        omega
  | succ j ihj =>
      intro tg hj
      by_cases htg : tg < 2 ^ s
      · by_cases hacc : N.accept tg
        · have e1 : iter N x 1 ⟨s, a₀, tg, .init, []⟩ =
              ⟨s, a₀, tg, .eval a₀ tg s, []⟩ := by
            rw [iter_one, stepx_init, if_pos htg, if_pos hacc]
          obtain ⟨t1, v1, ht1, hv1⟩ := bigstep_eval N x s a₀ s a₀ tg tg []
          have e2 : iter N x (1 + t1) ⟨s, a₀, tg, .init, []⟩ =
              ⟨s, a₀, tg, .ret v1, []⟩ := iter_trans N x e1 ht1
          by_cases hR : Reach s (N.stepRel x) s a₀ tg
          · have hv1t : v1 = true := hv1.mpr hR
            subst hv1t
            refine ⟨1 + t1 + 1, true, tg, ?_, ?_⟩
            · rw [iter_succ_of N x e2, stepx_ret_nil]; simp
            · simp only [true_iff]
              exact ⟨tg, le_rfl, htg, hacc, hR⟩
          · have hv1f : v1 = false := by
              by_contra hcon
              exact hR (hv1.mp (by simpa using hcon))
            subst hv1f
            have e3 : iter N x (1 + t1 + 1) ⟨s, a₀, tg, .init, []⟩ =
                ⟨s, a₀, tg + 1, .init, []⟩ := by
              rw [iter_succ_of N x e2, stepx_ret_nil]; simp
            obtain ⟨t2, v2, tg', ht2, hv2⟩ := ihj (tg + 1) (by omega)
            refine ⟨1 + t1 + 1 + t2, v2, tg', iter_trans N x e3 ht2, ?_⟩
            rw [hv2]
            constructor
            · rintro ⟨c, hc1, hc2, hc3, hc4⟩; exact ⟨c, by omega, hc2, hc3, hc4⟩
            · rintro ⟨c, hc1, hc2, hc3, hc4⟩
              rcases eq_or_lt_of_le hc1 with h | h
              · exact absurd (h ▸ hc4) hR
              · exact ⟨c, by omega, hc2, hc3, hc4⟩
        · have e1 : iter N x 1 ⟨s, a₀, tg, .init, []⟩ = ⟨s, a₀, tg + 1, .init, []⟩ := by
            rw [iter_one, stepx_init, if_pos htg, if_neg hacc]
          obtain ⟨t2, v2, tg', ht2, hv2⟩ := ihj (tg + 1) (by omega)
          refine ⟨1 + t2, v2, tg', iter_trans N x e1 ht2, ?_⟩
          rw [hv2]
          constructor
          · rintro ⟨c, hc1, hc2, hc3, hc4⟩; exact ⟨c, by omega, hc2, hc3, hc4⟩
          · rintro ⟨c, hc1, hc2, hc3, hc4⟩
            rcases eq_or_lt_of_le hc1 with h | h
            · exact absurd (h ▸ hc3) hacc
            · exact ⟨c, by omega, hc2, hc3, hc4⟩
      · refine ⟨1, false, tg, ?_, ?_⟩
        · rw [iter_one, stepx_init, if_neg htg]
        · simp only [Bool.false_eq_true, false_iff]
          rintro ⟨c, hc1, hc2, -, -⟩
          omega

/-- The simulator, started in its initial state, halts with the verdict "some accepting
configuration below `2 ^ s` is `Reach`-able from `a₀`". -/
theorem bigstep_run (N : NMachine Γ) (x : List Γ) (s a₀ : ℕ) :
    ∃ (t : ℕ) (v : Bool) (tg' : ℕ),
      iter N x t ⟨s, a₀, 0, .init, []⟩ = ⟨s, a₀, tg', .halt v, []⟩ ∧
        (v = true ↔ ∃ c, c < 2 ^ s ∧ N.accept c ∧ Reach s (N.stepRel x) s a₀ c) := by
  obtain ⟨t, v, tg', ht, hv⟩ := bigstep_init N x s a₀ (2 ^ s) 0 (by simp)
  refine ⟨t, v, tg', ht, ?_⟩
  rw [hv]
  constructor
  · rintro ⟨c, -, hc2, hc3, hc4⟩; exact ⟨c, hc2, hc3, hc4⟩
  · rintro ⟨c, hc2, hc3, hc4⟩; exact ⟨c, Nat.zero_le _, hc2, hc3, hc4⟩

end CS

