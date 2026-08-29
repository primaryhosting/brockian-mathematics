import RequestProject.Savitch.Machine

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Savitch's theorem

We model a space-`s` machine by its configuration graph: it has at most `2 ^ s`
configurations (`s` bits of workspace), a start configuration, an acceptance
predicate, and a transition relation (a relation for nondeterministic machines, a
function for deterministic ones).  A nondeterministic machine accepts when some
accepting configuration is reachable from the start configuration; a deterministic
machine accepts when its (unique) run visits an accepting configuration.

The main theorem `CS.savitch` states `NSPACE f ⊆ DSPACE (9 * (f + 1) ^ 2)`, i.e.
nondeterministic space `f` is contained in deterministic space `O(f ^ 2)`, and
`CS.PSPACE_eq_NPSPACE` deduces `PSPACE = NPSPACE`.
-/

namespace CS

open Savitch

/-- A nondeterministic machine using space `s`: at most `2 ^ s` configurations. -/
structure NMachine (s : ℕ) where
  /-- Number of configurations. -/
  size : ℕ
  /-- The space bound: `s` bits of workspace. -/
  hsize : size ≤ 2 ^ s
  /-- The (nondeterministic) transition relation. -/
  step : Fin size → Fin size → Bool
  /-- The initial configuration. -/
  start : Fin size
  /-- The accepting configurations. -/
  acc : Fin size → Bool

/-- A nondeterministic machine accepts if some accepting configuration is reachable. -/
def NMachine.Accepts {s : ℕ} (M : NMachine s) : Prop :=
  ∃ c, Relation.ReflTransGen (fun x y => M.step x y = true) M.start c ∧ M.acc c = true

/-- A deterministic machine using space `s`: at most `2 ^ s` configurations. -/
structure DMachine (s : ℕ) where
  /-- Number of configurations. -/
  size : ℕ
  /-- The space bound: `s` bits of workspace. -/
  hsize : size ≤ 2 ^ s
  /-- The transition function. -/
  step : Fin size → Fin size
  /-- The initial configuration. -/
  start : Fin size
  /-- The accepting configurations. -/
  acc : Fin size → Bool

/-- The configuration of a deterministic machine after `t` steps. -/
def DMachine.run {s : ℕ} (D : DMachine s) (t : ℕ) : Fin D.size := D.step^[t] D.start

/-- A deterministic machine accepts if its run visits an accepting configuration. -/
def DMachine.Accepts {s : ℕ} (D : DMachine s) : Prop := ∃ t, D.acc (D.run t) = true

/-- A deterministic machine halts if its run reaches a fixed point. -/
def DMachine.Halts {s : ℕ} (D : DMachine s) : Prop := ∃ t, D.step (D.run t) = D.run t

/-- `NSPACE f`: languages decided by a nondeterministic machine using space `f n`
on inputs of length `n`. -/
def NSPACE (f : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ M : (x : List Bool) → NMachine (f x.length), ∀ x, x ∈ L ↔ (M x).Accepts}

/-- `DSPACE g`: languages decided by a halting deterministic machine using space `g n`
on inputs of length `n`. -/
def DSPACE (g : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ M : (x : List Bool) → DMachine (g x.length),
        (∀ x, (M x).Halts) ∧ ∀ x, x ∈ L ↔ (M x).Accepts}

/-! ### Padding: space classes are monotone -/

theorem NSPACE_mono {f f' : ℕ → ℕ} (h : ∀ n, f n ≤ f' n) : NSPACE f ⊆ NSPACE f' := by
  rintro L ⟨M, hM⟩
  refine ⟨fun x => { (M x) with
      hsize := le_trans (M x).hsize (Nat.pow_le_pow_right (by norm_num) (h x.length)) }, ?_⟩
  intro x
  exact hM x

theorem DSPACE_mono {g g' : ℕ → ℕ} (h : ∀ n, g n ≤ g' n) : DSPACE g ⊆ DSPACE g' := by
  rintro L ⟨M, hH, hM⟩
  refine ⟨fun x => { (M x) with
      hsize := le_trans (M x).hsize (Nat.pow_le_pow_right (by norm_num) (h x.length)) }, ?_, ?_⟩
  · intro x; exact hH x
  · intro x; exact hM x

/-! ### Adding a unique accepting configuration -/

section Sink

variable {s : ℕ} (M : NMachine s)

/-- The configuration graph of `M` with an extra sink node, reached from every
accepting configuration. -/
def sinkRel : Fin (M.size + 1) → Fin (M.size + 1) → Bool := fun x y =>
  if hx : (x : ℕ) < M.size then
    (if hy : (y : ℕ) < M.size then M.step ⟨x, hx⟩ ⟨y, hy⟩ else M.acc ⟨x, hx⟩)
  else false

theorem sink_reach_aux {z : Fin (M.size + 1)}
    (h : Relation.ReflTransGen (fun x y => sinkRel M x y = true) (Fin.castSucc M.start) z) :
    (∃ hz : (z : ℕ) < M.size,
        Relation.ReflTransGen (fun x y => M.step x y = true) M.start ⟨z, hz⟩) ∨ M.Accepts := by
  induction h with
  | refl => exact Or.inl ⟨by simp, by simp⟩
  | @tail y z _ hyz ih =>
    rcases ih with ⟨hy', path⟩ | hacc
    · rw [sinkRel, dif_pos hy'] at hyz
      by_cases hz : (z : ℕ) < M.size
      · rw [dif_pos hz] at hyz
        exact Or.inl ⟨hz, path.tail hyz⟩
      · rw [dif_neg hz] at hyz
        exact Or.inr ⟨⟨y, hy'⟩, path, hyz⟩
    · exact Or.inr hacc

theorem sink_lift {c : Fin M.size}
    (h : Relation.ReflTransGen (fun x y => M.step x y = true) M.start c) :
    Relation.ReflTransGen (fun x y => sinkRel M x y = true)
      (Fin.castSucc M.start) (Fin.castSucc c) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z _ hyz ih =>
    refine ih.tail ?_
    rw [sinkRel, dif_pos (by simp : ((Fin.castSucc y : Fin (M.size + 1)) : ℕ) < M.size),
      dif_pos (by simp : ((Fin.castSucc z : Fin (M.size + 1)) : ℕ) < M.size)]
    simpa using hyz

theorem sink_reach_iff :
    Relation.ReflTransGen (fun x y => sinkRel M x y = true)
        (Fin.castSucc M.start) (Fin.last M.size) ↔ M.Accepts := by
  constructor
  · intro h
    rcases sink_reach_aux M h with ⟨hz, -⟩ | hacc
    · simp at hz
    · exact hacc
  · rintro ⟨c, path, hacc⟩
    refine (sink_lift M path).tail ?_
    rw [sinkRel, dif_pos (by simp : ((Fin.castSucc c : Fin (M.size + 1)) : ℕ) < M.size),
      dif_neg (by simp)]
    simpa using hacc

end Sink

/-! ### Arithmetic bound on the number of configurations -/

theorem savitch_card_bound {n s : ℕ} (hn : n ≤ 2 ^ (s + 1)) :
    (n * n + 2) * (2 * (n * n * n) + 1) ^ (s + 1) ≤ 2 ^ (9 * (s + 1) ^ 2) := by
  set t := s + 1 with ht
  have ht1 : 1 ≤ t := by omega
  have h1 : n * n + 2 ≤ 2 ^ (2 * t + 1) := by
    have hnn : n * n ≤ 2 ^ (2 * t) := by
      calc n * n ≤ 2 ^ t * 2 ^ t := Nat.mul_le_mul hn hn
      _ = 2 ^ (2 * t) := by rw [← pow_add]; ring_nf
    have h2 : (2 : ℕ) ≤ 2 ^ (2 * t) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc n * n + 2 ≤ 2 ^ (2 * t) + 2 ^ (2 * t) := by omega
    _ = 2 ^ (2 * t + 1) := by rw [pow_succ]; ring
  have h2 : 2 * (n * n * n) + 1 ≤ 2 ^ (3 * t + 2) := by
    have hnnn : n * n * n ≤ 2 ^ (3 * t) := by
      calc n * n * n ≤ 2 ^ t * 2 ^ t * 2 ^ t := Nat.mul_le_mul (Nat.mul_le_mul hn hn) hn
      _ = 2 ^ (3 * t) := by rw [← pow_add, ← pow_add]; ring_nf
    have hle : 2 * (n * n * n) ≤ 2 ^ (3 * t + 1) := by
      calc 2 * (n * n * n) ≤ 2 * 2 ^ (3 * t) := by omega
      _ = 2 ^ (3 * t + 1) := by rw [pow_succ]; ring
    have h1' : (1 : ℕ) ≤ 2 ^ (3 * t + 1) := Nat.one_le_two_pow
    calc 2 * (n * n * n) + 1 ≤ 2 ^ (3 * t + 1) + 2 ^ (3 * t + 1) := by omega
    _ = 2 ^ (3 * t + 2) := by rw [pow_succ, pow_succ]; ring
  calc (n * n + 2) * (2 * (n * n * n) + 1) ^ t
      ≤ 2 ^ (2 * t + 1) * (2 ^ (3 * t + 2)) ^ t := Nat.mul_le_mul h1 (Nat.pow_le_pow_left h2 t)
  _ = 2 ^ (2 * t + 1 + (3 * t + 2) * t) := by rw [← pow_mul, ← pow_add]
  _ ≤ 2 ^ (9 * t ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-! ### Turning an abstract deterministic dynamical system into a `DMachine` -/

theorem iterate_conj {α β : Type*} (e : α ≃ β) (F : α → α) (t : ℕ) (x : α) :
    (fun i => e (F (e.symm i)))^[t] (e x) = e (F^[t] x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    simpa using ih (F x)

/-- Any deterministic dynamical system on a finite type of size at most `2 ^ s` is a
space-`s` deterministic machine. -/
theorem exists_dmachine {s : ℕ} {C : Type} [Fintype C] (hcard : Fintype.card C ≤ 2 ^ s)
    (F : C → C) (c₀ : C) (P : C → Bool) :
    ∃ D : DMachine s, (∀ t, D.acc (D.run t) = P (F^[t] c₀)) ∧
      (∀ t, D.step (D.run t) = D.run t ↔ F (F^[t] c₀) = F^[t] c₀) := by
  classical
  let e := Fintype.equivFin C
  refine ⟨{ size := Fintype.card C
            hsize := hcard
            step := fun i => e (F (e.symm i))
            start := e c₀
            acc := fun i => P (e.symm i) }, ?_, ?_⟩
  · intro t
    show P (e.symm ((fun i => e (F (e.symm i)))^[t] (e c₀))) = P (F^[t] c₀)
    rw [iterate_conj e F t c₀, Equiv.symm_apply_apply]
  · intro t
    show (fun i => e (F (e.symm i))) ((fun i => e (F (e.symm i)))^[t] (e c₀))
        = (fun i => e (F (e.symm i)))^[t] (e c₀) ↔ _
    rw [iterate_conj e F t c₀]
    simp only [Equiv.symm_apply_apply]
    exact ⟨fun h => e.injective h, fun h => congrArg e h⟩

/-! ### Savitch's theorem for a single machine -/

/-- Savitch's simulation: a nondeterministic machine of space `s` is simulated by a
halting deterministic machine of space `9 * (s + 1) ^ 2`. -/
theorem savitch_machine {s : ℕ} (M : NMachine s) :
    ∃ D : DMachine (9 * (s + 1) ^ 2), D.Halts ∧ (D.Accepts ↔ M.Accepts) := by
  classical
  set n := M.size + 1 with hn
  set K := s + 1 with hK
  have hnle : n ≤ 2 ^ K := by
    have h1 : (1 : ℕ) ≤ 2 ^ s := Nat.one_le_two_pow
    have h2 := M.hsize
    calc n ≤ 2 ^ s + 1 := by omega
    _ ≤ 2 ^ s + 2 ^ s := by omega
    _ = 2 ^ K := by rw [hK, pow_succ]; ring
  set R := sinkRel M with hR
  set a₀ : Fin n := Fin.castSucc M.start with ha₀
  set b₀ : Fin n := Fin.last M.size with hb₀
  have hanswer : cy R K a₀ b₀ = true ↔ M.Accepts := by
    rw [cy_iff_reachLe, ← reflTransGen_iff_reachLe hnle]
    exact sink_reach_iff M
  have hcard : Fintype.card (Conf n K) ≤ 2 ^ (9 * (s + 1) ^ 2) :=
    le_trans (card_conf_le n K) (savitch_card_bound hnle)
  obtain ⟨D, hacc, hhalt⟩ := exists_dmachine hcard (dstep R K) (dstart a₀ b₀ K)
    (fun c => decide (c = dfinal n K true))
  obtain ⟨N, hN⟩ := dstep_run R K a₀ b₀
  refine ⟨D, ⟨N, (hhalt N).mpr ?_⟩, ?_⟩
  · rw [hN]
    exact dstep_dfinal _
  · constructor
    · rintro ⟨t, ht⟩
      rw [hacc t] at ht
      simp only [decide_eq_true_eq] at ht
      have h1 : (dstep R K)^[N + t] (dstart a₀ b₀ K) = dfinal n K true := by
        rw [Function.iterate_add_apply, ht]
        exact Function.iterate_fixed (dstep_dfinal _) N
      have h2 : (dstep R K)^[t + N] (dstart a₀ b₀ K) = dfinal n K (cy R K a₀ b₀) := by
        rw [Function.iterate_add_apply, hN]
        exact Function.iterate_fixed (dstep_dfinal _) t
      rw [Nat.add_comm, h1] at h2
      exact hanswer.mp (dfinal_inj h2).symm
    · intro hM
      refine ⟨N, ?_⟩
      rw [hacc N, hN, hanswer.mpr hM]
      simp

/-- **Savitch's theorem**: nondeterministic space `f` is contained in deterministic
space `O(f ^ 2)`; concretely `NSPACE f ⊆ DSPACE (9 * (f + 1) ^ 2)`. -/
theorem savitch (f : ℕ → ℕ) : NSPACE f ⊆ DSPACE (fun n => 9 * (f n + 1) ^ 2) := by
  classical
  rintro L ⟨M, hM⟩
  choose D hHalt hAcc using fun x : List Bool => savitch_machine (M x)
  exact ⟨D, hHalt, fun x => (hM x).trans (hAcc x).symm⟩

/-! ### `PSPACE = NPSPACE` -/

/-- Deterministic polynomial space. -/
def PSPACE : Set (Set (List Bool)) := {L | ∃ c k, L ∈ DSPACE (fun n => c * (n + 1) ^ k)}

/-- Nondeterministic polynomial space. -/
def NPSPACE : Set (Set (List Bool)) := {L | ∃ c k, L ∈ NSPACE (fun n => c * (n + 1) ^ k)}

theorem reflTransGen_fun_iff {α : Type*} (F : α → α) (x y : α) :
    Relation.ReflTransGen (fun u v => F u = v) x y ↔ ∃ t, F^[t] x = y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @tail b c _ hbc ih =>
      obtain ⟨t, ht⟩ := ih
      exact ⟨t + 1, by rw [Function.iterate_succ_apply', ht, hbc]⟩
  · rintro ⟨t, rfl⟩
    induction t with
    | zero => exact Relation.ReflTransGen.refl
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact ih.tail rfl

/-- A deterministic machine viewed as a nondeterministic one. -/
def DMachine.toNMachine {s : ℕ} (D : DMachine s) : NMachine s where
  size := D.size
  hsize := D.hsize
  step := fun x y => decide (D.step x = y)
  start := D.start
  acc := D.acc

theorem DMachine.toNMachine_accepts {s : ℕ} (D : DMachine s) :
    D.toNMachine.Accepts ↔ D.Accepts := by
  constructor
  · rintro ⟨c, path, hacc⟩
    have hex : ∃ t, D.step^[t] D.start = c := by
      rw [← reflTransGen_fun_iff]
      refine path.mono ?_
      intro u v h
      simpa [DMachine.toNMachine] using h
    obtain ⟨t, ht⟩ := hex
    exact ⟨t, by rw [DMachine.run, ht]; exact hacc⟩
  · rintro ⟨t, ht⟩
    refine ⟨D.run t, ?_, ht⟩
    have hpath : Relation.ReflTransGen (fun u v => D.step u = v) D.start (D.run t) :=
      (reflTransGen_fun_iff D.step D.start (D.run t)).mpr ⟨t, rfl⟩
    refine hpath.mono ?_
    intro u v h
    simpa [DMachine.toNMachine] using h

theorem PSPACE_subset_NPSPACE : PSPACE ⊆ NPSPACE := by
  rintro L ⟨c, k, M, -, hM⟩
  refine ⟨c, k, fun x => (M x).toNMachine, ?_⟩
  intro x
  rw [hM x, ← DMachine.toNMachine_accepts]

theorem NPSPACE_subset_PSPACE : NPSPACE ⊆ PSPACE := by
  rintro L ⟨c, k, hL⟩
  have h1 : L ∈ DSPACE (fun n => 9 * (c * (n + 1) ^ k + 1) ^ 2) := savitch _ hL
  refine ⟨9 * (c + 1) ^ 2, 2 * k, DSPACE_mono ?_ h1⟩
  intro n
  have hpow : (1 : ℕ) ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : c * (n + 1) ^ k + 1 ≤ (c + 1) * (n + 1) ^ k := by nlinarith
  calc 9 * (c * (n + 1) ^ k + 1) ^ 2 ≤ 9 * ((c + 1) * (n + 1) ^ k) ^ 2 :=
        Nat.mul_le_mul_left 9 (Nat.pow_le_pow_left h2 2)
  _ = 9 * (c + 1) ^ 2 * (n + 1) ^ (2 * k) := by rw [mul_pow, ← pow_mul]; ring

/-- **Savitch's theorem**, corollary: `PSPACE = NPSPACE`. -/
theorem PSPACE_eq_NPSPACE : PSPACE = NPSPACE :=
  Set.Subset.antisymm PSPACE_subset_NPSPACE NPSPACE_subset_PSPACE

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

import RequestProject.Savitch.Walk

/-!
The `canYield` predicate underlying Savitch's algorithm, and its correctness
with respect to bounded reachability.
-/

namespace CS.Savitch

variable {n : ℕ} {R : Fin n → Fin n → Bool} {a b : Fin n} {k i : ℕ}

/-- `cy R k a b` decides whether `b` is reachable from `a` in at most `2 ^ k` steps. -/
def cy (R : Fin n → Fin n → Bool) : ℕ → Fin n → Fin n → Bool
  | 0, a, b => (a == b) || R a b
  | k + 1, a, b => (List.finRange n).any (fun m => cy R k a m && cy R k m b)

theorem cy_zero (a b : Fin n) : cy R 0 a b = ((a == b) || R a b) := rfl

theorem cy_succ_iff : cy R (k + 1) a b = true ↔ ∃ m, cy R k a m = true ∧ cy R k m b = true := by
  simp [cy, List.any_eq_true]

theorem cy_iff_reachLe : ∀ (k : ℕ) (a b : Fin n), cy R k a b = true ↔ ReachLe R (2 ^ k) a b := by
  intro k
  induction k with
  | zero =>
    intro a b
    rw [cy_zero, pow_zero, reachLe_one_iff]
    simp
  | succ k ih =>
    intro a b
    rw [cy_succ_iff]
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    rw [h2, reachLe_add_iff]
    constructor
    · rintro ⟨m, h1, h2⟩
      exact ⟨m, (ih a m).mp h1, (ih m b).mp h2⟩
    · rintro ⟨m, h1, h2⟩
      exact ⟨m, (ih a m).mpr h1, (ih m b).mpr h2⟩

/-- The value computed by the midpoint loop of Savitch's algorithm, started at index `i`. -/
def loopVal (R : Fin n → Fin n → Bool) (k : ℕ) (a b : Fin n) (i : ℕ) : Bool :=
  if h : i < n then
    ((cy R k a ⟨i, h⟩ && cy R k ⟨i, h⟩ b) || loopVal R k a b (i + 1))
  else false
termination_by n - i
decreasing_by omega

theorem loopVal_of_lt (h : i < n) :
    loopVal R k a b i = ((cy R k a ⟨i, h⟩ && cy R k ⟨i, h⟩ b) || loopVal R k a b (i + 1)) := by
  rw [loopVal]
  simp [h]

theorem loopVal_of_ge (h : ¬ i < n) : loopVal R k a b i = false := by
  rw [loopVal]
  simp [h]

theorem loopVal_iff :
    ∀ i : ℕ, loopVal R k a b i = true ↔
      ∃ m : Fin n, i ≤ (m : ℕ) ∧ cy R k a m = true ∧ cy R k m b = true := by
  intro i
  induction hd : n - i using Nat.strong_induction_on generalizing i with
  | _ d ih =>
    subst hd
    by_cases h : i < n
    · rw [loopVal_of_lt h]
      simp only [Bool.or_eq_true, Bool.and_eq_true]
      rw [ih (n - (i + 1)) (by omega) (i + 1) rfl]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨m, hm, h1, h2⟩)
        · exact ⟨⟨i, h⟩, le_refl _, h1, h2⟩
        · exact ⟨m, by omega, h1, h2⟩
      · rintro ⟨m, hm, h1, h2⟩
        rcases eq_or_lt_of_le hm with heq | hlt
        · left
          have : m = ⟨i, h⟩ := Fin.ext heq.symm
          subst this
          exact ⟨h1, h2⟩
        · exact Or.inr ⟨m, by omega, h1, h2⟩
    · rw [loopVal_of_ge h]
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨m, hm, -, -⟩
      have := m.isLt
      omega

theorem cy_succ_eq_loopVal (R : Fin n → Fin n → Bool) (k : ℕ) (a b : Fin n) :
    cy R (k + 1) a b = loopVal R k a b 0 := by
  rw [Bool.eq_iff_iff, cy_succ_iff, loopVal_iff]
  constructor
  · rintro ⟨m, h1, h2⟩
    exact ⟨m, Nat.zero_le _, h1, h2⟩
  · rintro ⟨m, -, h1, h2⟩
    exact ⟨m, h1, h2⟩

end CS.Savitch

import RequestProject.Savitch.CanYield

/-!
The deterministic stack machine implementing Savitch's algorithm, with its
correctness proof and the bound on its number of configurations.
-/

namespace CS.Savitch

/-- A stack frame `(a, b, mid, ph)`: we are computing whether `b` is reachable from `a`,
currently testing the midpoint `mid`; `ph = false` means the first half is being computed,
`ph = true` the second half. -/
abbrev Frame (n : ℕ) := Fin n × Fin n × Fin n × Bool

/-- Control state: `Sum.inl (a, b)` is a call, `Sum.inr v` is a return with value `v`. -/
abbrev Ctrl (n : ℕ) := (Fin n × Fin n) ⊕ Bool

/-- A raw configuration of the Savitch machine. -/
abbrev Raw (n : ℕ) := Ctrl n × List (Frame n)

variable {n : ℕ} {R : Fin n → Fin n → Bool} {K : ℕ}

/-- The first node index, as an element of `Fin n` (`n > 0` since `a : Fin n`). -/
def mid0 (a : Fin n) : Fin n := ⟨0, a.pos⟩

@[simp] theorem mid0_val (a : Fin n) : (mid0 a : ℕ) = 0 := rfl

/-- Move to the next midpoint, or return `false` if the midpoints are exhausted. -/
def advance (a b mid : Fin n) (st : List (Frame n)) : Raw n :=
  if h : (mid : ℕ) + 1 < n then
    (Sum.inl (a, ⟨(mid : ℕ) + 1, h⟩), (a, b, ⟨(mid : ℕ) + 1, h⟩, false) :: st)
  else (Sum.inr false, st)

/-- One step of the Savitch machine with recursion depth budget `K`. -/
def stepR (R : Fin n → Fin n → Bool) (K : ℕ) : Raw n → Raw n
  | (Sum.inl (a, b), st) =>
      if K - st.length = 0 then (Sum.inr ((a == b) || R a b), st)
      else (Sum.inl (a, mid0 a), (a, b, mid0 a, false) :: st)
  | (Sum.inr v, []) => (Sum.inr v, [])
  | (Sum.inr v, (a, b, mid, ph) :: st) =>
      if ph then (if v then (Sum.inr true, st) else advance a b mid st)
      else (if v then (Sum.inl (mid, b), (a, b, mid, true) :: st) else advance a b mid st)

/-- `Reaches R K c c'` : the machine goes from `c` to `c'` in some number of steps. -/
def Reaches (R : Fin n → Fin n → Bool) (K : ℕ) (c c' : Raw n) : Prop :=
  ∃ N, (stepR R K)^[N] c = c'

theorem Reaches.rfl' {c : Raw n} : Reaches R K c c := ⟨0, rfl⟩

theorem Reaches.trans {c₁ c₂ c₃ : Raw n} (h₁ : Reaches R K c₁ c₂) (h₂ : Reaches R K c₂ c₃) :
    Reaches R K c₁ c₃ := by
  obtain ⟨N₁, h₁⟩ := h₁
  obtain ⟨N₂, h₂⟩ := h₂
  exact ⟨N₂ + N₁, by rw [Function.iterate_add_apply, h₁, h₂]⟩

theorem Reaches.one {c c' : Raw n} (h : stepR R K c = c') : Reaches R K c c' :=
  ⟨1, by simpa using h⟩

/-! ### Big-step correctness -/

theorem bigstep_call (R : Fin n → Fin n → Bool) (K : ℕ) :
    ∀ (k : ℕ) (a b : Fin n) (st : List (Frame n)), st.length + k = K →
      Reaches R K (Sum.inl (a, b), st) (Sum.inr (cy R k a b), st) := by
  intro k
  induction k with
  | zero =>
    intro a b st hst
    apply Reaches.one
    show stepR R K (Sum.inl (a, b), st) = _
    simp only [stepR]
    rw [if_pos (by omega)]
    rfl
  | succ k ih =>
    have loop : ∀ (d : ℕ) (a b mid : Fin n) (st : List (Frame n)), n - (mid : ℕ) ≤ d →
        st.length + (k + 1) = K →
        Reaches R K (Sum.inl (a, mid), (a, b, mid, false) :: st)
          (Sum.inr (loopVal R k a b (mid : ℕ)), st) := by
      intro d
      induction d with
      | zero =>
        intro a b mid st hd _
        have := mid.isLt
        omega
      | succ d ihd =>
        intro a b mid st hd hst
        have hmid : (mid : ℕ) < n := mid.isLt
        have hstack : ((a, b, mid, false) :: st).length + k = K := by simp; omega
        have hstack' : ((a, b, mid, true) :: st).length + k = K := by simp; omega
        have hunfold : loopVal R k a b (mid : ℕ) =
            ((cy R k a mid && cy R k mid b) || loopVal R k a b ((mid : ℕ) + 1)) := by
          rw [loopVal_of_lt hmid]
        -- moving to the next midpoint
        have hadv : Reaches R K (advance a b mid st) (Sum.inr (loopVal R k a b ((mid : ℕ) + 1)), st) := by
          unfold advance
          by_cases h : (mid : ℕ) + 1 < n
          · rw [dif_pos h]
            exact ihd a b ⟨(mid : ℕ) + 1, h⟩ st (by simp; omega) hst
          · rw [dif_neg h, loopVal_of_ge h]
            exact Reaches.rfl'
        refine Reaches.trans (ih a mid _ hstack) ?_
        by_cases hv : cy R k a mid = true
        · rw [hv]
          refine Reaches.trans (Reaches.one (?_ : stepR R K (Sum.inr true, (a, b, mid, false) :: st)
              = (Sum.inl (mid, b), (a, b, mid, true) :: st))) ?_
          · simp [stepR]
          refine Reaches.trans (ih mid b _ hstack') ?_
          by_cases hw : cy R k mid b = true
          · rw [hw, hunfold, hv, hw]
            refine Reaches.one ?_
            simp [stepR]
          · simp only [Bool.not_eq_true] at hw
            rw [hw, hunfold, hv, hw]
            simp only [Bool.and_false, Bool.false_or]
            exact Reaches.trans (Reaches.one (by simp [stepR] : stepR R K
              (Sum.inr false, (a, b, mid, true) :: st) = advance a b mid st)) hadv
        · simp only [Bool.not_eq_true] at hv
          rw [hv, hunfold, hv]
          simp only [Bool.false_and, Bool.false_or]
          exact Reaches.trans (Reaches.one (by simp [stepR] : stepR R K
            (Sum.inr false, (a, b, mid, false) :: st) = advance a b mid st)) hadv
    intro a b st hst
    refine Reaches.trans (Reaches.one (?_ : stepR R K (Sum.inl (a, b), st)
        = (Sum.inl (a, mid0 a), (a, b, mid0 a, false) :: st))) ?_
    · simp only [stepR]
      rw [if_neg (by omega)]
    · have := loop n a b (mid0 a) st (by simp) hst
      rw [mid0_val] at this
      rw [cy_succ_eq_loopVal]
      exact this

/-! ### The bounded configuration type -/

/-- Configurations of the Savitch machine: stacks of depth at most `K`. -/
def Conf (n K : ℕ) := {c : Raw n // c.2.length ≤ K}

theorem advance_length_le {a b mid : Fin n} {st : List (Frame n)} (h : st.length + 1 ≤ K) :
    (advance a b mid st).2.length ≤ K := by
  unfold advance
  split
  · simpa using h
  · simpa using by omega

theorem stepR_length_le {c : Raw n} (h : c.2.length ≤ K) : (stepR R K c).2.length ≤ K := by
  obtain ⟨ctrl, st⟩ := c
  simp only at h
  match ctrl, st with
  | Sum.inl (a, b), st =>
    show (stepR R K (Sum.inl (a, b), st)).2.length ≤ K
    simp only [stepR]
    split
    · exact h
    · rename_i hK
      simp only [List.length_cons]
      omega
  | Sum.inr v, [] =>
    show (stepR R K (Sum.inr v, ([] : List (Frame n)))).2.length ≤ K
    simp [stepR]
  | Sum.inr v, (a, b, mid, ph) :: st =>
    show (stepR R K (Sum.inr v, (a, b, mid, ph) :: st)).2.length ≤ K
    have h' : st.length + 1 ≤ K := by simpa using h
    simp only [stepR]
    split
    · split
      · simpa using by omega
      · exact advance_length_le h'
    · split
      · simpa using h'
      · exact advance_length_le h'

instance : DecidableEq (Conf n K) := fun _ _ => decidable_of_iff _ Subtype.ext_iff.symm

/-- Encoding of a bounded configuration into a fixed finite type. -/
def confEncode (c : Conf n K) : Ctrl n × (Fin K → Option (Frame n)) :=
  (c.1.1, fun i : Fin K => c.1.2[(i : ℕ)]?)

theorem confEncode_injective : Function.Injective (confEncode (n := n) (K := K)) := by
  rintro ⟨⟨c1, l1⟩, h1⟩ ⟨⟨c2, l2⟩, h2⟩ h
  simp only [confEncode, Prod.mk.injEq, funext_iff] at h
  obtain ⟨hc, hl⟩ := h
  simp only at h1 h2
  have hll : l1 = l2 := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < K
    · exact hl ⟨i, hi⟩
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  subst hll
  simp_all

noncomputable instance : Fintype (Conf n K) :=
  Fintype.ofInjective confEncode confEncode_injective

theorem card_conf_le (n K : ℕ) :
    Fintype.card (Conf n K) ≤ (n * n + 2) * (2 * (n * n * n) + 1) ^ K := by
  have h := Fintype.card_le_of_injective _ (confEncode_injective (n := n) (K := K))
  refine h.trans (le_of_eq ?_)
  simp [Fintype.card_prod, Fintype.card_sum, Fintype.card_option]
  ring

/-- The deterministic step function on bounded configurations. -/
def dstep (R : Fin n → Fin n → Bool) (K : ℕ) (c : Conf n K) : Conf n K :=
  ⟨stepR R K c.1, stepR_length_le c.2⟩

/-- The initial configuration: call `(a, b)` with empty stack. -/
def dstart (a b : Fin n) (K : ℕ) : Conf n K := ⟨(Sum.inl (a, b), []), by simp⟩

/-- The final configuration holding the answer `v`. -/
def dfinal (n K : ℕ) (v : Bool) : Conf n K := ⟨(Sum.inr v, []), by simp⟩

theorem dfinal_inj {v w : Bool} (h : dfinal n K v = dfinal n K w) : v = w := by
  simpa [dfinal, Subtype.ext_iff] using h

theorem dstep_dfinal (v : Bool) : dstep R K (dfinal n K v) = dfinal n K v := by
  apply Subtype.ext
  rfl

theorem dstep_iterate_val (N : ℕ) (c : Conf n K) :
    ((dstep R K)^[N] c).1 = (stepR R K)^[N] c.1 := by
  induction N generalizing c with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

/-- The machine started on `(a, b)` reaches the final configuration holding `cy R K a b`. -/
theorem dstep_run (R : Fin n → Fin n → Bool) (K : ℕ) (a b : Fin n) :
    ∃ N, (dstep R K)^[N] (dstart a b K) = dfinal n K (cy R K a b) := by
  obtain ⟨N, hN⟩ := bigstep_call R K K a b [] (by simp)
  exact ⟨N, Subtype.ext (by rw [dstep_iterate_val]; exact hN)⟩

end CS.Savitch

import Mathlib

/-!
Walks in a finite directed graph on `Fin n`, and bounded reachability.
-/

namespace CS.Savitch

variable {n K : ℕ} {R : Fin n → Fin n → Bool} {a b m : Fin n} {t t₁ t₂ : ℕ}

/-- `Walk R t a b`: there is a walk of exactly `t` steps from `a` to `b`. -/
def Walk (R : Fin n → Fin n → Bool) (t : ℕ) (a b : Fin n) : Prop :=
  ∃ f : ℕ → Fin n, f 0 = a ∧ f t = b ∧ ∀ i < t, R (f i) (f (i + 1)) = true

/-- `ReachLe R t a b`: `b` is reachable from `a` in at most `t` steps. -/
def ReachLe (R : Fin n → Fin n → Bool) (t : ℕ) (a b : Fin n) : Prop :=
  ∃ t' ≤ t, Walk R t' a b

theorem walk_zero_iff : Walk R 0 a b ↔ a = b := by
  constructor
  · rintro ⟨f, h0, ht, -⟩; exact h0 ▸ ht ▸ rfl
  · rintro rfl; exact ⟨fun _ => a, rfl, rfl, by omega⟩

theorem walk_one_of (h : R a b = true) : Walk R 1 a b := by
  refine ⟨fun i => if i = 0 then a else b, by simp, by simp, ?_⟩
  intro i hi
  interval_cases i
  simpa using h

theorem walk_one_iff : Walk R 1 a b ↔ R a b = true := by
  constructor
  · rintro ⟨f, h0, h1, hs⟩
    have := hs 0 (by omega)
    rw [h0] at this
    simpa [h1] using this
  · exact walk_one_of

theorem Walk.comp (h₁ : Walk R t₁ a m) (h₂ : Walk R t₂ m b) : Walk R (t₁ + t₂) a b := by
  obtain ⟨f, hf0, hf1, hfs⟩ := h₁
  obtain ⟨g, hg0, hg1, hgs⟩ := h₂
  refine ⟨fun u => if u ≤ t₁ then f u else g (u - t₁), ?_, ?_, ?_⟩
  · simp [hf0]
  · dsimp only
    by_cases h : t₁ + t₂ ≤ t₁
    · have ht₂ : t₂ = 0 := by omega
      subst ht₂
      rw [if_pos h, Nat.add_zero, hf1, ← hg0, ← hg1]
    · rw [if_neg h, Nat.add_sub_cancel_left, hg1]
  · intro i hi
    dsimp only
    by_cases h1 : i + 1 ≤ t₁
    · have hi1 : i ≤ t₁ := by omega
      rw [if_pos hi1, if_pos h1]
      exact hfs i (by omega)
    · have hval : (if i ≤ t₁ then f i else g (i - t₁)) = g (i - t₁) := by
        by_cases h2 : i ≤ t₁
        · have hii : i = t₁ := by omega
          subst hii
          rw [if_pos h2, hf1, ← hg0]
          congr 1
          omega
        · rw [if_neg h2]
      rw [hval, if_neg h1]
      have he : i + 1 - t₁ = (i - t₁) + 1 := by omega
      rw [he]
      exact hgs (i - t₁) (by omega)

theorem Walk.split (h : Walk R (t₁ + t₂) a b) : ∃ m, Walk R t₁ a m ∧ Walk R t₂ m b := by
  obtain ⟨f, hf0, hf1, hfs⟩ := h
  refine ⟨f t₁, ⟨f, hf0, rfl, fun i hi => hfs i (by omega)⟩,
    ⟨fun u => f (t₁ + u), rfl, by simpa using hf1, fun i hi => ?_⟩⟩
  have := hfs (t₁ + i) (by omega)
  simpa [Nat.add_assoc] using this

theorem reachLe_zero_iff : ReachLe R 0 a b ↔ a = b := by
  constructor
  · rintro ⟨t', ht', hw⟩
    have : t' = 0 := by omega
    subst this
    exact walk_zero_iff.mp hw
  · rintro rfl; exact ⟨0, le_refl _, walk_zero_iff.mpr rfl⟩

theorem reachLe_one_iff : ReachLe R 1 a b ↔ (a = b ∨ R a b = true) := by
  constructor
  · rintro ⟨t', ht', hw⟩
    interval_cases t'
    · exact Or.inl (walk_zero_iff.mp hw)
    · exact Or.inr (walk_one_iff.mp hw)
  · rintro (rfl | h)
    · exact ⟨0, by omega, walk_zero_iff.mpr rfl⟩
    · exact ⟨1, le_refl _, walk_one_of h⟩

theorem ReachLe.mono (hle : t₁ ≤ t₂) (h : ReachLe R t₁ a b) : ReachLe R t₂ a b := by
  obtain ⟨t', ht', hw⟩ := h
  exact ⟨t', le_trans ht' hle, hw⟩

theorem reachLe_add_iff :
    ReachLe R (t₁ + t₂) a b ↔ ∃ m, ReachLe R t₁ a m ∧ ReachLe R t₂ m b := by
  constructor
  · rintro ⟨t', ht', hw⟩
    have huv : t' = min t' t₁ + (t' - min t' t₁) := by omega
    rw [huv] at hw
    obtain ⟨m, h1, h2⟩ := hw.split
    exact ⟨m, ⟨_, by omega, h1⟩, ⟨_, by omega, h2⟩⟩
  · rintro ⟨m, ⟨u, hu, hw1⟩, ⟨v, hv, hw2⟩⟩
    exact ⟨u + v, by omega, hw1.comp hw2⟩

/-- Cutting a repeated vertex out of a walk. -/
theorem walk_cut {f : ℕ → Fin n} {i j : ℕ} (hf0 : f 0 = a) (hf1 : f t = b)
    (hfs : ∀ u < t, R (f u) (f (u + 1)) = true)
    (hlt : i < j) (hj : j ≤ t) (hfe : f i = f j) : ∃ t' < t, Walk R t' a b := by
  set d := j - i with hd
  have hd0 : 0 < d := by omega
  refine ⟨t - d, by omega, fun u => if u ≤ i then f u else f (u + d), ?_, ?_, ?_⟩
  · simp [hf0]
  · dsimp only
    by_cases h : t - d ≤ i
    · have htj : t = j := by omega
      have hti : t - d = i := by omega
      rw [if_pos h, hti, hfe, ← hf1, htj]
    · rw [if_neg h]
      have he : t - d + d = t := by omega
      rw [he, hf1]
  · intro u hu
    dsimp only
    by_cases hA : u + 1 ≤ i
    · have h2 : u ≤ i := by omega
      rw [if_pos h2, if_pos hA]
      exact hfs u (by omega)
    · have hgu : (if u ≤ i then f u else f (u + d)) = f (u + d) := by
        by_cases h3 : u ≤ i
        · have hui : u = i := by omega
          subst hui
          rw [if_pos h3, hfe]
          congr 1
          omega
        · rw [if_neg h3]
      rw [hgu, if_neg hA]
      have he : u + 1 + d = (u + d) + 1 := by omega
      rw [he]
      exact hfs (u + d) (by omega)

/-- A walk of length at least `n` can be shortened. -/
theorem walk_shorten (h : Walk R t a b) (ht : n ≤ t) : ∃ t' < t, Walk R t' a b := by
  obtain ⟨f, hf0, hf1, hfs⟩ := h
  have hcard : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by simp
  obtain ⟨i, j, hij, hfe⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (n + 1) => f (i : ℕ)) hcard
  have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  have hi : (i : ℕ) ≤ n := by omega
  have hj : (j : ℕ) ≤ n := by omega
  rcases lt_or_gt_of_ne hij' with hlt | hlt
  · exact walk_cut hf0 hf1 hfs hlt (by omega) hfe
  · exact walk_cut hf0 hf1 hfs hlt (by omega) hfe.symm

theorem exists_walk_lt (h : Walk R t a b) : ∃ t' < n, Walk R t' a b := by
  induction t using Nat.strong_induction_on generalizing b with
  | _ t ih =>
    by_cases hn : t < n
    · exact ⟨t, hn, h⟩
    · obtain ⟨t', ht', hw⟩ := walk_shorten h (by omega)
      exact ih t' ht' hw

theorem walk_reflTransGen (h : Walk R t a b) :
    Relation.ReflTransGen (fun x y => R x y = true) a b := by
  induction t generalizing b with
  | zero => rw [walk_zero_iff] at h; subst h; exact Relation.ReflTransGen.refl
  | succ k ih =>
    obtain ⟨m, h1, h2⟩ := h.split
    exact (ih h1).tail (walk_one_iff.mp h2)

theorem reflTransGen_walk (h : Relation.ReflTransGen (fun x y => R x y = true) a b) :
    ∃ t, Walk R t a b := by
  induction h with
  | refl => exact ⟨0, walk_zero_iff.mpr rfl⟩
  | tail hxy hyz ih =>
    obtain ⟨t, hw⟩ := ih
    exact ⟨t + 1, hw.comp (walk_one_of hyz)⟩

theorem reflTransGen_iff_reachLe (hK : n ≤ 2 ^ K) :
    Relation.ReflTransGen (fun x y => R x y = true) a b ↔ ReachLe R (2 ^ K) a b := by
  constructor
  · intro h
    obtain ⟨t, hw⟩ := reflTransGen_walk h
    obtain ⟨t', ht', hw'⟩ := exists_walk_lt hw
    exact ⟨t', by omega, hw'⟩
  · rintro ⟨t', -, hw⟩
    exact walk_reflTransGen hw

end CS.Savitch

