/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Savitch.Model
import RequestProject.Savitch.Stack

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Savitch's theorem

`NSPACE f ⊆ DSPACE (f²)`.

Given a nondeterministic machine with at most `2 ^ (c * f n + c)` configurations we build a
deterministic machine which decides, by Savitch's midpoint recursion, whether an accepting
configuration is reachable in the configuration graph.  The deterministic machine stores an
explicit recursion stack of depth `c * f n + c + 2`, each frame holding a constant number of
configurations and indices, hence it has `2 ^ O(f n ^ 2)` configurations.

As a corollary, `PSPACE = NPSPACE`.
-/

namespace CS

open Savitch

section Construction

variable (M : NMachine)

/-- The vertices of the configuration graph: the configurations of `M`, together with an extra
sink `none` which is reachable exactly from the accepting configurations.  Thus `M` accepts iff
the sink is reachable from the initial configuration. -/
abbrev Vtx (M : NMachine) (n : ℕ) : Type := Option (M.Conf n)

instance vtxFinite (n : ℕ) : Finite (Vtx M n) := by
  haveI := M.finite n; infer_instance

noncomputable instance vtxFintype (n : ℕ) : Fintype (Vtx M n) := Fintype.ofFinite _

noncomputable instance vtxDecEq (n : ℕ) : DecidableEq (Vtx M n) := Classical.decEq _

/-- An enumeration of the vertices of the configuration graph. -/
noncomputable def enum (n : ℕ) : List (Vtx M n) := (Finset.univ : Finset (Vtx M n)).toList

theorem mem_enum (n : ℕ) (x : Vtx M n) : x ∈ enum M n := by
  simp [enum]

theorem length_enum (n : ℕ) : (enum M n).length = Nat.card (Vtx M n) := by
  simp [enum, Nat.card_eq_fintype_card]

/-- Adjacency in the configuration graph, as a function of the scanned input symbol `b`. -/
def badjB (n : ℕ) (b : Bool) : Vtx M n → Vtx M n → Bool
  | some u, some v => M.next n u b v
  | some u, none => M.accept n u
  | none, _ => false

/-- Adjacency in the configuration graph of `M` on the input `x`. -/
def badjT (x : List Bool) : Vtx M x.length → Vtx M x.length → Bool
  | some u, w => badjB M x.length (readBit x (M.head x.length u)) (some u) w
  | none, _ => false

theorem badjT_some_some (x : List Bool) (u v : M.Conf x.length) :
    badjT M x (some u) (some v) = M.next x.length u (readBit x (M.head x.length u)) v := rfl

theorem badjT_some_none (x : List Bool) (u : M.Conf x.length) :
    badjT M x (some u) none = M.accept x.length u := rfl

theorem badjT_none (x : List Bool) (w : Vtx M x.length) : badjT M x none w = false := rfl

/-- Reachability of `some c` in the extended graph is reachability of `c` in `M`. -/
theorem reflTransGen_some (x : List Bool) (u : M.Conf x.length) :
    ∀ w : Vtx M x.length, Relation.ReflTransGen (adjOf (badjT M x)) (some u) w →
      (w = none ∧ ∃ c, Relation.ReflTransGen (M.stepRel x) u c ∧ M.accept x.length c = true) ∨
      (∃ c, w = some c ∧ Relation.ReflTransGen (M.stepRel x) u c) := by
  intro w h
  induction h with
  | refl => exact Or.inr ⟨u, rfl, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    rcases ih with ⟨rfl, -⟩ | ⟨b', rfl, hb'⟩
    · exact absurd hbc (by simp [adjOf, badjT_none])
    · cases c with
      | none =>
        exact Or.inl ⟨rfl, b', hb', by simpa [adjOf, badjT_some_none] using hbc⟩
      | some c' =>
        refine Or.inr ⟨c', rfl, hb'.tail ?_⟩
        simpa [NMachine.stepRel, adjOf, badjT_some_some] using hbc

/-- A computation of `M` lifts to a walk in the extended graph. -/
theorem reflTransGen_lift (x : List Bool) (u v : M.Conf x.length)
    (h : Relation.ReflTransGen (M.stepRel x) u v) :
    Relation.ReflTransGen (adjOf (badjT M x)) (some u) (some v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    refine ih.tail ?_
    simpa [adjOf, badjT_some_some, NMachine.stepRel] using hbc

/-- `M` accepts `x` iff the sink is reachable from the initial configuration. -/
theorem accepts_iff_reflTransGen (x : List Bool) :
    M.Accepts x ↔
      Relation.ReflTransGen (adjOf (badjT M x)) (some (M.start x.length)) none := by
  constructor
  · rintro ⟨c, hc, hacc⟩
    exact (reflTransGen_lift M x _ _ hc).tail
      (by simpa [adjOf, badjT_some_none] using hacc)
  · intro h
    rcases reflTransGen_some M x _ _ h with ⟨-, c, hc, hacc⟩ | ⟨c, hc, -⟩
    · exact ⟨c, hc, hacc⟩
    · exact absurd hc (by simp)

variable (c : ℕ) (sf : ℕ → ℕ)

/-- The recursion depth used by the simulation. -/
def savK (c : ℕ) (sf : ℕ → ℕ) (n : ℕ) : ℕ := c * sf n + c + 1

/-- The input head position of the simulating machine: it scans the position that the
configuration stored in the top frame would scan. -/
def savHead (n : ℕ) (s : SState (Vtx M n)) : ℕ :=
  match s.stack with
  | [] => 0
  | f :: _ =>
    match f.u with
    | none => 0
    | some u => M.head n u

/-- The deterministic machine given by Savitch's construction. -/
noncomputable def savMachine : DMachine where
  Conf n := {s : SState (Vtx M n) // Valid (savK c sf n) (enum M n).length s}
  finite n := instFiniteValid _ _
  head n s := savHead M n s.val
  next n s b := ⟨sstep (badjB M n b) (enum M n) s.val, valid_sstep s.property⟩
  start n := ⟨⟨[⟨savK c sf n, some (M.start n), none, 0, false⟩], none⟩, ⟨le_rfl, by simp⟩⟩
  accept n s := saccept s.val

theorem savMachine_step (x : List Bool) (s : (savMachine M c sf).Conf x.length) :
    ((savMachine M c sf).stepFun x s).val =
      sstep (badjT M x) (enum M x.length) s.val := by
  show sstep (badjB M x.length (readBit x (savHead M x.length s.val))) (enum M x.length) s.val = _
  refine sstep_congr ?_
  rintro ⟨lvl, u, v, mid, ph⟩ rest hs w
  cases u with
  | none => cases w <;> rfl
  | some u' =>
    have hhead : savHead M x.length s.val = M.head x.length u' := by
      simp [savHead, hs]
    rw [hhead]
    cases w <;> rfl

theorem savMachine_iterate (x : List Bool) (t : ℕ) :
    (((savMachine M c sf).stepFun x)^[t] ((savMachine M c sf).start x.length)).val =
      (sstep (badjT M x) (enum M x.length))^[t]
        (⟨[⟨savK c sf x.length, some (M.start x.length), none, 0, false⟩], none⟩ :
          SState (Vtx M x.length)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih,
      savMachine_step]

theorem savMachine_accept_iterate (x : List Bool) (t : ℕ) :
    (savMachine M c sf).accept x.length
        (((savMachine M c sf).stepFun x)^[t] ((savMachine M c sf).start x.length)) =
      saccept ((sstep (badjT M x) (enum M x.length))^[t]
        (⟨[⟨savK c sf x.length, some (M.start x.length), none, 0, false⟩], none⟩ :
          SState (Vtx M x.length))) := by
  show saccept _ = _
  rw [savMachine_iterate]

theorem savMachine_accepts (x : List Bool) :
    (savMachine M c sf).Accepts x ↔
      Reach (adjOf (badjT M x)) (savK c sf x.length) (some (M.start x.length)) none := by
  rw [← run_root (badj := badjT M x) (l := enum M x.length) (mem_enum M x.length)]
  simp only [DMachine.Accepts, savMachine_accept_iterate]

end Construction

/-! ### Arithmetic bounds -/

theorem two_pow_ge_succ (s : ℕ) : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self

theorem two_mul_le_sq_add_one (F : ℕ) : 2 * F ≤ F ^ 2 + 1 := by
  cases F with
  | zero => simp
  | succ m => nlinarith [Nat.zero_le (m * m)]

theorem savitch_exponent_le (c F : ℕ) :
    (4 * (c * F + c) + 7) * ((c * F + c) + 2) + 2 ≤
      (16 * c ^ 2 + 30 * c + 16) * F ^ 2 + (16 * c ^ 2 + 30 * c + 16) := by
  have h1 : 2 * F ≤ F ^ 2 + 1 := two_mul_le_sq_add_one F
  have h2 : F ≤ F ^ 2 + 1 := by omega
  nlinarith [Nat.zero_le c, Nat.zero_le F, sq_nonneg c, Nat.zero_le (c * F),
    Nat.zero_le (c ^ 2 * F), Nat.zero_le (c ^ 2 * F ^ 2)]

/-! ### The number of configurations of the simulating machine -/

theorem card_vtx_le (M : NMachine) (c : ℕ) (sf : ℕ → ℕ)
    (hcard : ∀ n, Nat.card (M.Conf n) ≤ 2 ^ (c * sf n + c)) (n : ℕ) :
    Nat.card (Vtx M n) ≤ 2 ^ (c * sf n + c + 1) := by
  haveI := M.finite n
  rw [Finite.card_option]
  have h := hcard n
  have h1 : (1 : ℕ) ≤ 2 ^ (c * sf n + c) := Nat.one_le_two_pow
  have h2 : (2 : ℕ) ^ (c * sf n + c + 1) = 2 ^ (c * sf n + c) * 2 := by ring
  omega

theorem savMachine_card_le (M : NMachine) (c : ℕ) (sf : ℕ → ℕ)
    (hcard : ∀ n, Nat.card (M.Conf n) ≤ 2 ^ (c * sf n + c)) (n : ℕ) :
    Nat.card ((savMachine M c sf).Conf n) ≤
      2 ^ ((16 * c ^ 2 + 30 * c + 16) * sf n ^ 2 + (16 * c ^ 2 + 30 * c + 16)) := by
  have hlen : (enum M n).length = Nat.card (Vtx M n) := length_enum M n
  have hNX : Nat.card (Vtx M n) ≤ 2 ^ (c * sf n + c + 1) := card_vtx_le M c sf hcard n
  set s := c * sf n + c with hs
  set NX := Nat.card (Vtx M n) with hNXdef
  have hbase : Nat.card ((savMachine M c sf).Conf n) ≤
      ((savK c sf n + 1) * NX * NX * ((enum M n).length + 1) * 2 + 1) ^ (savK c sf n + 1) * 3 :=
    card_valid_le _ _
  have hKeq : savK c sf n = s + 1 := rfl
  have hone : (1 : ℕ) ≤ 2 ^ (s + 1) := Nat.one_le_two_pow
  have a1 : savK c sf n + 1 ≤ 2 ^ (s + 1) := by
    rw [hKeq]; exact two_pow_ge_succ (s + 1)
  have a3 : NX + 1 ≤ 2 ^ (s + 2) := by
    have h2 : (2 : ℕ) ^ (s + 2) = 2 ^ (s + 1) + 2 ^ (s + 1) := by ring
    omega
  have step1 : (savK c sf n + 1) * NX * NX * ((enum M n).length + 1) * 2 + 1 ≤
      2 ^ (4 * s + 7) := by
    rw [hlen]
    have hmul : (savK c sf n + 1) * NX * NX * (NX + 1) * 2 ≤
        2 ^ (s + 1) * 2 ^ (s + 1) * 2 ^ (s + 1) * 2 ^ (s + 2) * 2 := by
      gcongr
    have heq : (2 : ℕ) ^ (s + 1) * 2 ^ (s + 1) * 2 ^ (s + 1) * 2 ^ (s + 2) * 2 =
        2 ^ (4 * s + 6) := by ring
    have hlast : (2 : ℕ) ^ (4 * s + 7) = 2 ^ (4 * s + 6) + 2 ^ (4 * s + 6) := by ring
    have hpos : (1 : ℕ) ≤ 2 ^ (4 * s + 6) := Nat.one_le_two_pow
    omega
  have step2 : ((savK c sf n + 1) * NX * NX * ((enum M n).length + 1) * 2 + 1) ^
      (savK c sf n + 1) * 3 ≤ 2 ^ ((4 * s + 7) * (s + 2) + 2) := by
    calc ((savK c sf n + 1) * NX * NX * ((enum M n).length + 1) * 2 + 1) ^ (savK c sf n + 1) * 3
        ≤ (2 ^ (4 * s + 7)) ^ (savK c sf n + 1) * 3 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left step1 _)
      _ = 2 ^ ((4 * s + 7) * (s + 2)) * 3 := by rw [hKeq, ← pow_mul]
      _ ≤ 2 ^ ((4 * s + 7) * (s + 2)) * 4 := by omega
      _ = 2 ^ ((4 * s + 7) * (s + 2) + 2) := by ring
  refine hbase.trans (step2.trans (Nat.pow_le_pow_right (by norm_num) ?_))
  simpa [hs] using savitch_exponent_le c (sf n)

/-! ### Savitch's theorem -/

/-- **Savitch's theorem**: every language decided by a nondeterministic machine in space `O(f)`
is decided by a deterministic machine in space `O(f²)`. -/
theorem savitch (f : ℕ → ℕ) : NSPACE f ⊆ DSPACE (fun n => f n ^ 2) := by
  rintro L ⟨M, c, hcard, hL⟩
  refine ⟨savMachine M c f, 16 * c ^ 2 + 30 * c + 16, ?_, ?_⟩
  · intro n
    exact savMachine_card_le M c f hcard n
  · intro x
    have hK : Nat.card (Vtx M x.length) ≤ 2 ^ savK c f x.length :=
      card_vtx_le M c f hcard x.length
    rw [hL x, accepts_iff_reflTransGen, savMachine_accepts]
    exact (reach_iff_reflTransGen hK _ _).symm

/-! ### `PSPACE = NPSPACE` -/

/-- A deterministic machine viewed as a (degenerate) nondeterministic one. -/
noncomputable def NMachine.ofDMachine (D : DMachine) : NMachine where
  Conf := D.Conf
  finite := D.finite
  head := D.head
  next n u b v := open Classical in decide (D.next n u b = v)
  start := D.start
  accept := D.accept

theorem reflTransGen_fun {α : Type} (g : α → α) (a c : α) :
    Relation.ReflTransGen (fun u v => v = g u) a c ↔ ∃ t, g^[t] a = c := by
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
    | succ t ih => exact ih.tail (by rw [Function.iterate_succ_apply'])

theorem accepts_ofDMachine (D : DMachine) (x : List Bool) :
    (NMachine.ofDMachine D).Accepts x ↔ D.Accepts x := by
  have hstep : ∀ u v : D.Conf x.length,
      (NMachine.ofDMachine D).stepRel x u v ↔ v = D.stepFun x u := by
    intro u v
    simp [NMachine.stepRel, NMachine.ofDMachine, DMachine.stepFun, eq_comm]
  constructor
  · rintro ⟨c, hc, hacc⟩
    have : Relation.ReflTransGen (fun u v : D.Conf x.length => v = D.stepFun x u)
        (D.start x.length) c := by
      refine Relation.ReflTransGen.mono ?_ hc
      intro u v h
      exact (hstep u v).1 h
    obtain ⟨t, ht⟩ := (reflTransGen_fun _ _ _).1 this
    exact ⟨t, by rw [ht]; exact hacc⟩
  · rintro ⟨t, ht⟩
    refine ⟨(D.stepFun x)^[t] (D.start x.length), ?_, ht⟩
    refine Relation.ReflTransGen.mono ?_ ((reflTransGen_fun (D.stepFun x) _ _).2 ⟨t, rfl⟩)
    intro u v h
    exact (hstep u v).2 h

/-- Deterministic space is contained in nondeterministic space. -/
theorem dspace_subset_nspace (f : ℕ → ℕ) : DSPACE f ⊆ NSPACE f := by
  rintro L ⟨D, c, hcard, hL⟩
  exact ⟨NMachine.ofDMachine D, c, hcard, fun x => (hL x).trans (accepts_ofDMachine D x).symm⟩

/-- `PSPACE`: languages decidable in polynomial space. -/
def PSPACE : Set (List Bool → Prop) := ⋃ k : ℕ, DSPACE (fun n => n ^ k)

/-- `NPSPACE`: languages decidable nondeterministically in polynomial space. -/
def NPSPACE : Set (List Bool → Prop) := ⋃ k : ℕ, NSPACE (fun n => n ^ k)

/-- **`PSPACE = NPSPACE`**, a corollary of Savitch's theorem. -/
theorem pspace_eq_npspace : PSPACE = NPSPACE := by
  apply Set.Subset.antisymm
  · rintro L hL
    obtain ⟨S, ⟨k, rfl⟩, hLS⟩ := hL
    exact Set.mem_iUnion.2 ⟨k, dspace_subset_nspace _ hLS⟩
  · rintro L hL
    obtain ⟨S, ⟨k, rfl⟩, hLS⟩ := hL
    refine Set.mem_iUnion.2 ⟨2 * k, ?_⟩
    have hfun : (fun n : ℕ => (n ^ k) ^ 2) = fun n : ℕ => n ^ (2 * k) := by
      funext n; rw [← pow_mul, mul_comm]
    have := savitch (fun n : ℕ => n ^ k) hLS
    rwa [hfun] at this

/-! ### A non-vacuity check

The space classes are not empty and the machines really do read their input: the language of
words whose first symbol is `1` is decided in constant space (and hence, by
`dspace_subset_nspace`, also nondeterministically).
-/

/-- A three-state machine that accepts iff the first input symbol is `1`: it starts in the
state `none`, and on its first step it stores the scanned symbol. -/
def firstBitMachine : DMachine where
  Conf _ := Option Bool
  finite _ := inferInstance
  head _ _ := 0
  next _ q b := some (q.getD b)
  start _ := none
  accept _ q := q == some true

theorem firstBit_mem_dspace :
    (fun x : List Bool => readBit x 0 = true) ∈ DSPACE (fun _ => 0) := by
  refine ⟨firstBitMachine, 2, fun n => ?_, fun x => ?_⟩
  · simp [firstBitMachine, Nat.card_eq_fintype_card]
  · have hstep : ∀ q : Option Bool, firstBitMachine.stepFun x q = some (q.getD (readBit x 0)) :=
      fun _ => rfl
    constructor
    · intro hx
      refine ⟨1, ?_⟩
      rw [Function.iterate_one]
      simp [DMachine.stepFun, firstBitMachine, hx]
    · rintro ⟨t, ht⟩
      by_contra hx
      have hx' : readBit x 0 = false := by
        cases h : readBit x 0 with
        | false => rfl
        | true => exact absurd h hx
      have key : ∀ t : ℕ,
          ((firstBitMachine.stepFun x)^[t] (firstBitMachine.start x.length) : Option Bool) = none ∨
          ((firstBitMachine.stepFun x)^[t] (firstBitMachine.start x.length) : Option Bool) =
            some false := by
        intro t
        induction t with
        | zero => exact Or.inl rfl
        | succ t ih =>
          rw [Function.iterate_succ_apply', hstep]
          rcases ih with h | h <;> rw [h] <;> simp [hx']
      rcases key t with h | h <;> rw [h] at ht <;> simp [firstBitMachine] at ht

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

import Mathlib

/-!
# Walks in a finite digraph and the Savitch recursion

`PathTo adj m u v` says that there is a walk with exactly `m` edges from `u` to `v`.
`Reach adj k u v` is the predicate computed by Savitch's midpoint recursion; we show it is
equivalent to the existence of a walk of length at most `2 ^ k`, and that in a finite digraph
reachability is witnessed by a walk shorter than the number of vertices.
-/

namespace CS
namespace Savitch

variable {X : Type}

/-- There is a walk with exactly `m` edges from `u` to `v`. -/
def PathTo (adj : X → X → Prop) (m : ℕ) (u v : X) : Prop :=
  ∃ g : ℕ → X, g 0 = u ∧ g m = v ∧ ∀ i < m, adj (g i) (g (i + 1))

/-- Savitch's midpoint recursion: `Reach adj k u v` holds iff `v` can be reached from `u`
by a walk of at most `2 ^ k` edges. -/
def Reach (adj : X → X → Prop) : ℕ → X → X → Prop
  | 0, u, v => u = v ∨ adj u v
  | k + 1, u, v => ∃ w, Reach adj k u w ∧ Reach adj k w v

variable {adj : X → X → Prop}

@[simp] theorem reach_zero (u v : X) : Reach adj 0 u v ↔ (u = v ∨ adj u v) := Iff.rfl

@[simp] theorem reach_succ (k : ℕ) (u v : X) :
    Reach adj (k + 1) u v ↔ ∃ w, Reach adj k u w ∧ Reach adj k w v := Iff.rfl

theorem pathTo_zero (u : X) : PathTo adj 0 u u := ⟨fun _ => u, rfl, rfl, by omega⟩

theorem pathTo_zero_iff (u v : X) : PathTo adj 0 u v ↔ u = v := by
  constructor
  · rintro ⟨g, h0, h1, -⟩; exact h0 ▸ h1 ▸ rfl
  · rintro rfl; exact pathTo_zero u

theorem pathTo_one_iff (u v : X) : PathTo adj 1 u v ↔ adj u v := by
  constructor
  · rintro ⟨g, h0, h1, hs⟩
    have := hs 0 (by omega)
    rwa [h0, h1] at this
  · intro h
    refine ⟨fun t => if t = 0 then u else v, by simp, by simp, ?_⟩
    intro i hi
    interval_cases i
    simpa using h

theorem PathTo.concat {a b : ℕ} {u w v : X} (h₁ : PathTo adj a u w) (h₂ : PathTo adj b w v) :
    PathTo adj (a + b) u v := by
  obtain ⟨g₁, g₁0, g₁a, g₁s⟩ := h₁
  obtain ⟨g₂, g₂0, g₂b, g₂s⟩ := h₂
  refine ⟨fun t => if t ≤ a then g₁ t else g₂ (t - a), ?_, ?_, ?_⟩
  · simpa using g₁0
  · by_cases hb : b = 0
    · subst hb
      simp only [add_zero, le_refl, if_true]
      rw [g₁a, ← g₂0, ← g₂b]
    · have hab : ¬ (a + b ≤ a) := by omega
      simp only [hab, if_false]
      have hsub : a + b - a = b := by omega
      rw [hsub, g₂b]
  · intro i hi
    rcases lt_trichotomy i a with h | h | h
    · have h1 : i ≤ a := by omega
      have h2 : i + 1 ≤ a := by omega
      simp only [h1, h2, if_true]
      exact g₁s i h
    · subst h
      have h2 : ¬ (i + 1 ≤ i) := by omega
      simp only [le_refl, if_true, h2, if_false]
      have hi1 : i + 1 - i = 1 := by omega
      rw [hi1, g₁a, ← g₂0]
      exact g₂s 0 (by omega)
    · have h1 : ¬ (i ≤ a) := by omega
      have h2 : ¬ (i + 1 ≤ a) := by omega
      simp only [h1, h2, if_false]
      have hsub : i + 1 - a = (i - a) + 1 := by omega
      rw [hsub]
      exact g₂s (i - a) (by omega)

theorem pathTo_prefix {g : ℕ → X} {m : ℕ} (hs : ∀ i < m, adj (g i) (g (i + 1))) {i : ℕ}
    (hi : i ≤ m) : PathTo adj i (g 0) (g i) :=
  ⟨g, rfl, rfl, fun j hj => hs j (by omega)⟩

theorem pathTo_suffix {g : ℕ → X} {m : ℕ} (hs : ∀ i < m, adj (g i) (g (i + 1))) {i : ℕ}
    (hi : i ≤ m) : PathTo adj (m - i) (g i) (g m) := by
  refine ⟨fun t => g (t + i), by simp, ?_, ?_⟩
  · have h : m - i + i = m := by omega
    simp only [h]
  · intro j hj
    have h : j + 1 + i = j + i + 1 := by omega
    simp only [h]
    exact hs (j + i) (by omega)

/-- A walk can be split at any intermediate point. -/
theorem PathTo.split {m : ℕ} {u v : X} (h : PathTo adj m u v) {i : ℕ} (hi : i ≤ m) :
    ∃ w, PathTo adj i u w ∧ PathTo adj (m - i) w v := by
  obtain ⟨g, h0, hm, hs⟩ := h
  subst h0; subst hm
  exact ⟨g i, pathTo_prefix hs hi, pathTo_suffix hs hi⟩

theorem reach_iff_exists_pathTo (k : ℕ) (u v : X) :
    Reach adj k u v ↔ ∃ m ≤ 2 ^ k, PathTo adj m u v := by
  induction k generalizing u v with
  | zero =>
    simp only [reach_zero, pow_zero]
    constructor
    · rintro (rfl | h)
      · exact ⟨0, by omega, pathTo_zero u⟩
      · exact ⟨1, by omega, (pathTo_one_iff u v).2 h⟩
    · rintro ⟨m, hm, hp⟩
      interval_cases m
      · exact Or.inl ((pathTo_zero_iff u v).1 hp)
      · exact Or.inr ((pathTo_one_iff u v).1 hp)
  | succ k ih =>
    constructor
    · rintro ⟨w, hw1, hw2⟩
      obtain ⟨a, ha, hpa⟩ := (ih u w).1 hw1
      obtain ⟨b, hb, hpb⟩ := (ih w v).1 hw2
      refine ⟨a + b, ?_, hpa.concat hpb⟩
      have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      omega
    · rintro ⟨m, hm, hp⟩
      obtain ⟨w, hw1, hw2⟩ := hp.split (i := min m (2 ^ k)) (by omega)
      refine ⟨w, (ih u w).2 ⟨_, by omega, hw1⟩, (ih w v).2 ⟨_, ?_, hw2⟩⟩
      have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      omega

theorem reflTransGen_of_steps {g : ℕ → X} :
    ∀ (m : ℕ), (∀ i < m, adj (g i) (g (i + 1))) → Relation.ReflTransGen adj (g 0) (g m) := by
  intro m
  induction m with
  | zero => intro _; exact Relation.ReflTransGen.refl
  | succ m ih =>
    intro hs
    exact (ih fun i hi => hs i (by omega)).tail (hs m (by omega))

theorem PathTo.reflTransGen {m : ℕ} {u v : X} (h : PathTo adj m u v) :
    Relation.ReflTransGen adj u v := by
  obtain ⟨g, h0, hm, hs⟩ := h
  subst h0; subst hm
  exact reflTransGen_of_steps m hs

theorem exists_pathTo_of_reflTransGen {u v : X} (h : Relation.ReflTransGen adj u v) :
    ∃ m, PathTo adj m u v := by
  induction h with
  | refl => exact ⟨0, pathTo_zero u⟩
  | tail _ hbc ih =>
    obtain ⟨m, hm⟩ := ih
    exact ⟨m + 1, hm.concat ((pathTo_one_iff _ _).2 hbc)⟩

/-- Pigeonhole: a walk at least as long as the number of vertices can be shortened. -/
theorem exists_shorter [Finite X] {m : ℕ} {u v : X} (h : PathTo adj m u v)
    (hm : Nat.card X ≤ m) : ∃ m' < m, PathTo adj m' u v := by
  classical
  have : Fintype X := Fintype.ofFinite X
  obtain ⟨g, h0, hm', hs⟩ := h
  subst h0; subst hm'
  have hcard : Fintype.card X < Fintype.card (Fin (m + 1)) := by
    have hnc : Nat.card X = Fintype.card X := Nat.card_eq_fintype_card
    simp only [Fintype.card_fin]
    omega
  obtain ⟨i, j, hij, hgij⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (m + 1) => g i) hcard
  have hne : (i : ℕ) ≠ (j : ℕ) := fun hc => hij (Fin.ext hc)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨(i : ℕ) + (m - (j : ℕ)), by omega, ?_⟩
    have hpi : PathTo adj (i : ℕ) (g 0) (g i) := pathTo_prefix hs (by omega)
    have hpj : PathTo adj (m - (j : ℕ)) (g j) (g m) := pathTo_suffix hs (by omega)
    rw [← hgij] at hpj
    exact hpi.concat hpj
  · refine ⟨(j : ℕ) + (m - (i : ℕ)), by omega, ?_⟩
    have hpj : PathTo adj (j : ℕ) (g 0) (g j) := pathTo_prefix hs (by omega)
    have hpi : PathTo adj (m - (i : ℕ)) (g i) (g m) := pathTo_suffix hs (by omega)
    rw [hgij] at hpi
    exact hpj.concat hpi

/-- In a finite digraph, reachability is witnessed by a walk with fewer edges than there are
vertices. -/
theorem exists_short_pathTo [Finite X] {u v : X} (h : Relation.ReflTransGen adj u v) :
    ∃ m < Nat.card X, PathTo adj m u v := by
  obtain ⟨m, hm⟩ := exists_pathTo_of_reflTransGen h
  induction m using Nat.strong_induction_on generalizing v with
  | _ m ih =>
    by_cases hlt : m < Nat.card X
    · exact ⟨m, hlt, hm⟩
    · obtain ⟨m', hm', hp'⟩ := exists_shorter hm (by omega)
      exact ih m' hm' (hp'.reflTransGen) hp'

/-- The key consequence: if `2 ^ k` is at least the number of vertices, Savitch's recursion at
depth `k` decides reachability. -/
theorem reach_iff_reflTransGen [Finite X] {k : ℕ} (hk : Nat.card X ≤ 2 ^ k) (u v : X) :
    Reach adj k u v ↔ Relation.ReflTransGen adj u v := by
  constructor
  · intro h
    obtain ⟨m, _, hp⟩ := (reach_iff_exists_pathTo k u v).1 h
    exact hp.reflTransGen
  · intro h
    obtain ⟨m, hm, hp⟩ := exists_short_pathTo h
    exact (reach_iff_exists_pathTo k u v).2 ⟨m, by omega, hp⟩

end Savitch
end CS

import Mathlib

/-!
# A space-bounded machine model

We use the standard "configuration graph" presentation of space bounded computation.

A machine is given, for every input length `n`, by a *finite* set of configurations `Conf n`.
The machine reads its input only through an input head: the position of the head is a function
of the current configuration, and the transition function/relation may depend on the input only
through the symbol currently scanned.  The *space* used by the machine on inputs of length `n`
is (up to a constant factor) `log₂ (Nat.card (Conf n))`, which is how the space classes below
are defined: a machine runs in space `O(s)` if it has at most `2 ^ (c * s n + c)` configurations.

This is the usual abstraction of space-bounded computation by its configuration graph; it is
non-uniform (the configuration graph may depend on `n` in an arbitrary way), which is the
standard setting in which Savitch's argument is a purely graph-theoretic statement about
reachability.
-/

namespace CS

/-- `readBit x i` is the `i`-th symbol of the input word `x`; positions past the end read `false`
(the blank symbol). -/
def readBit (x : List Bool) (i : ℕ) : Bool := x[i]?.getD false

/-- A nondeterministic space-bounded machine, presented by its configuration graph. -/
structure NMachine where
  /-- The set of configurations available on inputs of length `n`. -/
  Conf : ℕ → Type
  /-- There are only finitely many configurations. -/
  finite : ∀ n, Finite (Conf n)
  /-- Position of the input head in a given configuration. -/
  head : ∀ n, Conf n → ℕ
  /-- `next n u b v` says that `v` is a possible successor of `u` when the scanned input symbol
  is `b`. -/
  next : ∀ n, Conf n → Bool → Conf n → Bool
  /-- The initial configuration. -/
  start : ∀ n, Conf n
  /-- The accepting configurations. -/
  accept : ∀ n, Conf n → Bool

/-- The one-step relation of a nondeterministic machine on a fixed input. -/
def NMachine.stepRel (M : NMachine) (x : List Bool) (u v : M.Conf x.length) : Prop :=
  M.next x.length u (readBit x (M.head x.length u)) v = true

/-- A nondeterministic machine accepts `x` if some accepting configuration is reachable from the
initial configuration. -/
def NMachine.Accepts (M : NMachine) (x : List Bool) : Prop :=
  ∃ c, Relation.ReflTransGen (M.stepRel x) (M.start x.length) c ∧ M.accept x.length c = true

/-- A deterministic space-bounded machine, presented by its configuration graph. -/
structure DMachine where
  /-- The set of configurations available on inputs of length `n`. -/
  Conf : ℕ → Type
  /-- There are only finitely many configurations. -/
  finite : ∀ n, Finite (Conf n)
  /-- Position of the input head in a given configuration. -/
  head : ∀ n, Conf n → ℕ
  /-- The (deterministic) transition function, depending on the scanned input symbol. -/
  next : ∀ n, Conf n → Bool → Conf n
  /-- The initial configuration. -/
  start : ∀ n, Conf n
  /-- The accepting configurations. -/
  accept : ∀ n, Conf n → Bool

/-- The one-step function of a deterministic machine on a fixed input. -/
def DMachine.stepFun (M : DMachine) (x : List Bool) (c : M.Conf x.length) : M.Conf x.length :=
  M.next x.length c (readBit x (M.head x.length c))

/-- A deterministic machine accepts `x` if its (unique) run reaches an accepting configuration. -/
def DMachine.Accepts (M : DMachine) (x : List Bool) : Prop :=
  ∃ t, M.accept x.length ((M.stepFun x)^[t] (M.start x.length)) = true

/-- `NSPACE f` : languages decided by a nondeterministic machine using space `O(f)`, i.e. having
at most `2 ^ (c * f n + c)` configurations on inputs of length `n`. -/
def NSPACE (f : ℕ → ℕ) : Set (List Bool → Prop) :=
  { L | ∃ (M : NMachine) (c : ℕ),
      (∀ n, Nat.card (M.Conf n) ≤ 2 ^ (c * f n + c)) ∧ ∀ x, L x ↔ M.Accepts x }

/-- `DSPACE f` : languages decided by a deterministic machine using space `O(f)`, i.e. having
at most `2 ^ (c * f n + c)` configurations on inputs of length `n`. -/
def DSPACE (f : ℕ → ℕ) : Set (List Bool → Prop) :=
  { L | ∃ (M : DMachine) (c : ℕ),
      (∀ n, Nat.card (M.Conf n) ≤ 2 ^ (c * f n + c)) ∧ ∀ x, L x ↔ M.Accepts x }

end CS

import RequestProject.Savitch.Paths

/-!
# The Savitch stack machine

We implement Savitch's midpoint recursion as a deterministic machine whose configuration is an
explicit call stack of bounded depth.  Each stack frame stores a level `lvl`, the two endpoints
`u`, `v` of the sub-query, the index `mid` of the midpoint currently being tried, and a `phase`
bit saying which of the two recursive halves is being examined.

The point of the construction is that a stack of depth `k + 1` of frames, each of which stores a
constant number of vertices and indices, has only `2 ^ O(k · log N)` states, whereas the
underlying digraph on `N` vertices may be traversed nondeterministically only.
-/

namespace CS
namespace Savitch

variable {X : Type}

/-- A frame of the recursion stack: "is there a walk of at most `2 ^ lvl` edges from `u` to
`v`?", currently trying the midpoint with index `mid`; `phase = false` means the first half
`u ⟶ mid` is being checked, `phase = true` means the first half succeeded and the second half
`mid ⟶ v` is being checked. -/
structure Frame (X : Type) where
  /-- The recursion level: the query is about walks of length at most `2 ^ lvl`. -/
  lvl : ℕ
  /-- Source of the query. -/
  u : X
  /-- Target of the query. -/
  v : X
  /-- Index of the midpoint currently being tried. -/
  mid : ℕ
  /-- Which half of the query is being checked. -/
  phase : Bool

/-- A configuration of the stack machine: a call stack together with an optional value being
returned by the call that just finished. -/
structure SState (X : Type) where
  /-- The call stack, innermost (currently executing) frame first. -/
  stack : List (Frame X)
  /-- `none`: start executing the top frame; `some b`: the last call returned `b`. -/
  ret : Option Bool

variable [DecidableEq X]

/-- One step of the stack machine.  `badj` is the adjacency test (it is only consulted at level
`0` frames) and `l` enumerates the vertices. -/
def sstep (badj : X → X → Bool) (l : List X) (s : SState X) : SState X :=
  match s.stack, s.ret with
  | [], r => ⟨[], r⟩
  | f :: rest, none =>
    match f.lvl with
    | 0 => ⟨rest, some (decide (f.u = f.v) || badj f.u f.v)⟩
    | k + 1 =>
      match l[f.mid]? with
      | none => ⟨rest, some false⟩
      | some m =>
        if f.phase then ⟨⟨k, m, f.v, 0, false⟩ :: f :: rest, none⟩
        else ⟨⟨k, f.u, m, 0, false⟩ :: f :: rest, none⟩
  | f :: rest, some r =>
    if f.phase then
      (if r then ⟨rest, some true⟩
       else ⟨⟨f.lvl, f.u, f.v, min (f.mid + 1) l.length, false⟩ :: rest, none⟩)
    else
      (if r then ⟨⟨f.lvl, f.u, f.v, f.mid, true⟩ :: rest, none⟩
       else ⟨⟨f.lvl, f.u, f.v, min (f.mid + 1) l.length, false⟩ :: rest, none⟩)

variable {badj : X → X → Bool} {l : List X}

@[simp] theorem sstep_nil (r : Option Bool) : sstep badj l ⟨[], r⟩ = ⟨[], r⟩ := rfl

@[simp] theorem sstep_base (u v : X) (mid : ℕ) (ph : Bool) (rest : List (Frame X)) :
    sstep badj l ⟨⟨0, u, v, mid, ph⟩ :: rest, none⟩ =
      ⟨rest, some (decide (u = v) || badj u v)⟩ := rfl

theorem sstep_call_none {k : ℕ} {u v : X} {mid : ℕ} {ph : Bool} {rest : List (Frame X)}
    (h : l[mid]? = none) :
    sstep badj l ⟨⟨k + 1, u, v, mid, ph⟩ :: rest, none⟩ = ⟨rest, some false⟩ := by
  simp [sstep, h]

theorem sstep_call_some_false {k : ℕ} {u v m : X} {mid : ℕ} {rest : List (Frame X)}
    (h : l[mid]? = some m) :
    sstep badj l ⟨⟨k + 1, u, v, mid, false⟩ :: rest, none⟩ =
      ⟨⟨k, u, m, 0, false⟩ :: ⟨k + 1, u, v, mid, false⟩ :: rest, none⟩ := by
  simp [sstep, h]

theorem sstep_call_some_true {k : ℕ} {u v m : X} {mid : ℕ} {rest : List (Frame X)}
    (h : l[mid]? = some m) :
    sstep badj l ⟨⟨k + 1, u, v, mid, true⟩ :: rest, none⟩ =
      ⟨⟨k, m, v, 0, false⟩ :: ⟨k + 1, u, v, mid, true⟩ :: rest, none⟩ := by
  simp [sstep, h]

@[simp] theorem sstep_ret_false_false {lvl : ℕ} {u v : X} {mid : ℕ} {rest : List (Frame X)} :
    sstep badj l ⟨⟨lvl, u, v, mid, false⟩ :: rest, some false⟩ =
      ⟨⟨lvl, u, v, min (mid + 1) l.length, false⟩ :: rest, none⟩ := by
  simp [sstep]

@[simp] theorem sstep_ret_false_true {lvl : ℕ} {u v : X} {mid : ℕ} {rest : List (Frame X)} :
    sstep badj l ⟨⟨lvl, u, v, mid, false⟩ :: rest, some true⟩ =
      ⟨⟨lvl, u, v, mid, true⟩ :: rest, none⟩ := by
  simp [sstep]

@[simp] theorem sstep_ret_true_false {lvl : ℕ} {u v : X} {mid : ℕ} {rest : List (Frame X)} :
    sstep badj l ⟨⟨lvl, u, v, mid, true⟩ :: rest, some false⟩ =
      ⟨⟨lvl, u, v, min (mid + 1) l.length, false⟩ :: rest, none⟩ := by
  simp [sstep]

@[simp] theorem sstep_ret_true_true {lvl : ℕ} {u v : X} {mid : ℕ} {rest : List (Frame X)} :
    sstep badj l ⟨⟨lvl, u, v, mid, true⟩ :: rest, some true⟩ = ⟨rest, some true⟩ := by
  simp [sstep]

/-- Two adjacency tests that agree on the pairs actually inspected give the same step. -/
theorem sstep_congr {b1 b2 : X → X → Bool} {s : SState X}
    (h : ∀ f rest, s.stack = f :: rest → ∀ w, b1 f.u w = b2 f.u w) :
    sstep b1 l s = sstep b2 l s := by
  obtain ⟨stack, ret⟩ := s
  cases stack with
  | nil => rfl
  | cons f rest =>
    obtain ⟨lvl, u, v, mid, ph⟩ := f
    cases ret with
    | none =>
      cases lvl with
      | zero =>
        rw [sstep_base, sstep_base, h ⟨0, u, v, mid, ph⟩ rest rfl v]
      | succ k =>
        cases hmid : l[mid]? with
        | none => rw [sstep_call_none hmid, sstep_call_none hmid]
        | some m =>
          cases ph with
          | false => rw [sstep_call_some_false hmid, sstep_call_some_false hmid]
          | true => rw [sstep_call_some_true hmid, sstep_call_some_true hmid]
    | some r =>
      cases ph <;> cases r <;> simp

/-- The adjacency relation determined by the Boolean adjacency test. -/
def adjOf (badj : X → X → Bool) (u v : X) : Prop := badj u v = true

/-- The value that a frame ought to return. -/
def fval (badj : X → X → Bool) (l : List X) : Frame X → Prop
  | ⟨0, u, v, _, _⟩ => u = v ∨ badj u v = true
  | ⟨k + 1, u, v, mid, false⟩ =>
      ∃ j, mid ≤ j ∧ ∃ m, l[j]? = some m ∧
        Reach (adjOf badj) k u m ∧ Reach (adjOf badj) k m v
  | ⟨k + 1, u, v, mid, true⟩ =>
      (∃ m, l[mid]? = some m ∧ Reach (adjOf badj) k m v) ∨
      (∃ j, mid < j ∧ ∃ m, l[j]? = some m ∧
        Reach (adjOf badj) k u m ∧ Reach (adjOf badj) k m v)

omit [DecidableEq X] in
theorem fval_fresh (hl : ∀ x : X, x ∈ l) (k : ℕ) (u v : X) :
    fval badj l ⟨k, u, v, 0, false⟩ ↔ Reach (adjOf badj) k u v := by
  cases k with
  | zero => simp [fval, Reach, adjOf]
  | succ k =>
    simp only [fval, reach_succ]
    constructor
    · rintro ⟨j, -, m, -, h1, h2⟩
      exact ⟨m, h1, h2⟩
    · rintro ⟨m, h1, h2⟩
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 (hl m)
      exact ⟨j, Nat.zero_le _, m, hj, h1, h2⟩

omit [DecidableEq X] in
theorem iterate_trans {f : SState X → SState X} {a b : ℕ} {s₁ s₂ s₃ : SState X}
    (h₁ : f^[a] s₁ = s₂) (h₂ : f^[b] s₂ = s₃) : f^[b + a] s₁ = s₃ := by
  rw [Function.iterate_add_apply, h₁, h₂]

/-- **Correctness of the stack machine**: executing the top frame of the stack returns the value
that frame is supposed to compute, leaving the rest of the stack untouched. -/
theorem run_frame (hl : ∀ x : X, x ∈ l) :
    ∀ (k : ℕ) (f : Frame X), f.lvl = k → ∀ rest : List (Frame X),
      ∃ t b, (sstep badj l)^[t] ⟨f :: rest, none⟩ = ⟨rest, some b⟩ ∧
        (b = true ↔ fval badj l f) := by
  intro k
  induction k with
  | zero =>
    intro f hf rest
    obtain ⟨lvl, u, v, mid, ph⟩ := f
    simp only at hf
    subst hf
    refine ⟨1, decide (u = v) || badj u v, ?_, ?_⟩
    · simp
    · simp [fval]
  | succ k ih =>
    have inner : ∀ (M : ℕ) (u v : X) (mid : ℕ) (ph : Bool),
        2 * (l.length + 1 - mid) + (if ph then 1 else 2) ≤ M → ∀ rest : List (Frame X),
        ∃ t b, (sstep badj l)^[t] ⟨⟨k + 1, u, v, mid, ph⟩ :: rest, none⟩ = ⟨rest, some b⟩ ∧
          (b = true ↔ fval badj l ⟨k + 1, u, v, mid, ph⟩) := by
      intro M
      induction M with
      | zero =>
        intro u v mid ph hm rest
        exfalso
        cases ph <;> simp at hm
      | succ M ihM =>
        intro u v mid ph hm rest
        cases hmid : l[mid]? with
        | none =>
          have hlen : l.length ≤ mid := List.getElem?_eq_none_iff.1 hmid
          refine ⟨1, false, by simpa using sstep_call_none (badj := badj) hmid, ?_⟩
          simp only [Bool.false_eq_true, false_iff]
          cases ph with
          | false =>
            rintro ⟨j, hj, m, hjm, -, -⟩
            rw [List.getElem?_eq_none_iff.2 (by omega : l.length ≤ j)] at hjm
            simp at hjm
          | true =>
            rintro (⟨m, hjm, -⟩ | ⟨j, hj, m, hjm, -, -⟩)
            · rw [hmid] at hjm; simp at hjm
            · rw [List.getElem?_eq_none_iff.2 (by omega : l.length ≤ j)] at hjm
              simp at hjm
        | some m =>
          have hmidlt : mid < l.length := by
            by_contra hc
            rw [List.getElem?_eq_none_iff.2 (by omega : l.length ≤ mid)] at hmid
            simp at hmid
          cases ph with
          | false =>
            obtain ⟨t₁, b₁, ht₁, hb₁⟩ := ih ⟨k, u, m, 0, false⟩ rfl
              (⟨k + 1, u, v, mid, false⟩ :: rest)
            have hchild : (b₁ = true) ↔ Reach (adjOf badj) k u m := by
              rw [hb₁]; exact fval_fresh hl k u m
            have e1 : (sstep badj l)^[1] (⟨⟨k + 1, u, v, mid, false⟩ :: rest, none⟩ : SState X) =
                ⟨⟨k, u, m, 0, false⟩ :: ⟨k + 1, u, v, mid, false⟩ :: rest, none⟩ := by
              simpa using sstep_call_some_false hmid
            have e12 := iterate_trans e1 ht₁
            cases hb : b₁ with
            | true =>
              rw [hb] at e12
              have hReach : Reach (adjOf badj) k u m := hchild.1 hb
              have e3 : (sstep badj l)^[1]
                  (⟨⟨k + 1, u, v, mid, false⟩ :: rest, some true⟩ : SState X) =
                  ⟨⟨k + 1, u, v, mid, true⟩ :: rest, none⟩ := by simp
              obtain ⟨t₂, b₂, ht₂, hb₂⟩ := ihM u v mid true (by simp at hm ⊢; omega) rest
              refine ⟨t₂ + (1 + (t₁ + 1)), b₂,
                iterate_trans (iterate_trans e12 e3) ht₂, ?_⟩
              have hiff : fval badj l (⟨k + 1, u, v, mid, true⟩ : Frame X) ↔
                  fval badj l (⟨k + 1, u, v, mid, false⟩ : Frame X) := by
                simp only [fval]
                constructor
                · rintro (⟨m', hm', hr⟩ | ⟨j, hj, m', hjm', h1, h2⟩)
                  · rw [hmid] at hm'
                    obtain rfl := Option.some.inj hm'
                    exact ⟨mid, le_rfl, m, hmid, hReach, hr⟩
                  · exact ⟨j, by omega, m', hjm', h1, h2⟩
                · rintro ⟨j, hj, m', hjm', h1, h2⟩
                  rcases eq_or_lt_of_le hj with rfl | hlt
                  · rw [hmid] at hjm'
                    obtain rfl := Option.some.inj hjm'
                    exact Or.inl ⟨m, hmid, h2⟩
                  · exact Or.inr ⟨j, hlt, m', hjm', h1, h2⟩
              rw [hb₂, hiff]
            | false =>
              rw [hb] at e12
              have hnr : ¬ Reach (adjOf badj) k u m := by
                intro hc; simpa [hb] using hchild.2 hc
              have e3 : (sstep badj l)^[1]
                  (⟨⟨k + 1, u, v, mid, false⟩ :: rest, some false⟩ : SState X) =
                  ⟨⟨k + 1, u, v, mid + 1, false⟩ :: rest, none⟩ := by
                simp [Nat.min_eq_left (show mid + 1 ≤ l.length by omega)]
              obtain ⟨t₂, b₂, ht₂, hb₂⟩ := ihM u v (mid + 1) false (by simp at hm ⊢; omega) rest
              refine ⟨t₂ + (1 + (t₁ + 1)), b₂,
                iterate_trans (iterate_trans e12 e3) ht₂, ?_⟩
              have hiff : fval badj l (⟨k + 1, u, v, mid + 1, false⟩ : Frame X) ↔
                  fval badj l (⟨k + 1, u, v, mid, false⟩ : Frame X) := by
                simp only [fval]
                constructor
                · rintro ⟨j, hj, m', hjm', h1, h2⟩
                  exact ⟨j, by omega, m', hjm', h1, h2⟩
                · rintro ⟨j, hj, m', hjm', h1, h2⟩
                  rcases eq_or_lt_of_le hj with rfl | hlt
                  · rw [hmid] at hjm'
                    obtain rfl := Option.some.inj hjm'
                    exact absurd h1 hnr
                  · exact ⟨j, by omega, m', hjm', h1, h2⟩
              rw [hb₂, hiff]
          | true =>
            obtain ⟨t₁, b₁, ht₁, hb₁⟩ := ih ⟨k, m, v, 0, false⟩ rfl
              (⟨k + 1, u, v, mid, true⟩ :: rest)
            have hchild : (b₁ = true) ↔ Reach (adjOf badj) k m v := by
              rw [hb₁]; exact fval_fresh hl k m v
            have e1 : (sstep badj l)^[1] (⟨⟨k + 1, u, v, mid, true⟩ :: rest, none⟩ : SState X) =
                ⟨⟨k, m, v, 0, false⟩ :: ⟨k + 1, u, v, mid, true⟩ :: rest, none⟩ := by
              simpa using sstep_call_some_true hmid
            have e12 := iterate_trans e1 ht₁
            cases hb : b₁ with
            | true =>
              rw [hb] at e12
              have hReach : Reach (adjOf badj) k m v := hchild.1 hb
              have e3 : (sstep badj l)^[1]
                  (⟨⟨k + 1, u, v, mid, true⟩ :: rest, some true⟩ : SState X) =
                  ⟨rest, some true⟩ := by simp
              refine ⟨1 + (t₁ + 1), true, iterate_trans e12 e3, ?_⟩
              simp only [true_iff]
              exact Or.inl ⟨m, hmid, hReach⟩
            | false =>
              rw [hb] at e12
              have hnr : ¬ Reach (adjOf badj) k m v := by
                intro hc; simpa [hb] using hchild.2 hc
              have e3 : (sstep badj l)^[1]
                  (⟨⟨k + 1, u, v, mid, true⟩ :: rest, some false⟩ : SState X) =
                  ⟨⟨k + 1, u, v, mid + 1, false⟩ :: rest, none⟩ := by
                simp [Nat.min_eq_left (show mid + 1 ≤ l.length by omega)]
              obtain ⟨t₂, b₂, ht₂, hb₂⟩ := ihM u v (mid + 1) false (by simp at hm ⊢; omega) rest
              refine ⟨t₂ + (1 + (t₁ + 1)), b₂,
                iterate_trans (iterate_trans e12 e3) ht₂, ?_⟩
              have hiff : fval badj l (⟨k + 1, u, v, mid + 1, false⟩ : Frame X) ↔
                  fval badj l (⟨k + 1, u, v, mid, true⟩ : Frame X) := by
                simp only [fval]
                constructor
                · rintro ⟨j, hj, m', hjm', h1, h2⟩
                  exact Or.inr ⟨j, by omega, m', hjm', h1, h2⟩
                · rintro (⟨m', hm', hr⟩ | ⟨j, hj, m', hjm', h1, h2⟩)
                  · rw [hmid] at hm'
                    obtain rfl := Option.some.inj hm'
                    exact absurd hr hnr
                  · exact ⟨j, by omega, m', hjm', h1, h2⟩
              rw [hb₂, hiff]
    intro f hf rest
    obtain ⟨lvl, u, v, mid, ph⟩ := f
    simp only at hf
    subst hf
    exact inner _ u v mid ph le_rfl rest

/-- Accepting configurations of the stack machine: the stack is empty and the value returned is
`true`. -/
def saccept (s : SState X) : Bool := s.stack.isEmpty && (s.ret == some true)

omit [DecidableEq X] in
theorem eq_of_saccept {s : SState X} (h : saccept s = true) : s = ⟨[], some true⟩ := by
  obtain ⟨st, rt⟩ := s
  simp only [saccept, List.isEmpty_iff, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  subst h1; subst h2; rfl

theorem sstep_iterate_nil (r : Option Bool) (t : ℕ) :
    (sstep badj l)^[t] ⟨[], r⟩ = ⟨[], r⟩ := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply, sstep_nil, ih]

/-- **The stack machine decides `Reach`**: started with a single frame asking whether `v` is
reachable from `u` by a walk of length at most `2 ^ K`, the machine accepts iff it is. -/
theorem run_root (hl : ∀ x : X, x ∈ l) (K : ℕ) (u v : X) :
    (∃ t, saccept ((sstep badj l)^[t] ⟨[⟨K, u, v, 0, false⟩], none⟩) = true) ↔
      Reach (adjOf badj) K u v := by
  obtain ⟨t₀, b, ht₀, hb⟩ := run_frame hl K ⟨K, u, v, 0, false⟩ rfl []
  rw [fval_fresh hl] at hb
  constructor
  · rintro ⟨t, ht⟩
    have hstate : (sstep badj l)^[t] ⟨[⟨K, u, v, 0, false⟩], none⟩ = ⟨[], some true⟩ :=
      eq_of_saccept ht
    have h1 : (sstep badj l)^[max t t₀] (⟨[⟨K, u, v, 0, false⟩], none⟩ : SState X) =
        ⟨[], some true⟩ := by
      rw [show max t t₀ = (max t t₀ - t) + t by omega, Function.iterate_add_apply, hstate,
        sstep_iterate_nil]
    have h2 : (sstep badj l)^[max t t₀] (⟨[⟨K, u, v, 0, false⟩], none⟩ : SState X) =
        ⟨[], some b⟩ := by
      rw [show max t t₀ = (max t t₀ - t₀) + t₀ by omega, Function.iterate_add_apply, ht₀,
        sstep_iterate_nil]
    rw [h1] at h2
    have hbt : b = true := (Option.some.inj (congrArg SState.ret h2)).symm
    exact hb.1 hbt
  · intro h
    refine ⟨t₀, ?_⟩
    rw [ht₀]
    simp [saccept, hb.2 h]

/-! ### Bounding the number of configurations -/

/-- The levels of the frames on the stack increase by exactly one from the top to the bottom of
the stack, and the bottom frame has level at most `K`. -/
def LevelsOK (K : ℕ) : List (Frame X) → Prop
  | [] => True
  | [f] => f.lvl ≤ K
  | f :: g :: t => f.lvl + 1 = g.lvl ∧ LevelsOK K (g :: t)

omit [DecidableEq X] in
theorem levelsOK_le {K : ℕ} : ∀ (L : List (Frame X)), LevelsOK K L → ∀ f ∈ L, f.lvl ≤ K := by
  intro L
  induction L with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil =>
      intro h f hf
      simp only [List.mem_singleton] at hf
      subst hf
      exact h
    | cons b t' =>
      intro h f hf
      obtain ⟨h1, h2⟩ := h
      have hb := ih h2
      rcases List.mem_cons.1 hf with rfl | hf'
      · have : b.lvl ≤ K := hb b (by simp)
        omega
      · exact hb f hf'

omit [DecidableEq X] in
omit [DecidableEq X] in
omit [DecidableEq X] in
theorem levelsOK_length_add {K : ℕ} : ∀ (L : List (Frame X)) (f : Frame X),
    LevelsOK K (f :: L) → (f :: L).length + f.lvl ≤ K + 1 := by
  intro L
  induction L with
  | nil =>
    intro f h
    have hf : f.lvl ≤ K := h
    simp only [List.length_singleton]
    omega
  | cons g t ih =>
    intro f h
    obtain ⟨h1, h2⟩ := h
    have := ih g h2
    simp only [List.length_cons] at *
    omega

omit [DecidableEq X] in
omit [DecidableEq X] in
theorem levelsOK_length {K : ℕ} (L : List (Frame X)) (h : LevelsOK K L) : L.length ≤ K + 1 := by
  cases L with
  | nil => simp
  | cons f t => have := levelsOK_length_add t f h; omega

omit [DecidableEq X] in
theorem levelsOK_tail {K : ℕ} {f : Frame X} {L : List (Frame X)} (h : LevelsOK K (f :: L)) :
    LevelsOK K L := by
  cases L with
  | nil => trivial
  | cons g t => exact h.2

omit [DecidableEq X] in
theorem levelsOK_head_mod {K : ℕ} {f f' : Frame X} {L : List (Frame X)}
    (h : LevelsOK K (f :: L)) (hlvl : f'.lvl = f.lvl) : LevelsOK K (f' :: L) := by
  cases L with
  | nil => simpa [LevelsOK, hlvl] using h
  | cons g t => exact ⟨by rw [hlvl]; exact h.1, h.2⟩

/-- The invariant satisfied by all configurations of the Savitch machine: the stack is a
well-formed chain of levels below `K`, and all midpoint indices are at most `N`. -/
structure Valid (K N : ℕ) (s : SState X) : Prop where
  /-- The levels along the stack are well-formed. -/
  levels : LevelsOK K s.stack
  /-- All midpoint indices are within range. -/
  mids : ∀ f ∈ s.stack, f.mid ≤ N

theorem valid_sstep {K : ℕ} {s : SState X} (h : Valid K l.length s) :
    Valid K l.length (sstep badj l s) := by
  obtain ⟨stack, ret⟩ := s
  cases stack with
  | nil => exact h
  | cons f rest =>
    obtain ⟨lvl, u, v, mid, ph⟩ := f
    have hlev : LevelsOK K (⟨lvl, u, v, mid, ph⟩ :: rest) := h.levels
    have hmids : ∀ g ∈ (⟨lvl, u, v, mid, ph⟩ :: rest : List (Frame X)), g.mid ≤ l.length := h.mids
    cases ret with
    | none =>
      cases lvl with
      | zero =>
        rw [sstep_base]
        exact ⟨levelsOK_tail hlev, fun g hg => hmids g (List.mem_cons_of_mem _ hg)⟩
      | succ k =>
        cases hmid : l[mid]? with
        | none =>
          rw [sstep_call_none hmid]
          exact ⟨levelsOK_tail hlev, fun g hg => hmids g (List.mem_cons_of_mem _ hg)⟩
        | some m =>
          cases ph with
          | false =>
            rw [sstep_call_some_false hmid]
            refine ⟨⟨rfl, hlev⟩, ?_⟩
            intro g hg
            rcases List.mem_cons.1 hg with rfl | hg'
            · simp
            · exact hmids g hg'
          | true =>
            rw [sstep_call_some_true hmid]
            refine ⟨⟨rfl, hlev⟩, ?_⟩
            intro g hg
            rcases List.mem_cons.1 hg with rfl | hg'
            · simp
            · exact hmids g hg'
    | some r =>
      cases ph with
      | false =>
        cases r with
        | false =>
          rw [sstep_ret_false_false]
          refine ⟨levelsOK_head_mod hlev rfl, ?_⟩
          intro g hg
          rcases List.mem_cons.1 hg with rfl | hg'
          · simp
          · exact hmids g (List.mem_cons_of_mem _ hg')
        | true =>
          rw [sstep_ret_false_true]
          refine ⟨levelsOK_head_mod hlev rfl, ?_⟩
          intro g hg
          rcases List.mem_cons.1 hg with rfl | hg'
          · exact hmids ⟨lvl, u, v, mid, false⟩ (by simp)
          · exact hmids g (List.mem_cons_of_mem _ hg')
      | true =>
        cases r with
        | false =>
          rw [sstep_ret_true_false]
          refine ⟨levelsOK_head_mod hlev rfl, ?_⟩
          intro g hg
          rcases List.mem_cons.1 hg with rfl | hg'
          · simp
          · exact hmids g (List.mem_cons_of_mem _ hg')
        | true =>
          rw [sstep_ret_true_true]
          exact ⟨levelsOK_tail hlev, fun g hg => hmids g (List.mem_cons_of_mem _ hg)⟩

/-- Encoding of a valid configuration by a bounded array of bounded frames; used only to count
configurations. -/
def encodeValid (K N : ℕ) (s : {s : SState X // Valid K N s}) :
    (Fin (K + 1) → Option (Fin (K + 1) × X × X × Fin (N + 1) × Bool)) × Option Bool :=
  (fun i => (s.val.stack[i.val]?).map
      (fun f => (⟨min f.lvl K, by omega⟩, f.u, f.v, ⟨min f.mid N, by omega⟩, f.phase)),
    s.val.ret)

omit [DecidableEq X] in
theorem encodeValid_injective (K N : ℕ) :
    Function.Injective (encodeValid (X := X) K N) := by
  rintro ⟨⟨st1, r1⟩, hv1⟩ ⟨⟨st2, r2⟩, hv2⟩ heq
  have hr : r1 = r2 := congrArg Prod.snd heq
  have hfun := congrArg Prod.fst heq
  have hst : st1 = st2 := by
    refine List.ext_getElem? fun i => ?_
    by_cases hi : i < K + 1
    · have hi' := congrFun hfun ⟨i, hi⟩
      simp only [encodeValid] at hi'
      cases h1 : st1[i]? with
      | none =>
        cases h2 : st2[i]? with
        | none => rfl
        | some f2 =>
          rw [h1, h2] at hi'
          simp at hi'
      | some f1 =>
        cases h2 : st2[i]? with
        | none => rw [h1, h2] at hi'; simp at hi'
        | some f2 =>
          rw [h1, h2] at hi'
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq] at hi'
          obtain ⟨hlvl, hu, hv, hmid, hph⟩ := hi'
          have hb1 : f1.lvl ≤ K := levelsOK_le _ hv1.levels _ (List.mem_of_getElem? h1)
          have hb2 : f2.lvl ≤ K := levelsOK_le _ hv2.levels _ (List.mem_of_getElem? h2)
          have hm1 : f1.mid ≤ N := hv1.mids _ (List.mem_of_getElem? h1)
          have hm2 : f2.mid ≤ N := hv2.mids _ (List.mem_of_getElem? h2)
          have : f1 = f2 := by
            obtain ⟨a1, b1, c1, d1, e1⟩ := f1
            obtain ⟨a2, b2, c2, d2, e2⟩ := f2
            simp only at hlvl hu hv hmid hph hb1 hb2 hm1 hm2
            have : a1 = a2 := by omega
            have : d1 = d2 := by omega
            simp_all
          rw [this]
    · have hlen1 : st1.length ≤ K + 1 := levelsOK_length _ hv1.levels
      have hlen2 : st2.length ≤ K + 1 := levelsOK_length _ hv2.levels
      rw [List.getElem?_eq_none_iff.2 (by omega), List.getElem?_eq_none_iff.2 (by omega)]
  subst hst; subst hr; rfl

instance instFiniteValid [Finite X] (K N : ℕ) : Finite {s : SState X // Valid K N s} :=
  Finite.of_injective _ (encodeValid_injective K N)

omit [DecidableEq X] in
theorem card_valid_le [Finite X] (K N : ℕ) :
    Nat.card {s : SState X // Valid K N s} ≤
      ((K + 1) * Nat.card X * Nat.card X * (N + 1) * 2 + 1) ^ (K + 1) * 3 := by
  have h := Nat.card_le_card_of_injective _ (encodeValid_injective (X := X) K N)
  refine h.trans (le_of_eq ?_)
  rw [Nat.card_prod, Nat.card_fun, Finite.card_option, Finite.card_option]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_bool]
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_bool]
  ring

end Savitch
end CS

