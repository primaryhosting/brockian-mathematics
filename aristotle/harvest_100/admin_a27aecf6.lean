/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A predicate on `Nat` is `Unbounded` when it holds arbitrarily far out; for subsets of `Nat`
this is exactly the same as being infinite. -/
def Unbounded (p : Nat → Prop) : Prop := ∀ n, ∃ m, n < m ∧ p m

theorem not_unbounded {p : Nat → Prop} (h : ¬ Unbounded p) : ∃ N, ∀ m, N < m → ¬ p m := by
  apply Classical.byContradiction
  intro hcon
  apply h
  intro n
  apply Classical.byContradiction
  intro hn
  exact hcon ⟨n, fun m hnm hq => hn ⟨m, hnm, hq⟩⟩

theorem unbounded_and_gt {p : Nat → Prop} (hp : Unbounded p) (a : Nat) :
    Unbounded (fun x => p x ∧ a < x) := by
  intro n
  obtain ⟨m, hm1, hm2⟩ := hp (max n a)
  exact ⟨m, by omega, hm2, by omega⟩

/-- Given an infinite set `p` and a point `a`, one of the two colour classes of `a` inside `p`
is again infinite. -/
theorem exists_colour_unbounded (c : Nat → Nat → Bool) {p : Nat → Prop} (hp : Unbounded p) (a : Nat) :
    ∃ b : Bool, Unbounded (fun x => p x ∧ c a x = b) := by
  by_cases h : Unbounded (fun x => p x ∧ c a x = true)
  · exact ⟨true, h⟩
  · refine ⟨false, ?_⟩
    obtain ⟨N, hN⟩ := not_unbounded h
    intro n
    obtain ⟨m, hm1, hm2⟩ := hp (max n N)
    refine ⟨m, by omega, hm2, ?_⟩
    have hmN := hN m (by omega)
    cases hb : c a m with
    | false => rfl
    | true => exact absurd ⟨hm2, hb⟩ hmN

/-- A state of the construction: an infinite set of naturals. -/
structure State (c : Nat → Nat → Bool) where
  /-- The current infinite set. -/
  p : Nat → Prop
  /-- Proof that it is infinite. -/
  hp : Unbounded p

variable {c : Nat → Nat → Bool}

/-- A distinguished point of the current set. -/
noncomputable def State.pt (s : State c) : Nat := Classical.choose (s.hp 0)

theorem State.pt_mem (s : State c) : s.p s.pt := (Classical.choose_spec (s.hp 0)).2

/-- The colour `b` such that infinitely many points of the current set see `s.pt` in colour `b`. -/
noncomputable def State.col (s : State c) : Bool :=
  Classical.choose (exists_colour_unbounded c s.hp s.pt)

theorem State.col_spec (s : State c) :
    Unbounded (fun x => s.p x ∧ c s.pt x = s.col) :=
  Classical.choose_spec (exists_colour_unbounded c s.hp s.pt)

/-- The next state: keep the points of the current set that see `s.pt` in colour `s.col`
and lie beyond `s.pt`. -/
noncomputable def State.next (s : State c) : State c :=
  ⟨fun x => (s.p x ∧ c s.pt x = s.col) ∧ s.pt < x, unbounded_and_gt s.col_spec s.pt⟩

/-- Iterating the construction. -/
noncomputable def State.iter (s : State c) : Nat → State c
  | 0 => s
  | k + 1 => (s.iter k).next

theorem State.next_p_imp (s : State c) {x : Nat} (hx : s.next.p x) : s.p x := hx.1.1

theorem State.iter_p_imp (s : State c) {i j : Nat} (hij : i ≤ j) {x : Nat}
    (hx : (s.iter j).p x) : (s.iter i).p x := by
  induction j with
  | zero =>
      have : i = 0 := Nat.le_zero.mp hij
      subst this
      exact hx
  | succ j ih =>
      by_cases h : i ≤ j
      · exact ih h ((s.iter j).next_p_imp hx)
      · have : i = j + 1 := by omega
        subst this
        exact hx

/-- The sequence of chosen points. -/
noncomputable def State.a (s : State c) (k : Nat) : Nat := (s.iter k).pt

/-- The sequence of chosen colours. -/
noncomputable def State.bcol (s : State c) (k : Nat) : Bool := (s.iter k).col

theorem State.a_lt_succ (s : State c) (k : Nat) : s.a k < s.a (k + 1) := by
  have h : (s.iter (k + 1)).p (s.a (k + 1)) := (s.iter (k + 1)).pt_mem
  exact h.2

theorem State.a_strictMono (s : State c) {i j : Nat} (hij : i < j) : s.a i < s.a j := by
  induction j with
  | zero => omega
  | succ j ih =>
      by_cases h : i < j
      · exact Nat.lt_trans (ih h) (s.a_lt_succ j)
      · have : i = j := by omega
        subst this
        exact s.a_lt_succ i

theorem State.colour_eq (s : State c) {i j : Nat} (hij : i < j) :
    c (s.a i) (s.a j) = s.bcol i := by
  have hj : (s.iter j).p (s.a j) := (s.iter j).pt_mem
  have h1 : (s.iter (i + 1)).p (s.a j) := s.iter_p_imp hij hj
  exact h1.1.2

theorem exists_constant_colour (s : State c) :
    ∃ b : Bool, Unbounded (fun k => s.bcol k = b) := by
  by_cases h : Unbounded (fun k => s.bcol k = true)
  · exact ⟨true, h⟩
  · refine ⟨false, ?_⟩
    obtain ⟨N, hN⟩ := not_unbounded h
    intro n
    refine ⟨max n N + 1, by omega, ?_⟩
    have hmN := hN (max n N + 1) (by omega)
    cases hb : s.bcol (max n N + 1) with
    | false => exact hb
    | true => exact absurd hb hmN

/-- A strictly increasing enumeration of an infinite set. -/
noncomputable def enum {p : Nat → Prop} (hp : Unbounded p) : Nat → Nat
  | 0 => Classical.choose (hp 0)
  | k + 1 => Classical.choose (hp (enum hp k))

theorem enum_spec {p : Nat → Prop} (hp : Unbounded p) (k : Nat) : p (enum hp k) := by
  cases k with
  | zero => exact (Classical.choose_spec (hp 0)).2
  | succ k => exact (Classical.choose_spec (hp (enum hp k))).2

theorem enum_lt_succ {p : Nat → Prop} (hp : Unbounded p) (k : Nat) :
    enum hp k < enum hp (k + 1) :=
  (Classical.choose_spec (hp (enum hp k))).1

theorem enum_strictMono {p : Nat → Prop} (hp : Unbounded p) {i j : Nat} (hij : i < j) :
    enum hp i < enum hp j := by
  induction j with
  | zero => omega
  | succ j ih =>
      by_cases h : i < j
      · exact Nat.lt_trans (ih h) (enum_lt_succ hp j)
      · have : i = j := by omega
        subst this
        exact enum_lt_succ hp i

/-- **Infinite Ramsey theorem** (pairs, two colours).  For every colouring
`c : Nat → Nat → Bool` of the pairs `{i, j} ⊆ Nat` (a pair `i < j` gets colour `c i j`) there is an
infinite set `S ⊆ Nat` — presented as an unbounded predicate on `Nat` — and a colour `b` such that
every pair from `S` has colour `b`. -/
theorem infinite_ramsey (c : Nat → Nat → Bool) :
    ∃ (S : Nat → Prop) (b : Bool), Unbounded S ∧ ∀ i j, S i → S j → i < j → c i j = b := by
  -- Start from all of `Nat`.
  let s : State c := ⟨fun _ => True, fun n => ⟨n + 1, by omega, trivial⟩⟩
  obtain ⟨b, hb⟩ := exists_constant_colour s
  -- Restrict to the steps whose colour is `b`.
  let g : Nat → Nat := enum hb
  let f : Nat → Nat := fun n => s.a (g n)
  have hfmono : ∀ i j, i < j → f i < f j := fun i j hij =>
    s.a_strictMono (enum_strictMono hb hij)
  have hfcol : ∀ i j, i < j → c (f i) (f j) = b := by
    intro i j hij
    have h1 : c (s.a (g i)) (s.a (g j)) = s.bcol (g i) :=
      s.colour_eq (enum_strictMono hb hij)
    have h2 : s.bcol (g i) = b := enum_spec hb i
    exact h1.trans h2
  have hfge : ∀ n, n ≤ f n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
        have := hfmono n (n + 1) (by omega)
        omega
  refine ⟨fun x => ∃ n, f n = x, b, ?_, ?_⟩
  · intro n
    exact ⟨f (n + 1), by have := hfge (n + 1); omega, ⟨n + 1, rfl⟩⟩
  · rintro i j ⟨m, rfl⟩ ⟨n, rfl⟩ hij
    have hmn : m < n := by
      by_cases h : m < n
      · exact h
      · have : n ≤ m := by omega
        by_cases h2 : n = m
        · subst h2; omega
        · have : n < m := by omega
          have := hfmono n m this
          omega
    exact hfcol m n hmn

end Frontier

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
import RequestProject.InfiniteRamsey

/-!
# Infinite Ramsey, stated with `Set.Infinite`

`RequestProject/InfiniteRamsey.lean` proves `Frontier.infinite_ramsey` in plain Lean core, where
an infinite subset of `ℕ` is presented as an unbounded predicate.  Here we record that this is
literally the Mathlib notion of an infinite subset of `ℕ`, and restate the theorem accordingly.
-/

namespace Frontier

open Set

/-- For subsets of `ℕ`, `Frontier.Unbounded` is exactly `Set.Infinite`. -/
theorem unbounded_iff_infinite (S : Set ℕ) : Unbounded (fun x => x ∈ S) ↔ S.Infinite := by
  constructor
  · intro h
    refine Set.infinite_of_forall_exists_gt fun a => ?_
    obtain ⟨m, hm, hmS⟩ := h a
    exact ⟨m, hmS, hm⟩
  · intro h a
    obtain ⟨m, hmS, hm⟩ := h.exists_gt a
    exact ⟨m, hm, hmS⟩

/-- **Infinite Ramsey theorem** (pairs, two colours), phrased with `Set.Infinite`:
every 2-colouring of `[ℕ]²` admits an infinite monochromatic set. -/
theorem infinite_ramsey_set (c : ℕ → ℕ → Bool) :
    ∃ (S : Set ℕ) (b : Bool), S.Infinite ∧ ∀ i ∈ S, ∀ j ∈ S, i < j → c i j = b := by
  obtain ⟨S, b, hS, hcol⟩ := infinite_ramsey c
  refine ⟨{x | S x}, b, (unbounded_iff_infinite {x | S x}).mp hS, ?_⟩
  intro i hi j hj hij
  exact hcol i j hi hj hij

end Frontier

