/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-- `Unbdd A` says that the set of naturals satisfying `A` is unbounded, i.e. infinite. -/
def Unbdd (A : Nat → Prop) : Prop := ∀ n, ∃ m, n < m ∧ A m

theorem not_unbdd {A : Nat → Prop} (h : ¬ Unbdd A) : ∃ n, ∀ m, n < m → ¬ A m :=
  Classical.byContradiction fun hcon =>
    h fun n => Classical.byContradiction fun hn => hcon ⟨n, fun m hm hAm => hn ⟨m, hm, hAm⟩⟩

/-- Infinite pigeonhole for two colours: if `A` is unbounded and `f` is a two-colouring of `Nat`,
then one of the two colour classes inside `A` is still unbounded. -/
theorem unbdd_split (A : Nat → Prop) (f : Nat → Bool) (hA : Unbdd A) :
    ∃ k : Bool, Unbdd (fun n => A n ∧ f n = k) :=
  Classical.byContradiction fun hcon => by
    obtain ⟨N1, hN1⟩ := not_unbdd (fun h => hcon ⟨true, h⟩)
    obtain ⟨N2, hN2⟩ := not_unbdd (fun h => hcon ⟨false, h⟩)
    obtain ⟨m, hm, hAm⟩ := hA (N1 + N2)
    cases hfm : f m with
    | true => exact hN1 m (by omega) ⟨hAm, hfm⟩
    | false => exact hN2 m (by omega) ⟨hAm, hfm⟩

/-- One step of the Ramsey construction, packaged as a structure: from an unbounded set `A`
we extract a point `a ∈ A`, a colour `k`, and an unbounded set `B` of points of `A` above `a`,
all joined to `a` in colour `k`. -/
structure StepData (c : Nat → Nat → Bool) (A : Nat → Prop) where
  a : Nat
  k : Bool
  B : Nat → Prop
  mem : A a
  sub : ∀ b, B b → A b ∧ a < b
  unbdd : Unbdd B
  colour : ∀ b, B b → c a b = k

theorem stepData_nonempty (c : Nat → Nat → Bool) (A : Nat → Prop) (hA : Unbdd A) :
    Nonempty (StepData c A) := by
  obtain ⟨a, -, hAa⟩ := hA 0
  have hA' : Unbdd (fun b => A b ∧ a < b) := by
    intro n
    obtain ⟨m, hm, hAm⟩ := hA (n + a)
    exact ⟨m, by omega, hAm, by omega⟩
  obtain ⟨k, hk⟩ := unbdd_split _ (fun b => c a b) hA'
  exact ⟨{ a := a
           k := k
           B := fun b => (A b ∧ a < b) ∧ c a b = k
           mem := hAa
           sub := fun b hb => hb.1
           unbdd := hk
           colour := fun b hb => hb.2 }⟩

/-- The state of the construction: an unbounded set together with a proof of unboundedness. -/
structure St (c : Nat → Nat → Bool) where
  A : Nat → Prop
  hA : Unbdd A

noncomputable def stepOf (c : Nat → Nat → Bool) (s : St c) : StepData c s.A :=
  Classical.choice (stepData_nonempty c s.A s.hA)

/-- The sequence of nested unbounded sets produced by the construction. -/
noncomputable def seq (c : Nat → Nat → Bool) : Nat → St c
  | 0 => ⟨fun _ => True, fun n => ⟨n + 1, by omega, trivial⟩⟩
  | n + 1 => ⟨(stepOf c (seq c n)).B, (stepOf c (seq c n)).unbdd⟩

/-- The `n`-th chosen point. -/
noncomputable def elt (c : Nat → Nat → Bool) (n : Nat) : Nat := (stepOf c (seq c n)).a

/-- The colour with which the `n`-th point is joined to all later chosen points. -/
noncomputable def col (c : Nat → Nat → Bool) (n : Nat) : Bool := (stepOf c (seq c n)).k

theorem seq_succ_apply (c : Nat → Nat → Bool) (n b : Nat) (hb : (seq c (n + 1)).A b) :
    (seq c n).A b ∧ elt c n < b :=
  (stepOf c (seq c n)).sub b hb

theorem seq_succ_colour (c : Nat → Nat → Bool) (n b : Nat) (hb : (seq c (n + 1)).A b) :
    c (elt c n) b = col c n :=
  (stepOf c (seq c n)).colour b hb

theorem elt_mem (c : Nat → Nat → Bool) (n : Nat) : (seq c n).A (elt c n) :=
  (stepOf c (seq c n)).mem

theorem seq_mono (c : Nat → Nat → Bool) {m n : Nat} (h : m ≤ n) {b : Nat} (hb : (seq c n).A b) :
    (seq c m).A b := by
  induction n with
  | zero => have : m = 0 := by omega
            subst this; exact hb
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact ih (by omega) (seq_succ_apply c n b hb).1
    · have : m = n + 1 := by omega
      subst this; exact hb

theorem elt_lt (c : Nat → Nat → Bool) {m n : Nat} (h : m < n) : elt c m < elt c n :=
  (seq_succ_apply c m _ (seq_mono c h (elt_mem c n))).2

theorem colour_of_lt (c : Nat → Nat → Bool) {m n : Nat} (h : m < n) :
    c (elt c m) (elt c n) = col c m :=
  seq_succ_colour c m _ (seq_mono c h (elt_mem c n))

theorem le_elt (c : Nat → Nat → Bool) (n : Nat) : n ≤ elt c n := by
  induction n with
  | zero => omega
  | succ n ih => have := elt_lt c (show n < n + 1 by omega); omega

/-- **Infinite Ramsey theorem** for pairs and two colours: every colouring `c` of the
(unordered) pairs of natural numbers with two colours admits an infinite set `S`
all of whose pairs receive the same colour `k`. -/
theorem infinite_ramsey (c : Nat → Nat → Bool) :
    ∃ (S : Nat → Prop) (k : Bool), Unbdd S ∧ ∀ a b, S a → S b → a < b → c a b = k := by
  obtain ⟨K, hK⟩ := unbdd_split (fun _ => True) (col c) (fun n => ⟨n + 1, by omega, trivial⟩)
  refine ⟨fun x => ∃ n, col c n = K ∧ x = elt c n, K, ?_, ?_⟩
  · intro n
    obtain ⟨j, hj, -, hcol⟩ := hK n
    exact ⟨elt c j, Nat.lt_of_lt_of_le hj (le_elt c j), j, hcol, rfl⟩
  · rintro x y ⟨m, hm, rfl⟩ ⟨n, hn, rfl⟩ hxy
    have hmn : m < n := by
      rcases Nat.lt_or_ge m n with h | h
      · exact h
      · exfalso
        rcases Nat.eq_or_lt_of_le h with h' | h'
        · subst h'; omega
        · have := elt_lt c h'; omega
    rw [colour_of_lt c hmn, hm]

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
# Infinite Ramsey, `Set`-valued restatement

A restatement of `Frontier.infinite_ramsey` using Mathlib's `Set.Infinite`.
-/

namespace Frontier

/-- **Infinite Ramsey theorem** for pairs and two colours, stated with `Set.Infinite`:
for every 2-colouring `c` of the unordered pairs of natural numbers (a pair `{a, b}` with
`a < b` receiving the colour `c a b`) there is an infinite set `S ⊆ ℕ` and a colour `k`
such that every pair from `S` has colour `k`. -/
theorem infinite_ramsey_set (c : ℕ → ℕ → Bool) :
    ∃ (S : Set ℕ) (k : Bool), S.Infinite ∧ ∀ a ∈ S, ∀ b ∈ S, a < b → c a b = k := by
  obtain ⟨S, k, hS, hmono⟩ := Frontier.infinite_ramsey c
  refine ⟨{n | S n}, k, Set.infinite_of_forall_exists_gt fun a => ?_, ?_⟩
  · obtain ⟨m, hm, hSm⟩ := hS a
    exact ⟨m, hSm, hm⟩
  · exact fun a ha b hb hab => hmono a b ha hb hab

end Frontier

