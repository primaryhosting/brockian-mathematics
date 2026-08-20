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
The limit step of the transfinite construction: at a countable limit ordinal `a`
we build a nice partial injection with domain `a` coherent with all previous ones,
by an `ω`-recursion along a cofinal sequence, reserving one new value at each stage
so that the resulting function still omits infinitely many naturals.
-/
import RequestProject.Aronszajn.Step

open Ordinal Cardinal Set

namespace Aronszajn


theorem exists_cofinal_seq {a : Ordinal.{0}} (ha : a < ω₁) (ha0 : 0 < a)
    (halim : ∀ b < a, b + 1 < a) :
    ∃ seq : ℕ → Ordinal.{0}, seq 0 = 0 ∧ (∀ n, seq n < a) ∧ StrictMono seq ∧
      ∀ b < a, ∃ n, b < seq n := by
  have hc : (Set.Iio a).Countable := (lt_omega1_iff_countable a).1 ha
  have hne : (Set.Iio a).Nonempty := ⟨0, ha0⟩
  obtain ⟨s, hs⟩ := hc.exists_surjective hne
  set seq : ℕ → Ordinal.{0} := fun n => Nat.rec (0 : Ordinal.{0})
    (fun n x => max (x + 1) ((s n : Ordinal.{0}) + 1)) n with hseq
  have hlt : ∀ n, seq n < a := by
    intro n
    induction n with
    | zero => exact ha0
    | succ n ih =>
      have h1 : seq n + 1 < a := halim _ ih
      have h2 : (s n : Ordinal.{0}) + 1 < a := halim _ (s n).2
      exact max_lt h1 h2
  have hmono : StrictMono seq := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact lt_of_lt_of_le (Order.lt_add_one_iff.2 le_rfl) (le_max_left _ _)
  refine ⟨seq, rfl, hlt, hmono, ?_⟩
  intro b hb
  obtain ⟨n, hn⟩ := hs ⟨b, hb⟩
  refine ⟨n + 1, ?_⟩
  have : (s n : Ordinal.{0}) = b := by rw [hn]
  calc b < (s n : Ordinal.{0}) + 1 := by rw [this]; exact Order.lt_add_one_iff.2 le_rfl
    _ ≤ seq (n + 1) := le_max_right _ _

end Aronszajn

/-
The key "one step extension" lemma for the construction of a coherent sequence
of partial injections.
-/
import RequestProject.Aronszajn.Defs

open Ordinal Cardinal Set

namespace Aronszajn

/-- An infinite set of naturals contains the range of an injection. -/
