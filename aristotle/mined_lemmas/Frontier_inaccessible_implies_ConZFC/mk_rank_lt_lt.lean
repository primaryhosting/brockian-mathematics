/-
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
This file formalizes the statement that a (strongly) inaccessible cardinal `κ` yields a model of
`ZFC`, namely the rank-initial segment `V κ = {x : ZFSet | rank x < κ.ord}` of the von Neumann
hierarchy, and deduces the semantic consistency statement `Con(ZFC)` (i.e. satisfiability of the
first-order theory `ZFCTheory`) from the existence of an inaccessible cardinal.
-/

universe u

namespace Frontier

open FirstOrder Language Cardinal Ordinal ZFSet

/-! ## The first-order language of set theory -/

/-- The relations of the language of set theory: a single binary relation `∈`. -/
inductive memRel : ℕ → Type
  | mem : memRel 2

/-- The first-order language of set theory: one binary relation symbol, no functions. -/

theorem mk_rank_lt_lt (hκ : κ.IsInaccessible) :
    ∀ o : Ordinal.{u}, o < κ.ord → #{x : ZFSet.{u} // x.rank < o} < Cardinal.lift.{u+1,u} κ := by
  intro o
  induction o using Ordinal.induction with
  | _ o IH =>
  intro ho
  have hset : {x : ZFSet.{u} | x.rank < o}
      = ⋃ (i : o.ToType), {x : ZFSet.{u} | x.rank = (ToType.toOrd i : Ordinal)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hx
      exact ⟨ToType.mk ⟨x.rank, hx⟩, by simp [ToType.toOrd]⟩
    · rintro ⟨i, hi⟩
      rw [hi]
      exact (ToType.toOrd i).2
  have hstep : ∀ b : Ordinal.{u},
      #{x : ZFSet.{u} | x.rank = b} ≤ 2 ^ #{y : ZFSet.{u} | y.rank < b} := by
    intro b
    rw [← Cardinal.mk_set]
    apply Cardinal.mk_le_of_injective (f := fun x => {y : {y : ZFSet.{u} | y.rank < b} | y.1 ∈ x.1})
    intro x y h
    simp only [Set.ext_iff, Set.mem_setOf_eq, Subtype.forall] at h
    refine Subtype.ext (ZFSet.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
    · exact (h z (x.2 ▸ ZFSet.rank_lt_of_mem hz)).1 hz
    · exact (h z (y.2 ▸ ZFSet.rank_lt_of_mem hz)).2 hz
  have hreg : (Cardinal.lift.{u+1,u} κ).IsRegular := hκ.isRegular.lift
  have hcard : Cardinal.lift.{u+1,u} #(o.ToType) < Cardinal.lift.{u+1,u} κ := by
    rw [Cardinal.lift_lt, Cardinal.mk_toType]
    exact Cardinal.lt_ord.mp ho
  have hsum : (Cardinal.sum fun i : o.ToType =>
        #{x : ZFSet.{u} | x.rank = (ToType.toOrd i : Ordinal)}) < Cardinal.lift.{u+1,u} κ := by
    refine Cardinal.sum_lt_lift_of_isRegular hreg hcard fun i => ?_
    refine lt_of_le_of_lt (hstep _) ?_
    have hlt : #{y : ZFSet.{u} | y.rank < (ToType.toOrd i : Ordinal)} < Cardinal.lift.{u+1,u} κ :=
      IH _ (ToType.toOrd i).2 (((ToType.toOrd i).2).trans ho)
    obtain ⟨A, hAlt, hA⟩ := Cardinal.lt_lift_iff.mp hlt
    rw [← hA, ← Cardinal.lift_two_power, Cardinal.lift_lt]
    exact hκ.isStrongLimit.two_power_lt hAlt
  have heq : #{x : ZFSet.{u} // x.rank < o} = #({x : ZFSet.{u} | x.rank < o} : Set ZFSet.{u}) := rfl
  rw [heq, hset]
  have hle := @Cardinal.mk_iUnion_le_sum_mk_lift ZFSet.{u} o.ToType
      (fun i => {x : ZFSet.{u} | x.rank = (ToType.toOrd i : Ordinal)})
  rw [Cardinal.lift_id'.{u, u+1}] at hle
  exact lt_of_le_of_lt hle hsum

/-- A set in `V κ` has fewer than `κ` elements. -/
