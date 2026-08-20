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


theorem E_spec : ∀ a < ω₁, Nice a (E a) ∧ ∀ b < a, Coh (E a) (E b) b := by
  intro a
  induction a using Ordinal.induction with
  | _ a IH =>
    intro ha
    classical
    set d : Ordinal.{0} → Ordinal.{0} → ℕ := fun b => if b < a then E b else fun _ => 0 with hd
    have hdval : ∀ b < a, d b = E b := by intro b hb; rw [hd]; simp [hb]
    have hdgood : ∀ b < a, Nice b (d b) ∧ ∀ c < b, Coh (d b) (d c) c := by
      intro b hb
      rw [hdval b hb]
      refine ⟨(IH b hb (hb.trans ha)).1, fun c hc => ?_⟩
      rw [hdval c (hc.trans hb)]
      exact (IH b hb (hb.trans ha)).2 c hc
    have hex := exists_step a ha d hdgood
    have := stepFun_spec hex
    rw [← E_eq a] at this
    refine ⟨this.1, fun b hb => ?_⟩
    have h2 := this.2 b hb
    rwa [hdval b hb] at h2

end Aronszajn

/-
The Aronszajn tree built from the coherent sequence `E`: its nodes are the
functions which are injective below some countable ordinal `a`, vanish from `a`
on, and differ from `E a` in only finitely many places; the order is end-extension.
-/
import RequestProject.Aronszajn.Coherent

open Ordinal Cardinal Set

namespace Aronszajn

/-- The set of nodes of the tree. A node is a pair `(a, f)` where `a < ω₁`, `f` is
injective below `a`, vanishes from `a` on, and differs from `E a` finitely often. -/
