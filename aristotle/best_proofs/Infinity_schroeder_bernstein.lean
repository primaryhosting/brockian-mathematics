/-!
# Schroeder Bernstein
Category: Frontier — Set Theory
Target: Infinity.schroeder_bernstein
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

universe u v

section CSB

variable {X : Type u} {Y : Type v}

/-- `iterateFun F n x` is the `n`-fold application of `F` to `x`. -/
def iterateFun (F : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => F (iterateFun F n x)

variable (f : X → Y) (g : Y → X)

/-- The "left part" of `X` in the Schröder-Bernstein construction: those points reachable
from a point outside the range of `g` by iterating `g ∘ f`. -/
def leftPart (x : X) : Prop :=
  ∃ n : Nat, ∃ z : X, (∀ y : Y, g y ≠ z) ∧ iterateFun (fun t => g (f t)) n z = x

theorem leftPart_step {x : X} (hx : leftPart f g x) : leftPart f g (g (f x)) := by
  obtain ⟨n, z, hz, hzx⟩ := hx
  exact ⟨n + 1, z, hz, by simp [iterateFun, hzx]⟩

theorem exists_preimage_of_not_leftPart {x : X} (hx : ¬ leftPart f g x) : ∃ y : Y, g y = x := by
  by_cases h : ∃ y : Y, g y = x
  · exact h
  · exact absurd ⟨0, x, fun y hy => h ⟨y, hy⟩, rfl⟩ hx

open Classical in
/-- The bijection built from the two injections. -/
noncomputable def csbFun (x : X) : Y :=
  if hx : leftPart f g x then f x else Classical.choose (exists_preimage_of_not_leftPart f g hx)

theorem csbFun_of_leftPart {x : X} (hx : leftPart f g x) : csbFun f g x = f x := by
  simp [csbFun, hx]

theorem csbFun_of_not_leftPart {x : X} (hx : ¬ leftPart f g x) : g (csbFun f g x) = x := by
  have h : csbFun f g x = Classical.choose (exists_preimage_of_not_leftPart f g hx) := by
    simp [csbFun, hx]
  rw [h]
  exact Classical.choose_spec (exists_preimage_of_not_leftPart f g hx)

theorem csbFun_injective (hf : Function.Injective f) :
    Function.Injective (csbFun f g) := by
  have key : ∀ x₁ x₂ : X, leftPart f g x₁ → ¬ leftPart f g x₂ →
      csbFun f g x₁ = csbFun f g x₂ → x₁ = x₂ := by
    intro x₁ x₂ h₁ h₂ heq
    have hx₂ : g (csbFun f g x₂) = x₂ := csbFun_of_not_leftPart f g h₂
    rw [csbFun_of_leftPart f g h₁] at heq
    rw [← heq] at hx₂
    exact absurd (hx₂ ▸ leftPart_step f g h₁) h₂
  intro x₁ x₂ heq
  by_cases h₁ : leftPart f g x₁ <;> by_cases h₂ : leftPart f g x₂
  · rw [csbFun_of_leftPart f g h₁, csbFun_of_leftPart f g h₂] at heq
    exact hf heq
  · exact key x₁ x₂ h₁ h₂ heq
  · exact (key x₂ x₁ h₂ h₁ heq.symm).symm
  · have e₁ := csbFun_of_not_leftPart f g h₁
    have e₂ := csbFun_of_not_leftPart f g h₂
    rw [heq] at e₁
    exact e₁.symm.trans e₂

theorem csbFun_surjective (hg : Function.Injective g) : Function.Surjective (csbFun f g) := by
  intro y
  by_cases hy : leftPart f g (g y)
  · obtain ⟨n, z, hz, hzx⟩ := hy
    cases n with
    | zero => exact absurd (hzx ▸ rfl : g y = z) (hz y)
    | succ m =>
      refine ⟨iterateFun (fun t => g (f t)) m z, ?_⟩
      have hstep : g (f (iterateFun (fun t => g (f t)) m z)) = g y := by
        simpa [iterateFun] using hzx
      have hmem : leftPart f g (iterateFun (fun t => g (f t)) m z) := ⟨m, z, hz, rfl⟩
      rw [csbFun_of_leftPart f g hmem]
      exact hg hstep
  · refine ⟨g y, ?_⟩
    exact hg (csbFun_of_not_leftPart f g hy)

end CSB

/-- **Cantor-Schröder-Bernstein**: if there is an injection `f : X → Y` and an injection
`g : Y → X`, then there is a bijection between `X` and `Y`. -/
theorem schroeder_bernstein {X : Type u} {Y : Type v} {f : X → Y} {g : Y → X}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ h : X → Y, Function.Injective h ∧ Function.Surjective h :=
  ⟨csbFun f g, csbFun_injective f g hf, csbFun_surjective f g hg⟩

/-- A two-sided-inverse form of Cantor-Schröder-Bernstein: the bijection `X ≃ Y` given as a
pair of mutually inverse maps. -/
theorem schroeder_bernstein_inverse {X : Type u} {Y : Type v} {f : X → Y} {g : Y → X}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ (h : X → Y) (k : Y → X), (∀ x, k (h x) = x) ∧ (∀ y, h (k y) = y) := by
  obtain ⟨h, hinj, hsurj⟩ := schroeder_bernstein hf hg
  refine ⟨h, fun y => Classical.choose (hsurj y), fun x => ?_, fun y => ?_⟩
  · exact hinj (Classical.choose_spec (hsurj (h x)))
  · exact Classical.choose_spec (hsurj y)

end Infinity

import Mathlib
import RequestProject.SchroederBernstein

/-!
# Schroeder Bernstein — Mathlib cross-check

The main statement `Infinity.schroeder_bernstein` is proved from first principles (see
`RequestProject/SchroederBernstein.lean`, whose required header comment prevents any `import`).
Here we record the corresponding `Equiv`-valued statement, and check it against Mathlib's own
`Function.Embedding.antisymm`.
-/

namespace Infinity

/-- Cantor-Schröder-Bernstein, packaged as an equivalence, derived from
`Infinity.schroeder_bernstein`. -/
theorem nonempty_equiv_of_injective {X : Type u} {Y : Type v} {f : X → Y} {g : Y → X}
    (hf : Function.Injective f) (hg : Function.Injective g) : Nonempty (X ≃ Y) := by
  obtain ⟨h, hinj, hsurj⟩ := schroeder_bernstein hf hg
  exact ⟨Equiv.ofBijective h ⟨hinj, hsurj⟩⟩

/-- The same statement as Mathlib's `Function.Embedding.antisymm`, for comparison. -/
theorem nonempty_equiv_of_injective' {X : Type u} {Y : Type v} {f : X → Y} {g : Y → X}
    (hf : Function.Injective f) (hg : Function.Injective g) : Nonempty (X ≃ Y) :=
  Function.Embedding.antisymm ⟨f, hf⟩ ⟨g, hg⟩

end Infinity

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

