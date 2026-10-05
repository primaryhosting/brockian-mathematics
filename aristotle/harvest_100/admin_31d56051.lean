/-!
# Schroeder Bernstein
Category: Frontier — Set Theory
Target: Infinity.schroeder_bernstein
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (only Lean's prelude is available), because a
module doc comment such as the header above cannot legally precede an `import` line.
Everything below is therefore developed from scratch: the Cantor–Schröder–Bernstein
back-and-forth construction and its correctness proof.  The only classical ingredient
used is `Classical.choice`.

A Mathlib-flavoured restatement, phrased with `Equiv` (`X ≃ Y`), is derived from the
main theorem in `RequestProject/SchroederBernsteinEquiv.lean`.
-/

namespace Infinity

universe u v

section
variable {X : Type u} {Y : Type v}

/-- `iterate F n x` is the `n`-fold application `F (F (… (F x)))`. -/
def iterate (F : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => F (iterate F n x)

/-- `Reach f g x` says that `x : X` is obtained from some element outside the range of
`g` by finitely many applications of `g ∘ f`.  These are exactly the points where the
Cantor–Schröder–Bernstein bijection is defined to be `f`. -/
def Reach (f : X → Y) (g : Y → X) (x : X) : Prop :=
  ∃ n : Nat, ∃ x₀ : X, (∀ y : Y, g y ≠ x₀) ∧ x = iterate (fun x => g (f x)) n x₀

/-- A point that is not reachable lies in the range of `g`. -/
theorem exists_preimage {f : X → Y} {g : Y → X} {x : X} (hx : ¬ Reach f g x) :
    ∃ y : Y, g y = x :=
  Classical.byContradiction fun hc =>
    hx ⟨0, x, fun y hy => hc ⟨y, hy⟩, rfl⟩

/-- The Cantor–Schröder–Bernstein map: `f` on reachable points, the inverse of `g`
elsewhere. -/
noncomputable def bij (f : X → Y) (g : Y → X) (x : X) : Y :=
  @dite _ (Reach f g x) (Classical.propDecidable _) (fun _ => f x)
    (fun hx => Classical.choose (exists_preimage hx))

theorem bij_pos {f : X → Y} {g : Y → X} {x : X} (hx : Reach f g x) : bij f g x = f x := by
  simp [bij, dif_pos hx]

theorem bij_neg {f : X → Y} {g : Y → X} {x : X} (hx : ¬ Reach f g x) :
    g (bij f g x) = x := by
  have h : bij f g x = Classical.choose (exists_preimage hx) := by
    simp [bij, dif_neg hx]
  rw [h]
  exact Classical.choose_spec (exists_preimage hx)

/-- Reachability is preserved by one step of `g ∘ f`. -/
theorem reach_step {f : X → Y} {g : Y → X} {x : X} (hx : Reach f g x) :
    Reach f g (g (f x)) := by
  obtain ⟨n, x₀, h0, hn⟩ := hx
  exact ⟨n + 1, x₀, h0, by rw [hn]; rfl⟩

theorem bij_injective {f : X → Y} {g : Y → X} (hf : Function.Injective f) :
    Function.Injective (bij f g) := by
  have key : ∀ x x' : X, Reach f g x → ¬ Reach f g x' → bij f g x ≠ bij f g x' := by
    intro x x' hx hx' he
    have h1 : g (bij f g x') = x' := bij_neg hx'
    rw [← he, bij_pos hx] at h1
    exact hx' (h1 ▸ reach_step hx)
  intro x x' he
  by_cases hx : Reach f g x
  · by_cases hx' : Reach f g x'
    · exact hf (by rw [← bij_pos hx, ← bij_pos hx', he])
    · exact absurd he (key x x' hx hx')
  · by_cases hx' : Reach f g x'
    · exact absurd he.symm (key x' x hx' hx)
    · have h1 := bij_neg hx
      rw [he, bij_neg hx'] at h1
      exact h1.symm

theorem bij_surjective {f : X → Y} {g : Y → X} (hg : Function.Injective g) :
    Function.Surjective (bij f g) := by
  intro y
  by_cases h : Reach f g (g y)
  · obtain ⟨n, x₀, h0, hn⟩ := h
    cases n with
    | zero => exact absurd (hn ▸ rfl : g y = x₀) (h0 y)
    | succ m =>
        refine ⟨iterate (fun x => g (f x)) m x₀, ?_⟩
        have hr : Reach f g (iterate (fun x => g (f x)) m x₀) := ⟨m, x₀, h0, rfl⟩
        rw [bij_pos hr]
        exact (hg (hn.trans rfl)).symm
  · exact ⟨g y, hg (bij_neg h)⟩

/-- **Cantor–Schröder–Bernstein**.  If there is an injection `f : X → Y` and an
injection `g : Y → X`, then `X` and `Y` are in bijection: there are mutually inverse
maps `h : X → Y` and `k : Y → X`, with `h` injective and surjective. -/
theorem schroeder_bernstein {X : Type u} {Y : Type v} {f : X → Y} {g : Y → X}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ (h : X → Y) (k : Y → X),
      Function.Injective h ∧ Function.Surjective h ∧
        (∀ x, k (h x) = x) ∧ (∀ y, h (k y) = y) := by
  have hinj : Function.Injective (bij f g) := bij_injective hf
  have hsurj : Function.Surjective (bij f g) := bij_surjective hg
  refine ⟨bij f g, fun y => Classical.choose (hsurj y), hinj, hsurj, ?_, ?_⟩
  · intro x
    exact hinj (Classical.choose_spec (hsurj (bij f g x)))
  · intro y
    exact Classical.choose_spec (hsurj y)

end
end Infinity

import Mathlib
import RequestProject.SchroederBernstein

/-!
# Schroeder Bernstein, phrased with `Equiv`

A Mathlib-flavoured corollary of `Infinity.schroeder_bernstein`: injections in both
directions yield an equivalence of types `X ≃ Y`.
-/

namespace Infinity

/-- Cantor–Schröder–Bernstein, stated as the existence of an equivalence `X ≃ Y`. -/
theorem schroeder_bernstein_equiv {X Y : Type*} {f : X → Y} {g : Y → X}
    (hf : Function.Injective f) (hg : Function.Injective g) : Nonempty (X ≃ Y) := by
  obtain ⟨h, k, hinj, hsurj, hk, hh⟩ := schroeder_bernstein hf hg
  exact ⟨⟨h, k, hk, hh⟩⟩

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

