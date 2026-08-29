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
