import Mathlib
/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

/-- Vertices of the Kneser graph `KG_{n,k}`: the `k`-element subsets of an `n`-element set. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-subsets of `Fin n`, and two
distinct vertices are adjacent when the corresponding sets are disjoint. -/

theorem not_colorable_two_of_odd_closed_walk {V : Type*} {G : SimpleGraph V}
    (f : ℕ → V) (N : ℕ) (hadj : ∀ j < N, G.Adj (f j) (f (j + 1)))
    (hcl : f N = f 0) (hodd : Odd N) : ¬ G.Colorable 2 := by
  rintro ⟨C⟩
  let D : G.Coloring (ZMod 2) := C
  have key : ∀ j ≤ N, D (f j) = D (f 0) + (j : ZMod 2) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have hne : D (f i) ≠ D (f (i + 1)) := D.valid (hadj i (by omega))
      have hstep : D (f (i + 1)) = D (f i) + 1 := by
        revert hne
        generalize D (f i) = a
        generalize D (f (i + 1)) = b
        revert a b
        decide
      rw [hstep, ih (by omega)]
      push_cast
      ring
  obtain ⟨m, hm⟩ := hodd
  have h1 : ((N : ℕ) : ZMod 2) = 1 := by
    subst hm
    have h : ((2 * m + 1 : ℕ) : ZMod 2) = (2 : ZMod 2) * m + 1 := by push_cast; ring
    rw [h, show (2 : ZMod 2) = 0 from rfl]
    ring
  have hN := key N le_rfl
  rw [hcl, h1] at hN
  exact absurd hN (by generalize D (f 0) = a; revert a; decide)

/-- The residue of `x` modulo `2k+1`, as an element of `Fin (2k+1)`. -/
