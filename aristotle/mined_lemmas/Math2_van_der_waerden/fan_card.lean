/-
# Van Der Waerden
Category: Frontier Math
Target: Math2.van_der_waerden
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Van Der Waerden

Category: Frontier Math

Target: `Math2.van_der_waerden`

Provenance: Aristotle theorem prover (Harmonic)

Any finite coloring of `ℕ` has arbitrarily long monochromatic arithmetic progressions.

The proof is the classical "color focusing" (Graham–Rothschild) double induction:
an outer induction on the length `k` of the progression, and, inside it, an induction on
the number `s` of *focused* progressions with pairwise distinct colors that can be found
in a sufficiently long window.
-/

set_option autoImplicit false

namespace Math2

/-- `HasAP c k N` : the coloring `c` has a monochromatic arithmetic progression of
length `k` (with positive common difference `d < N`) such that even the "next" term
`a + k * d` lies below `N`. -/

theorem fan_card {k r N : ℕ} {c : ℕ → Fin r} (h : Fan c k r N) : False := by
  obtain ⟨f, a, d, hf, hAPs, hdist, hfd⟩ := h
  set g : Fin (r + 1) → Fin r := fun j => if h : (j : ℕ) < r then c (a j) else c f with hg
  have hinj : Function.Injective g := by
    intro x y hxy
    simp only [hg] at hxy
    by_cases hx : (x : ℕ) < r <;> by_cases hy : (y : ℕ) < r <;>
      simp only [hx, hy, dif_pos, dif_neg, not_false_iff] at hxy
    · by_contra hne
      exact hdist x hx y hy (fun hc => hne (Fin.ext hc)) hxy
    · exact absurd hxy (hfd x hx)
    · exact absurd hxy.symm (hfd y hy)
    · have : (x : ℕ) = y := by omega
      exact Fin.ext this
  have hle := Fintype.card_le_of_injective g hinj
  simp at hle

