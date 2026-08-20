/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` to come first in a file, so the header above the import is a plain
block comment and this is the module docstring with the same content.)

Mathlib does not contain Ramsey numbers, so the whole development is built here:
the recursion `R(3,t+1) ≤ t + R(3,t)`, the parity refinement giving `R(3,4) ≤ 9`,
hence `R(3,5) ≤ 14`, and the circulant graph `C₁₃(1,5)` witnessing `R(3,5) > 13`.
-/

set_option maxHeartbeats 2000000

namespace Math

open Finset

/-! ## The Ramsey property -/

/-- `RamseyProp n s t` says that every simple graph on `n` vertices contains either a clique
of size `s` or an independent set of size `t` (equivalently, a clique of size `t` in the
complement).  `R(s,t)` is the least `n` with this property. -/

theorem ramseyRel_two : RamseyRel 3 2 := by
  intro V G A hA
  classical
  by_cases hpair : ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ ¬ G.Adj x y
  · obtain ⟨x, hx, y, hy, hxy, hadj⟩ := hpair
    refine Or.inr ⟨{x, y}, ?_, ?_, ?_⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
    · intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
      exact fun h => hadj h.symm
  · push_neg at hpair
    obtain ⟨A', hA', hcard⟩ := Finset.exists_subset_card_eq hA
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hcard
    have ha : a ∈ A := hA' (by simp)
    have hb : b ∈ A := hA' (by simp)
    have hc : c ∈ A := hA' (by simp)
    exact Or.inl ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hpair a ha b hb hab,
      hpair a ha c hc hac, hpair b hb c hc hbc⟩

section Neighborhood

variable [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The neighbours of `v` inside `A`. -/
