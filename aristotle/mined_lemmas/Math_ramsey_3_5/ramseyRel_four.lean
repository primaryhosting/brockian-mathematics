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

theorem ramseyRel_four : RamseyRel 9 4 := by
  refine ramseyRel_of_card_eq 9 4 ?_
  intro V G A hA
  by_contra hcon
  push_neg at hcon
  obtain ⟨htri, hind⟩ := hcon
  classical
  have hind' : ¬ HasIndepIn G A (3 + 1) := by simpa using hind
  have hdeg : ∀ v ∈ A, (nbrIn G A v).card = 3 := by
    intro v hv
    have h1 := card_split G hv
    have h2 := card_nbrIn_le (t := 3) G (A := A) (v := v) hv htri hind'
    have h3 := card_nonNbrIn_lt (t := 3) (k := 6) G ramseyRel_three hv htri hind'
    omega
  have hsum : ∑ v ∈ A, (nbrIn G A v).card = 27 := by
    rw [Finset.sum_congr rfl hdeg, Finset.sum_const, hA]
    rfl
  have heven : Even (∑ v ∈ A, (nbrIn G A v).card) := by
    have hcf : ∀ v, (nbrIn G A v).card = ∑ w ∈ A, if G.Adj v w then 1 else 0 := by
      intro v; exact Finset.card_filter _ _
    simp_rw [hcf]
    refine even_sum_symm (fun v w => if G.Adj v w then 1 else 0) ?_ ?_ A
    · intro x y
      by_cases h : G.Adj x y
      · simp [h, h.symm]
      · simp only [h, if_false]
        rw [if_neg (fun h' : G.Adj y x => h h'.symm)]
    · intro x; simp
  rw [hsum] at heven
  norm_num at heven

/-- `R(3,5) ≤ 14`. -/
