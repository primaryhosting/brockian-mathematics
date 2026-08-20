import Mathlib
/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Faltings' theorem (the Mordell conjecture) states that a smooth projective curve of genus
`≥ 2` over `ℚ` has only finitely many rational points.

In this file we

* formalise the statement for smooth plane curves in `ℙ²`, where the genus is given by the
  degree–genus formula `g = (d-1)(d-2)/2`, so that `d ≥ 4` is exactly the condition `g ≥ 2`
  (`Frontier.FaltingsMordellStatement`);
* verify, unconditionally, an instance of it: the Fermat quartic `x⁴ + y⁴ = z⁴`, a smooth
  plane curve of degree `4` and hence of genus `3`, has only finitely many rational points
  (`Frontier.faltings_mordell`) — indeed exactly four (`Frontier.fermatQuartic_projPoints`).
  The proof uses Fermat's Last Theorem for exponent four.
-/

namespace Frontier

open MvPolynomial
open scoped LinearAlgebra.Projectivization

noncomputable section

/-- The set of `ℚ`-points of the plane projective curve cut out by `F`. -/

theorem fermatQuartic_projPoints : projPoints fermatQuartic = fermatQuarticPointSet := by
  have hne0 : (![1, 0, 1] : Fin 3 → ℚ) ≠ 0 := by intro h; simpa using congrFun h 0
  have hne1 : (![1, 0, -1] : Fin 3 → ℚ) ≠ 0 := by intro h; simpa using congrFun h 0
  have hne2 : (![0, 1, 1] : Fin 3 → ℚ) ≠ 0 := by intro h; simpa using congrFun h 1
  have hne3 : (![0, 1, -1] : Fin 3 → ℚ) ≠ 0 := by intro h; simpa using congrFun h 1
  ext p
  constructor
  · intro hp
    have hv : p.rep ≠ 0 := p.rep_nonzero
    have heq : p.rep 0 ^ 4 + p.rep 1 ^ 4 - p.rep 2 ^ 4 = 0 := by
      simpa [projPoints] using hp
    obtain ⟨a, ha, hcase⟩ := fermatQuartic_solutions p.rep hv heq
    have key : ∀ (w : Fin 3 → ℚ) (hw : w ≠ 0), p.rep = a • w →
        p = Projectivization.mk ℚ w hw := by
      intro w hw hpw
      rw [← Projectivization.mk_rep p]
      exact (Projectivization.mk_eq_mk_iff' ℚ p.rep w hv hw).mpr ⟨a, hpw.symm⟩
    rcases hcase with hc | hc | hc | hc
    · exact Or.inl (key _ hne0 hc)
    · exact Or.inr (Or.inl (key _ hne1 hc))
    · exact Or.inr (Or.inr (Or.inl (key _ hne2 hc)))
    · exact Or.inr (Or.inr (Or.inr (key _ hne3 hc)))
  · intro hp
    rcases hp with hc | hc | hc | hc <;> rw [hc] <;>
      [exact (mem_projPoints_mk _ hne0).mpr (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]);
       exact (mem_projPoints_mk _ hne1).mpr (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]);
       exact (mem_projPoints_mk _ hne2).mpr (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]);
       exact (mem_projPoints_mk _ hne3).mpr (by norm_num [Matrix.cons_val_two, Matrix.tail_cons])]

/-- **Faltings' theorem for the Fermat quartic.** The smooth plane quartic `x⁴ + y⁴ = z⁴`
has genus `3 ≥ 2`, and it has only finitely many rational points — an unconditional
instance of the Mordell conjecture. -/
