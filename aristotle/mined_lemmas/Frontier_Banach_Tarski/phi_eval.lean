import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

theorem phi_eval (L : List (Fin 2 × Bool)) :
    (3:ℝ) ^ L.length • (phi (FreeGroup.mk L) v0) =
      !₂[((evalW L).1 : ℝ) * sq2, ((evalW L).2.1 : ℝ), ((evalW L).2.2 : ℝ) * sq2] := by
  induction L with
  | nil =>
    have h1 : phi (FreeGroup.mk ([] : List (Fin 2 × Bool))) = 1 := by rw [phi_mk]; simp
    simp only [List.length_nil, pow_zero, one_smul, evalW_nil, h1]
    ext i
    fin_cases i <;> simp [v0]
  | cons x L' ih =>
    have hstep : phi (FreeGroup.mk (x :: L')) v0 = genR x (phi (FreeGroup.mk L') v0) := by
      rw [phi_mk, phi_mk, List.map_cons, List.prod_cons]; rfl
    rw [hstep, List.length_cons, pow_succ]
    have hlin : ((3:ℝ) ^ L'.length * 3) • genR x (phi (FreeGroup.mk L') v0)
        = (3:ℝ) • genR x ((3:ℝ) ^ L'.length • (phi (FreeGroup.mk L') v0)) := by
      rw [map_smul, smul_smul]
      congr 1
      ring
    rw [hlin, ih]
    obtain ⟨i, b⟩ := x
    rcases fin2_eq_zero_or_one i with hi | hi <;> subst hi
    · exact genR_zero_smul b _ _ _
    · exact genR_one_smul b _ _ _

/-- The two rotations `rotA` and `rotB` generate a free group of rank two. -/
