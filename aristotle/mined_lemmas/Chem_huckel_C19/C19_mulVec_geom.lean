import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to precede any module documentation, so the requested
header comment appears immediately after the single `import Mathlib` line.)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₉`, i.e. the Hückel matrix of the
carbon skeleton of a 19-membered annulene (with `α = 0`, `β = 1`). -/

lemma C19_mulVec_geom {w : ℂ} (hw : w ^ 19 = 1) :
    C19 *ᵥ (fun j : Fin 19 => w ^ (j : ℕ)) = (w + w⁻¹) • (fun j : Fin 19 => w ^ (j : ℕ)) := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; norm_num at hw
  funext i
  have hne : (i - 1 : Fin 19) ≠ i + 1 := by revert i; decide
  have hnb : (SimpleGraph.cycleGraph 19).neighborFinset i = {i - 1, i + 1} :=
    SimpleGraph.cycleGraph_neighborFinset (n := 17) (v := i)
  rw [C19, SimpleGraph.adjMatrix_mulVec_apply, hnb, Finset.sum_pair hne]
  have h1 : w ^ ((i - 1 : Fin 19) : ℕ) = w ^ (i : ℕ) * w⁻¹ := by
    field_simp
    exact pow_val_sub_one hw i
  rw [h1, pow_val_add_one hw i]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- `exp (θ i) + exp (θ i)⁻¹ = 2 cos θ`. -/
