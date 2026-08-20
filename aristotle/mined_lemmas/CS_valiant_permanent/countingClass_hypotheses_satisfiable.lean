/-
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

/-- An instance of the 0/1 permanent problem: a size `n` together with an `n × n`
matrix of bits, viewed equivalently as the adjacency data of a bipartite graph. -/
structure Inst where
  size : ℕ
  edge : Fin size → Fin size → Bool

/-- The 0/1 matrix (over `ℕ`) attached to an instance. -/

theorem countingClass_hypotheses_satisfiable :
    ∃ SharpP : (Inst → ℕ) → Prop,
      (∀ f g, ParsimoniousReduction f g → SharpP g → SharpP f) ∧
      SharpP matchingCount ∧ (∀ f, SharpP f → ParsimoniousReduction f matchingCount) :=
  ⟨fun f => ParsimoniousReduction f matchingCount,
    fun _ _ hfg hg => parsimoniousReduction_trans hfg hg,
    parsimoniousReduction_refl _, fun _ h => h⟩

/-! ### The permanent of a 0/1 matrix counts witnesses -/

