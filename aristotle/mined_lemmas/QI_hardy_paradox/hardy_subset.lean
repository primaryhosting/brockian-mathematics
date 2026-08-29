import Mathlib
import RequestProject.Main

/-!
# Hardy Paradox — measure-theoretic form and a quantum-style witness

Companion to `RequestProject/Main.lean`, which contains the target theorem
`QI.hardy_paradox`.  Here we record

* `QI.hardy_paradox_measure`: the same impossibility for an arbitrary local hidden
  variable model given by a measure on the hidden variable space, and
* `QI.hardyBox`: an explicit no-signaling behaviour satisfying all four Hardy
  conditions with Hardy fraction `1/2`, showing that the hypotheses of the paradox
  are jointly realisable by a nonlocal (but no-signaling) theory, so that the
  statement is not vacuous.
-/

open scoped BigOperators

namespace QI

open MeasureTheory

/-- The set-theoretic form of Hardy's argument: the Hardy event is contained in the union
of the three forbidden events. -/

theorem hardy_subset {Λ : Type*} (A₁ A₂ B₁ B₂ : Λ → Bool) :
    {l : Λ | A₂ l = true ∧ B₂ l = true} ⊆
      {l : Λ | A₁ l = true ∧ B₁ l = true} ∪
      {l : Λ | A₂ l = true ∧ B₁ l = false} ∪
      {l : Λ | A₁ l = false ∧ B₂ l = true} := by
  intro l hl
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hcon
  exact hardy_pointwise A₁ A₂ B₁ B₂ l hcon.1.1 hcon.1.2 hcon.2 hl

/-- **Hardy's paradox, measure-theoretic form.**  There is no local hidden variable model
— a measure space `Λ` of hidden variables together with predetermined outcomes
`A₁, A₂, B₁, B₂` for all four measurements — reproducing Hardy's four conditions.  The
first three conditions say certain coincidences never happen; the fourth says a nonzero
fraction of the runs exhibits the coincidence `A₂ = 1, B₂ = 1`. -/
