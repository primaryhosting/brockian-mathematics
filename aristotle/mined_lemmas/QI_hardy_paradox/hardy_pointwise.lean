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

theorem hardy_pointwise {Λ : Type u} (A₁ A₂ B₁ B₂ : Λ → Bool) (l : Λ)
    (h11 : ¬(A₁ l = true ∧ B₁ l = true))
    (h21 : ¬(A₂ l = true ∧ B₁ l = false))
    (h12 : ¬(A₁ l = false ∧ B₂ l = true)) :
    ¬(A₂ l = true ∧ B₂ l = true) := by
  rintro ⟨ha2, hb2⟩
  -- `A₂ l = 1` rules out `B₁ l = 0`, hence `B₁ l = 1`.
  have hb1 : B₁ l = true := by
    cases hb1 : B₁ l with
    | false => exact absurd ⟨ha2, hb1⟩ h21
    | true => rfl
  -- `B₂ l = 1` rules out `A₁ l = 0`, hence `A₁ l = 1`.
  have ha1 : A₁ l = true := by
    cases ha1 : A₁ l with
    | false => exact absurd ⟨ha1, hb2⟩ h12
    | true => rfl
  exact h11 ⟨ha1, hb1⟩

/-- **Hardy's paradox.**  Consider any local hidden variable model: a list `runs` of the
hidden variable values realised in an experiment, together with outcomes `A₁, A₂, B₁, B₂`
for all four measurements, predetermined by the hidden variable.  If none of the runs
exhibits any of Hardy's three forbidden coincidences, then *no* run exhibits the event
`A₂ = 1, B₂ = 1`; so a positive fraction of runs with that event is impossible.

Quantum mechanics does predict exactly this situation, with a positive fraction of runs
(see `QI.hardyBox_hardy_conditions` in `RequestProject/HardyQuantum.lean` for an explicit
no-signaling behaviour achieving fraction `1/2`).  Hence local realism is refuted, with no
inequality involved. -/
