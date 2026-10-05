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
theorem hardy_paradox_measure {Λ : Type*} [MeasurableSpace Λ] (μ : Measure Λ)
    (A₁ A₂ B₁ B₂ : Λ → Bool)
    (h11 : μ {l : Λ | A₁ l = true ∧ B₁ l = true} = 0)
    (h21 : μ {l : Λ | A₂ l = true ∧ B₁ l = false} = 0)
    (h12 : μ {l : Λ | A₁ l = false ∧ B₂ l = true} = 0)
    (hpos : 0 < μ {l : Λ | A₂ l = true ∧ B₂ l = true}) : False := by
  have hzero : μ {l : Λ | A₂ l = true ∧ B₂ l = true} = 0 := by
    refine le_antisymm ?_ (zero_le _)
    calc μ {l : Λ | A₂ l = true ∧ B₂ l = true}
        ≤ μ ({l : Λ | A₁ l = true ∧ B₁ l = true} ∪
            {l : Λ | A₂ l = true ∧ B₁ l = false} ∪
            {l : Λ | A₁ l = false ∧ B₂ l = true}) :=
          measure_mono (hardy_subset A₁ A₂ B₁ B₂)
      _ ≤ μ ({l : Λ | A₁ l = true ∧ B₁ l = true} ∪
            {l : Λ | A₂ l = true ∧ B₁ l = false}) +
            μ {l : Λ | A₁ l = false ∧ B₂ l = true} := measure_union_le _ _
      _ ≤ (μ {l : Λ | A₁ l = true ∧ B₁ l = true} +
            μ {l : Λ | A₂ l = true ∧ B₁ l = false}) +
            μ {l : Λ | A₁ l = false ∧ B₂ l = true} := by
          gcongr
          exact measure_union_le _ _
      _ = 0 := by rw [h11, h21, h12]; simp
  exact absurd hzero (ne_of_gt hpos)

/-!
## The Hardy conditions are consistent for a nonlocal (no-signaling) behaviour

Settings are encoded by `Bool`: `false` = first measurement, `true` = second measurement.
Outcomes are encoded by `Bool`: `true` = outcome `1`, `false` = outcome `0`.
-/

/-- An explicit no-signaling box realising Hardy's conditions: the two outcomes are
perfectly correlated unless both parties choose their first measurement, in which case
they are perfectly anticorrelated.  `hardyBox x y a b` is `P(a, b | x, y)`. -/
def hardyBox (x y a b : Bool) : ℚ := if xor a b = (!x && !y) then 1 / 2 else 0

lemma hardyBox_nonneg (x y a b : Bool) : 0 ≤ hardyBox x y a b := by
  unfold hardyBox; split <;> norm_num

/-- Each conditional distribution is normalised. -/
lemma hardyBox_normalised (x y : Bool) :
    ∑ a : Bool, ∑ b : Bool, hardyBox x y a b = 1 := by
  cases x <;> cases y <;> norm_num [hardyBox]

/-- No-signaling from Bob to Alice: Alice's marginal does not depend on Bob's setting. -/
lemma hardyBox_no_signaling_A (x y y' a : Bool) :
    ∑ b : Bool, hardyBox x y a b = ∑ b : Bool, hardyBox x y' a b := by
  cases x <;> cases y <;> cases y' <;> cases a <;> simp [hardyBox]

/-- No-signaling from Alice to Bob: Bob's marginal does not depend on Alice's setting. -/
lemma hardyBox_no_signaling_B (x x' y b : Bool) :
    ∑ a : Bool, hardyBox x y a b = ∑ a : Bool, hardyBox x' y a b := by
  cases x <;> cases x' <;> cases y <;> cases b <;> simp [hardyBox]

/-- All four Hardy conditions hold for `hardyBox`, the last one with Hardy fraction
`1/2 > 0`.  Consequently the hypotheses of `QI.hardy_paradox` describe a genuinely
realisable statistical situation, which nevertheless admits no local realistic model. -/
theorem hardyBox_hardy_conditions :
    hardyBox false false true true = 0 ∧
    hardyBox true false true false = 0 ∧
    hardyBox false true false true = 0 ∧
    0 < hardyBox true true true true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [hardyBox]

end QI

/-!
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Hardy's nonlocality argument.

Two spacelike separated parties, Alice and Bob, each choose one of two measurements.
In a *local realistic* (local hidden variable) model the outcomes of **all four**
measurements are simultaneously determined by a hidden variable `l : Λ`, via functions

* `A₁ A₂ : Λ → Bool` (Alice's outcome for her first / second measurement),
* `B₁ B₂ : Λ → Bool` (Bob's outcome for her first / second measurement),

and the observed statistics are obtained by sampling `l`.

Hardy's four conditions are

* `P(A₁ = 1, B₁ = 1) = 0`,
* `P(A₂ = 1, B₁ = 0) = 0`,
* `P(A₁ = 0, B₂ = 1) = 0`,
* `P(A₂ = 1, B₂ = 1) > 0`.

Quantum mechanics predicts all four, the last one for a nonzero *fraction* of the runs.
No local realistic model can: this is proved without any inequality, purely from the
pointwise logic of the hidden variable assignment.

This file is deliberately `import`-free (Lean core only) so that the required header
comment can literally be the first thing in the file; the measure-theoretic version of
the same statement, together with an explicit no-signaling behaviour that does satisfy
all four Hardy conditions, lives in `RequestProject/HardyQuantum.lean`.
-/

universe u

namespace QI

/-- **Hardy's logical core.**  For a single value `l` of the hidden variable, the three
"impossible" events already force the fourth event to be impossible as well: no assignment
of outcomes to all four measurements can have `A₂ l = 1` and `B₂ l = 1` while avoiding all
three forbidden coincidences. -/
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
theorem hardy_paradox {Λ : Type u} (A₁ A₂ B₁ B₂ : Λ → Bool) (runs : List Λ)
    (h11 : runs.countP (fun l => A₁ l && B₁ l) = 0)
    (h21 : runs.countP (fun l => A₂ l && !B₁ l) = 0)
    (h12 : runs.countP (fun l => !A₁ l && B₂ l) = 0)
    (hpos : 0 < runs.countP (fun l => A₂ l && B₂ l)) : False := by
  have key : runs.countP (fun l => A₂ l && B₂ l) = 0 := by
    rw [List.countP_eq_zero]
    intro l hl
    have e11 := List.countP_eq_zero.mp h11 l hl
    have e21 := List.countP_eq_zero.mp h21 l hl
    have e12 := List.countP_eq_zero.mp h12 l hl
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at e11 e21 e12 ⊢
    exact hardy_pointwise A₁ A₂ B₁ B₂ l e11 e21 e12
  omega

end QI

