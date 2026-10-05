import Mathlib

/-!
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

open MeasureTheory

/-! ## Hardy's paradox for local hidden-variable models

A local hidden-variable model for a bipartite experiment with two binary settings and two
binary outcomes per party consists of a probability space `Ω` (the hidden variables) together
with outcome functions `A x ω` for Alice and `B y ω` for Bob.  *Locality* is encoded in the
types: Alice's outcome depends only on her own setting `x` and the hidden variable `ω`, never
on Bob's setting `y`, and symmetrically for Bob.

Hardy's argument shows that no such model can satisfy the four *Hardy conditions*:

* `A₁ = 1` implies `B₂ = 1` (almost surely),
* `B₁ = 1` implies `A₂ = 1` (almost surely),
* `A₂ = 1` and `B₂ = 1` never happen together (almost surely),
* yet `A₁ = 1` and `B₁ = 1` happen with nonzero probability.

Here the setting `false` stands for the first measurement and `true` for the second one, and
the outcome `true` stands for the outcome "1".
-/

/-- **Hardy's paradox.**  There is no local hidden-variable model satisfying the four Hardy
conditions.  Locality is built into the statement: Alice's outcome `A x ω` does not depend on
Bob's setting and Bob's outcome `B y ω` does not depend on Alice's setting.

The three "impossible" events have probability zero, while the event `A₁ = 1 ∧ B₁ = 1` has
nonzero probability; but that event is contained in the union of the three null events, a
contradiction.  No measurability assumptions are needed. -/
theorem hardy_paradox {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A B : Bool → Ω → Bool)
    (hA₁B₂ : μ {ω | A false ω = true ∧ B true ω = false} = 0)
    (hA₂B₁ : μ {ω | A true ω = false ∧ B false ω = true} = 0)
    (hA₂B₂ : μ {ω | A true ω = true ∧ B true ω = true} = 0)
    (hpos : μ {ω | A false ω = true ∧ B false ω = true} ≠ 0) :
    False := by
  apply hpos
  have hsub :
      {ω | A false ω = true ∧ B false ω = true} ⊆
        {ω | A false ω = true ∧ B true ω = false} ∪
          ({ω | A true ω = false ∧ B false ω = true} ∪
            {ω | A true ω = true ∧ B true ω = true}) := by
    intro ω hω
    obtain ⟨ha, hb⟩ := hω
    by_cases hb₂ : B true ω = true
    · by_cases ha₂ : A true ω = true
      · exact Or.inr (Or.inr ⟨ha₂, hb₂⟩)
      · exact Or.inr (Or.inl ⟨by simpa using ha₂, hb⟩)
    · exact Or.inl ⟨ha, by simpa using hb₂⟩
  refine le_antisymm ?_ (zero_le _)
  calc μ {ω | A false ω = true ∧ B false ω = true}
      ≤ μ ({ω | A false ω = true ∧ B true ω = false} ∪
          ({ω | A true ω = false ∧ B false ω = true} ∪
            {ω | A true ω = true ∧ B true ω = true})) := measure_mono hsub
    _ ≤ μ {ω | A false ω = true ∧ B true ω = false} +
          (μ {ω | A true ω = false ∧ B false ω = true} +
            μ {ω | A true ω = true ∧ B true ω = true}) :=
        le_trans (measure_union_le _ _) (by gcongr; exact measure_union_le _ _)
    _ = 0 := by rw [hA₁B₂, hA₂B₁, hA₂B₂]; simp

/-! ## A quantum model realising the Hardy conditions

We exhibit an explicit two-qubit state and explicit projective measurements for which the
Hardy conditions hold, with the "paradoxical" event occurring in a fraction `1/12` of the
runs.  Combined with `QI.hardy_paradox`, this shows that the quantum predictions cannot be
reproduced by any local hidden-variable model — and, unlike Bell's theorem, the argument uses
no inequalities, only events of probability zero and one event of positive probability.

The state is `ψ = (|01⟩ + |10⟩ - |11⟩)/√3`.  For setting `true` (the second measurement) each
party measures in the computational basis; for setting `false` (the first measurement) each
party measures in the basis `(|0⟩ ± |1⟩)/√2`, with the outcome `1` corresponding to `+`. -/

/-- The measurement vector of a party for setting `x` and outcome `a` (a unit vector in `ℂ²`).
For each fixed setting the two outcome vectors form an orthonormal basis of `ℂ²`. -/
noncomputable def qvec : Bool → Bool → Fin 2 → ℂ
  | false, true  => ![1 / Real.sqrt 2, 1 / Real.sqrt 2]
  | false, false => ![1 / Real.sqrt 2, -(1 / Real.sqrt 2)]
  | true,  true  => ![1, 0]
  | true,  false => ![0, 1]

/-- The Hardy state `ψ = (|01⟩ + |10⟩ - |11⟩)/√3`, written as its coefficient matrix. -/
noncomputable def psi : Fin 2 → Fin 2 → ℂ :=
  ![![0, 1 / Real.sqrt 3], ![1 / Real.sqrt 3, -(1 / Real.sqrt 3)]]

/-- The Born-rule probability of outcomes `(a, b)` given settings `(x, y)`. -/
noncomputable def qprob (x y a b : Bool) : ℝ :=
  Complex.normSq (∑ i : Fin 2, ∑ j : Fin 2, (starRingEnd ℂ) (qvec x a i * qvec y b j) * psi i j)

lemma sqrt_two_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  have : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  exact_mod_cast Complex.ofReal_ne_zero.mpr (ne_of_gt this)

lemma sqrt_three_ne_zero : (Real.sqrt 3 : ℂ) ≠ 0 := by
  have : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  exact_mod_cast Complex.ofReal_ne_zero.mpr (ne_of_gt this)

lemma sq_sqrt_two : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h

lemma sq_sqrt_three : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
  have h : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h

/-- Hardy condition 1: with the first setting on both sides, both outcomes are `1` in a
fraction `1/12` of the runs. -/
theorem qprob_first_first : qprob false false true true = 1 / 12 := by
  simp [qprob, psi, qvec, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.normSq_apply]
  field_simp
  ring_nf
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [show Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 by ring, h2, h3]
  norm_num

/-- Hardy condition 2: `A₁ = 1` forces `B₂ = 1`. -/
theorem qprob_A₁_one_B₂_zero : qprob false true true false = 0 := by
  simp [qprob, psi, qvec, Fin.sum_univ_two, Complex.normSq_apply]

/-- Hardy condition 3: `B₁ = 1` forces `A₂ = 1`. -/
theorem qprob_A₂_zero_B₁_one : qprob true false false true = 0 := by
  simp [qprob, psi, qvec, Fin.sum_univ_two, Complex.normSq_apply]

/-- Hardy condition 4: the second settings never both give outcome `1`. -/
theorem qprob_A₂_one_B₂_one : qprob true true true true = 0 := by
  simp [qprob, psi, qvec, Fin.sum_univ_two, Complex.normSq_apply]

/-- For every pair of settings the four Born probabilities sum to `1`, so `qprob` really is a
family of probability distributions. -/
theorem qprob_normalized (x y : Bool) :
    qprob x y false false + qprob x y false true + qprob x y true false + qprob x y true true
      = 1 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2' : Real.sqrt 2 ≠ 0 := by positivity
  have h3' : Real.sqrt 3 ≠ 0 := by positivity
  have h4 : Real.sqrt 2 ^ 4 = 4 := by
    rw [show Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 by ring, h2]; norm_num
  have h9 : Real.sqrt 3 ^ 4 = 9 := by
    rw [show Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 by ring, h3]; norm_num
  cases x <;> cases y <;>
    simp [qprob, psi, qvec, Fin.sum_univ_two, Complex.normSq_apply] <;>
    field_simp <;> ring_nf <;>
    nlinarith [h2, h3, h4, h9, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]

/-- **No local hidden-variable model reproduces the quantum Hardy probabilities.**
If a local model assigns to the four relevant events the probabilities predicted by quantum
mechanics for the Hardy state, we get a contradiction. -/
theorem no_local_model_for_quantum_hardy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A B : Bool → Ω → Bool)
    (h₁ : μ {ω | A false ω = true ∧ B true ω = false}
            = ENNReal.ofReal (qprob false true true false))
    (h₂ : μ {ω | A true ω = false ∧ B false ω = true}
            = ENNReal.ofReal (qprob true false false true))
    (h₃ : μ {ω | A true ω = true ∧ B true ω = true}
            = ENNReal.ofReal (qprob true true true true))
    (h₄ : μ {ω | A false ω = true ∧ B false ω = true}
            = ENNReal.ofReal (qprob false false true true)) :
    False := by
  refine hardy_paradox μ A B ?_ ?_ ?_ ?_
  · rw [h₁, qprob_A₁_one_B₂_zero]; simp
  · rw [h₂, qprob_A₂_zero_B₁_one]; simp
  · rw [h₃, qprob_A₂_one_B₂_one]; simp
  · rw [h₄, qprob_first_first]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    norm_num

end QI

