/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Scope of the formalisation

The ensemble is a *commuting* (equivalently: simultaneously diagonalizable) family of states,
measured by a POVM that is diagonal in the same eigenbasis.  Concretely, a state `ρₓ` is recorded
by its spectrum `r x : Z → ℝ` in a fixed orthonormal eigenbasis indexed by `Z`, a POVM element
`E y` by its diagonal `Z → ℝ`, and the Born rule is `Pr[y | x] = ∑ z, r x z * E y z`.  In this
situation the von Neumann entropy is the Shannon entropy of the spectrum, so the Holevo quantity
`χ = S(∑ₓ pₓ ρₓ) - ∑ₓ pₓ S(ρₓ)` and the accessible information are the ones defined below, and
`QI.holevo_bound` is the Holevo inequality `I_acc ≤ χ` for such ensembles.  The bound is tight:
for a uniform ensemble of two orthogonal states, measured in their own basis, both sides equal
`log 2`.  The fully general (non-commuting) case is not covered here.
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

set_option grind.warning false

namespace QI

/-! ## The log-sum inequality -/

/-- **Log-sum inequality**: for nonnegative weights `a`, `b` on a finite set such that `b i = 0`
forces `a i = 0` (absolute continuity), one has
`(∑ a) * log ((∑ a) / (∑ b)) ≤ ∑ a i * log (a i / b i)`. -/
theorem log_sum_inequality {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hac : ∀ i ∈ s, b i = 0 → a i = 0) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
      ≤ ∑ i ∈ s, a i * Real.log (a i / b i) := by
  set A := ∑ i ∈ s, a i with hA
  set B := ∑ i ∈ s, b i with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg ha
  have hB0 : 0 ≤ B := Finset.sum_nonneg hb
  rcases eq_or_lt_of_le hA0 with hA' | hApos
  · -- A = 0 : every `a i = 0`
    have hzero : ∀ i ∈ s, a i = 0 := by
      intro i hi
      have := (Finset.sum_eq_zero_iff_of_nonneg ha).1 hA'.symm i hi
      exact this
    have h1 : A * Real.log (A / B) = 0 := by rw [← hA']; ring
    rw [h1]
    refine le_of_eq ?_
    symm
    refine Finset.sum_eq_zero ?_
    intro i hi
    rw [hzero i hi]; ring
  · have hBpos : 0 < B := by
      rcases eq_or_lt_of_le hB0 with hB' | h
      · exfalso
        have hzero : ∀ i ∈ s, b i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hb).1 hB'.symm
        have : A = 0 := by
          rw [hA]
          exact Finset.sum_eq_zero fun i hi => hac i hi (hzero i hi)
        exact absurd this (ne_of_gt hApos)
      · exact h
    -- pointwise bound
    have key : ∀ i ∈ s, a i * Real.log (A / B) + (a i - A * b i / B)
        ≤ a i * Real.log (a i / b i) := by
      intro i hi
      rcases eq_or_lt_of_le (ha i hi) with hai | haipos
      · -- a i = 0
        have hai' : a i = 0 := hai.symm
        rw [hai']
        have : 0 ≤ A * b i / B := div_nonneg (mul_nonneg hA0 (hb i hi)) hB0
        simp only [zero_mul, zero_sub, zero_add]
        linarith
      · have hbipos : 0 < b i := by
          rcases eq_or_lt_of_le (hb i hi) with hbi | h
          · exact absurd (hac i hi hbi.symm) (ne_of_gt haipos)
          · exact h
        set t := (a i * B) / (b i * A) with ht
        have htpos : 0 < t := by
          rw [ht]; positivity
        have hlog : Real.log (1 / t) ≤ 1 / t - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        have hlogt : 1 - 1 / t ≤ Real.log t := by
          rw [Real.log_div one_ne_zero (ne_of_gt htpos)] at hlog
          simp only [Real.log_one, zero_sub] at hlog
          linarith
        have hinvt : 1 / t = (b i * A) / (a i * B) := by
          rw [ht]; rw [one_div, inv_div]
        have hlogsplit : Real.log t = Real.log (a i / b i) - Real.log (A / B) := by
          rw [ht]
          rw [show (a i * B) / (b i * A) = (a i / b i) / (A / B) by field_simp]
          rw [Real.log_div (by positivity) (by positivity)]
        have h1 : a i * (1 - 1 / t) ≤ a i * Real.log t := by
          exact mul_le_mul_of_nonneg_left hlogt (le_of_lt haipos)
        have h2 : a i * (1 - 1 / t) = a i - A * b i / B := by
          rw [hinvt]
          field_simp
        rw [h2, hlogsplit] at h1
        linarith
    have hsum := Finset.sum_le_sum key
    have hleft : ∑ i ∈ s, (a i * Real.log (A / B) + (a i - A * b i / B))
        = A * Real.log (A / B) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib]
      have : ∑ i ∈ s, A * b i / B = A := by
        rw [show (fun i => A * b i / B) = (fun i => (A / B) * b i) by
          funext i; ring]
        rw [← Finset.mul_sum, ← hB]
        field_simp
      rw [this, ← hA]
      ring
    rw [hleft] at hsum
    exact hsum

/-! ## Ensembles, POVMs and the entropic quantities

We work with a family of states that is simultaneously diagonal in a fixed orthonormal basis
indexed by `Z`, together with a POVM that is diagonal in the same basis.  A state is therefore
recorded by its spectrum `r x : Z → ℝ` (a probability vector, i.e. the diagonal of the density
matrix), and a POVM by its diagonal entries `E y : Z → ℝ`.  In this commuting situation the von
Neumann entropy of a state is the Shannon entropy of its spectrum, the Born rule reads
`Pr[y | x] = ∑ z, r x z * E y z`, and the Holevo quantity is
`χ = S(∑ₓ pₓ ρₓ) - ∑ₓ pₓ S(ρₓ)` as usual. -/

variable {X Y Z : Type*}

/-- Shannon (= von Neumann, in the common eigenbasis) entropy of a spectrum `r`. -/
noncomputable def entropy [Fintype Z] (r : Z → ℝ) : ℝ := ∑ z, Real.negMulLog (r z)

/-- The average state `∑ₓ pₓ ρₓ` of the ensemble, given by its spectrum. -/
noncomputable def avgState [Fintype X] (p : X → ℝ) (r : X → Z → ℝ) (z : Z) : ℝ :=
  ∑ x, p x * r x z

/-- The Holevo quantity `χ = S(∑ₓ pₓ ρₓ) - ∑ₓ pₓ S(ρₓ)` of the ensemble `(p, r)`. -/
noncomputable def holevoChi [Fintype X] [Fintype Z] (p : X → ℝ) (r : X → Z → ℝ) : ℝ :=
  entropy (avgState p r) - ∑ x, p x * entropy (r x)

/-- `E` is a POVM with outcomes in `Y`: positive elements summing to the identity. -/
def IsPOVM [Fintype Y] (E : Y → Z → ℝ) : Prop :=
  (∀ y z, 0 ≤ E y z) ∧ ∀ z, ∑ y, E y z = 1

/-- Born rule: the probability of outcome `y` when measuring the state `ρₓ` with the POVM `E`. -/
noncomputable def outProb [Fintype Z] (r : X → Z → ℝ) (E : Y → Z → ℝ) (x : X) (y : Y) : ℝ :=
  ∑ z, r x z * E y z

/-- Classical mutual information of the joint distribution `p x * q x y`. -/
noncomputable def mutualInfo [Fintype X] [Fintype Y] (p : X → ℝ) (q : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, p x * q x y * Real.log (q x y / ∑ x', p x' * q x' y)

/-- The accessible information of the ensemble `(p, r)` with measurement outcomes in `Y`:
the supremum, over all POVMs with outcome set `Y`, of the mutual information between the
label `X` and the measurement result. -/
noncomputable def accessibleInfo (Y : Type*) [Fintype Y] [Fintype X] [Fintype Z]
    (p : X → ℝ) (r : X → Z → ℝ) : ℝ :=
  sSup {I : ℝ | ∃ E : Y → Z → ℝ, IsPOVM E ∧ I = mutualInfo p (outProb r E)}

/-! ## The Holevo bound -/

section
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- The Holevo quantity is the mutual information between the label and the (unmeasured)
eigenbasis index. -/
theorem holevoChi_eq (p : X → ℝ) (r : X → Z → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hr0 : ∀ x z, 0 ≤ r x z) :
    holevoChi p r = ∑ x, ∑ z, p x * r x z * Real.log (r x z / avgState p r z) := by
  have hterm : ∀ x : X, ∀ z : Z,
      p x * r x z * Real.log (r x z / avgState p r z)
        = p x * r x z * Real.log (r x z) - p x * r x z * Real.log (avgState p r z) := by
    intro x z
    rcases eq_or_lt_of_le (mul_nonneg (hp0 x) (hr0 x z)) with h | h
    · rw [← h]; ring
    · have hpx : p x ≠ 0 := by
        intro h0; rw [h0] at h; simp at h
      have hrxz : r x z ≠ 0 := by
        intro h0; rw [h0] at h; simp at h
      have havg : avgState p r z ≠ 0 := by
        intro h0
        have hnn : ∀ x' ∈ Finset.univ, 0 ≤ p x' * r x' z := fun x' _ =>
          mul_nonneg (hp0 x') (hr0 x' z)
        have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 x (Finset.mem_univ x)
        exact absurd this (ne_of_gt h)
      rw [Real.log_div hrxz havg]; ring
  calc holevoChi p r
      = (∑ z, Real.negMulLog (avgState p r z)) - ∑ x, p x * ∑ z, Real.negMulLog (r x z) := rfl
    _ = ∑ x, ∑ z, (p x * r x z * Real.log (r x z) - p x * r x z * Real.log (avgState p r z)) := by
        have h1 : ∀ x : X, p x * ∑ z, Real.negMulLog (r x z)
            = ∑ z, -(p x * r x z * Real.log (r x z)) := by
          intro x
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro z _
          rw [Real.negMulLog]
          ring
        have h2 : ∀ z : Z, Real.negMulLog (avgState p r z)
            = ∑ x, -(p x * r x z * Real.log (avgState p r z)) := by
          intro z
          rw [Real.negMulLog, avgState, ← Finset.sum_neg_distrib, Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro x _
          ring
        simp only [h1, h2]
        rw [Finset.sum_comm (s := (Finset.univ : Finset Z)) (t := (Finset.univ : Finset X))]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro x _
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro z _
        ring
    _ = ∑ x, ∑ z, p x * r x z * Real.log (r x z / avgState p r z) := by
        refine Finset.sum_congr rfl ?_
        intro x _
        refine Finset.sum_congr rfl ?_
        intro z _
        rw [hterm x z]

/-- **Holevo bound, per measurement**: for any POVM, the mutual information between the label
and the outcome is at most the Holevo quantity of the ensemble. -/
theorem mutualInfo_le_holevoChi (p : X → ℝ) (r : X → Z → ℝ) (E : Y → Z → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hr0 : ∀ x z, 0 ≤ r x z) (hE : IsPOVM E) :
    mutualInfo p (outProb r E) ≤ holevoChi p r := by
  obtain ⟨hE0, hE1⟩ := hE
  set q : X → Y → ℝ := outProb r E with hq
  set avg : Z → ℝ := avgState p r with havg
  have havg0 : ∀ z, 0 ≤ avg z := fun z =>
    Finset.sum_nonneg fun x _ => mul_nonneg (hp0 x) (hr0 x z)
  have hq0 : ∀ x y, 0 ≤ q x y := fun x y =>
    Finset.sum_nonneg fun z _ => mul_nonneg (hr0 x z) (hE0 y z)
  -- marginal of the outcome
  have hmarg : ∀ y : Y, (∑ x', p x' * q x' y) = ∑ z, avg z * E y z := by
    intro y
    rw [hq]
    simp only [outProb, havg, avgState, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro z _
    refine Finset.sum_congr rfl ?_
    intro x _
    ring
  -- the key per-(x,y) estimate coming from the log-sum inequality
  have key : ∀ x : X, ∀ y : Y,
      p x * q x y * Real.log (q x y / ∑ x', p x' * q x' y)
        ≤ ∑ z, p x * r x z * E y z * Real.log (r x z / avg z) := by
    intro x y
    have hsa : (∑ z, p x * r x z * E y z) = p x * q x y := by
      rw [hq]; simp only [outProb, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro z _; ring
    have hsb : (∑ z, p x * avg z * E y z) = p x * ∑ x', p x' * q x' y := by
      rw [hmarg y, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro z _; ring
    have hls := log_sum_inequality (Finset.univ : Finset Z)
      (fun z => p x * r x z * E y z) (fun z => p x * avg z * E y z)
      (fun z _ => mul_nonneg (mul_nonneg (hp0 x) (hr0 x z)) (hE0 y z))
      (fun z _ => mul_nonneg (mul_nonneg (hp0 x) (havg0 z)) (hE0 y z))
      (by
        intro z _ hbz
        simp only at hbz ⊢
        rcases eq_or_lt_of_le (hp0 x) with h | hpx
        · rw [← h]; ring
        rcases eq_or_lt_of_le (hE0 y z) with h | hEyz
        · rw [← h]; ring
        have havgz : avg z = 0 := by
          by_contra hne
          have : p x * avg z * E y z ≠ 0 := by
            have := havg0 z
            have hpos : 0 < avg z := lt_of_le_of_ne this (Ne.symm hne)
            positivity
          exact this hbz
        have hrxz : p x * r x z = 0 := by
          have hnn : ∀ x' ∈ Finset.univ, 0 ≤ p x' * r x' z := fun x' _ =>
            mul_nonneg (hp0 x') (hr0 x' z)
          exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 havgz x (Finset.mem_univ x)
        rw [hrxz]; ring)
    rw [hsa, hsb] at hls
    -- rewrite both sides
    have hlhs : p x * q x y * Real.log (q x y / ∑ x', p x' * q x' y)
        ≤ p x * q x y * Real.log ((p x * q x y) / (p x * ∑ x', p x' * q x' y)) := by
      rcases eq_or_lt_of_le (hp0 x) with h | hpx
      · rw [← h]; simp
      · rw [mul_div_mul_left _ _ (ne_of_gt hpx)]
    refine le_trans hlhs (le_trans hls (le_of_eq ?_))
    refine Finset.sum_congr rfl ?_
    intro z _
    simp only
    rcases eq_or_lt_of_le (hp0 x) with h | hpx
    · rw [← h]; ring
    rcases eq_or_lt_of_le (hE0 y z) with h | hEyz
    · rw [← h]; ring
    have hc : (p x * E y z) ≠ 0 := by positivity
    have e1 : p x * r x z * E y z = (p x * E y z) * r x z := by ring
    have e2 : p x * avg z * E y z = (p x * E y z) * avg z := by ring
    rw [e1, e2, mul_div_mul_left _ _ hc]
  -- assemble
  have step1 : mutualInfo p q ≤ ∑ x, ∑ y, ∑ z, p x * r x z * E y z * Real.log (r x z / avg z) := by
    refine Finset.sum_le_sum ?_
    intro x _
    exact Finset.sum_le_sum fun y _ => key x y
  have step2 : ∀ x : X, (∑ y, ∑ z, p x * r x z * E y z * Real.log (r x z / avg z))
      = ∑ z, p x * r x z * Real.log (r x z / avg z) := by
    intro x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro z _
    have : ∀ y : Y, p x * r x z * E y z * Real.log (r x z / avg z)
        = (p x * r x z * Real.log (r x z / avg z)) * E y z := by
      intro y; ring
    simp only [this]
    rw [← Finset.mul_sum, hE1 z, mul_one]
  simp only [step2] at step1
  rw [holevoChi_eq p r hp0 hr0]
  exact step1

end

/-- **The Holevo bound.**  For a quantum ensemble `{pₓ, ρₓ}` (here: a family of states that is
simultaneously diagonalizable, recorded by the spectra `r x` in a common eigenbasis indexed by
`Z`), the accessible information — the supremum over all POVMs of the mutual information between
the label `x` and the measurement outcome — is at most the Holevo quantity
`χ = S(∑ₓ pₓ ρₓ) - ∑ₓ pₓ S(ρₓ)`.

(The normalisation hypotheses `hp1` and `hr1` express that `p` is a probability distribution and
each `ρₓ` is a state; the proof in fact only uses positivity.) -/
theorem holevo_bound {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Nonempty Y]
    [DecidableEq Y] (p : X → ℝ) (r : X → Z → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hr0 : ∀ x z, 0 ≤ r x z) (hr1 : ∀ x, ∑ z, r x z = 1) :
    accessibleInfo Y p r ≤ holevoChi p r := by
  refine csSup_le ?_ ?_
  · -- the set of achievable mutual informations is nonempty: take a trivial POVM
    refine ⟨mutualInfo p (outProb r (fun y _ => if y = Classical.arbitrary Y then 1 else 0)),
      ⟨_, ⟨?_, ?_⟩, rfl⟩⟩
    · intro y z
      by_cases h : y = Classical.arbitrary Y <;> simp [h]
    · intro z
      simp
  · rintro I ⟨E, hE, rfl⟩
    exact mutualInfo_le_holevoChi p r E hp0 hr0 hE

/-! ## Tightness

The uniform ensemble of two orthogonal states, measured in their own basis, saturates the
bound: both the accessible information and the Holevo quantity equal `log 2`. -/

/-- Uniform distribution on two labels. -/
noncomputable def exampleProb : Bool → ℝ := fun _ => 1 / 2

/-- Two orthogonal pure states (spectra `(1,0)` and `(0,1)`). -/
noncomputable def exampleStates : Bool → Bool → ℝ := fun x z => if x = z then 1 else 0

/-- The projective measurement in the common eigenbasis. -/
noncomputable def exampleMeas : Bool → Bool → ℝ := fun y z => if y = z then 1 else 0

theorem exampleMeas_isPOVM : IsPOVM exampleMeas := by
  constructor
  · intro y z; cases y <;> cases z <;> simp [exampleMeas]
  · intro z; cases z <;> simp [exampleMeas]

theorem exampleProb_nonneg : ∀ x, 0 ≤ exampleProb x := by
  intro x; cases x <;> norm_num [exampleProb]

theorem exampleStates_nonneg : ∀ x z, 0 ≤ exampleStates x z := by
  intro x z; cases x <;> cases z <;> simp [exampleStates]

theorem holevoChi_example : holevoChi exampleProb exampleStates = Real.log 2 := by
  have havg : avgState exampleProb exampleStates = fun _ => (1 / 2 : ℝ) := by
    funext z; cases z <;> simp [avgState, exampleProb, exampleStates]
  rw [holevoChi, havg]
  simp [entropy, Real.negMulLog, exampleStates, exampleProb]

theorem mutualInfo_example :
    mutualInfo exampleProb (outProb exampleStates exampleMeas) = Real.log 2 := by
  have h : outProb exampleStates exampleMeas = fun x y => if x = y then (1 : ℝ) else 0 := by
    funext x y; cases x <;> cases y <;> simp [outProb, exampleStates, exampleMeas]
  rw [h]
  simp [mutualInfo, exampleProb]

/-- The Holevo bound is tight. -/
theorem accessibleInfo_example : accessibleInfo Bool exampleProb exampleStates = Real.log 2 := by
  refine le_antisymm ?_ ?_
  · have h := holevo_bound (Y := Bool) exampleProb exampleStates exampleProb_nonneg
      (by simp [exampleProb]) exampleStates_nonneg
      (fun x => by cases x <;> simp [exampleStates])
    rw [holevoChi_example] at h
    exact h
  · rw [← mutualInfo_example]
    refine le_csSup ⟨holevoChi exampleProb exampleStates, ?_⟩
      ⟨exampleMeas, exampleMeas_isPOVM, rfl⟩
    rintro I ⟨E, hE, rfl⟩
    exact mutualInfo_le_holevoChi exampleProb exampleStates E exampleProb_nonneg
      exampleStates_nonneg hE

end QI

