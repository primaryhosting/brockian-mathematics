/-
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
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

namespace CS

/-!
## Dinur's gap amplification

We formalise the *outer structure* of Irit Dinur's proof of the PCP theorem.

Dinur's proof works with **constraint graphs**: a constraint graph `G` has a `size`
(its number of edges/constraints) and an `unsat` value `unsat G ∈ [0,1]`, the minimal
fraction of constraints violated by any assignment.  Two facts about this setting are
axiomatised in `ConstraintSystem`:

* `unsat G ∈ [0,1]`;
* if `G` is *not* satisfiable then at least one of its `size` constraints is violated by
  every assignment, so `unsat G ≥ 1 / size G`.

Dinur's main combinatorial lemma (preprocessing + graph powering + composition with an
inner assignment tester) produces a single **amplification step** `G ↦ step G` which

* blows the size up by at most a constant factor `blowup`;
* preserves satisfiability (`unsat G = 0 → unsat (step G) = 0`);
* *doubles* the unsat value until it reaches a fixed constant `gap`:
  `unsat (step G) ≥ min (2 * unsat G) gap`.

This is packaged in `GapAmplifier`.  The theorem `CS.pcp_dinur` below is the conclusion
of Dinur's argument: iterating such a step logarithmically many times turns any
constraint system into one of *polynomial* size with a *constant* gap — i.e. deciding
satisfiability of the original instance reduces to distinguishing "satisfiable" from
"at least a `gap` fraction of constraints violated", which is the PCP theorem in its
gap (hardness-of-approximation) form.
-/

/-- An abstract system of constraint graphs: each graph has a number of constraints
(`size`) and an unsatisfiability value `unsat ∈ [0,1]`, which — when nonzero — is at
least `1 / size` since at least one constraint must be violated. -/
structure ConstraintSystem where
  /-- The type of constraint graphs. -/
  Graph : Type
  /-- The number of constraints of a graph. -/
  size : Graph → ℕ
  /-- The minimal fraction of constraints violated by an assignment. -/
  unsat : Graph → ℝ
  unsat_nonneg : ∀ G : Graph, 0 ≤ unsat G
  unsat_le_one : ∀ G : Graph, unsat G ≤ 1
  one_div_size_le_unsat : ∀ G : Graph, unsat G ≠ 0 → 1 / (size G : ℝ) ≤ unsat G

/-- Dinur's gap-amplification step for a constraint system: a size-linear,
satisfiability-preserving transformation that doubles the unsat value up to a fixed
constant `gap`. -/
structure GapAmplifier (S : ConstraintSystem) where
  /-- One amplification round. -/
  step : S.Graph → S.Graph
  /-- The constant factor by which one round may increase the size. -/
  blowup : ℕ
  /-- The constant gap that the amplification saturates at. -/
  gap : ℝ
  gap_nonneg : 0 ≤ gap
  gap_le_one : gap ≤ 1
  size_step : ∀ G : S.Graph, S.size (step G) ≤ blowup * S.size G
  unsat_step : ∀ G : S.Graph, min (2 * S.unsat G) gap ≤ S.unsat (step G)
  unsat_step_zero : ∀ G : S.Graph, S.unsat G = 0 → S.unsat (step G) = 0

namespace GapAmplifier

variable {S : ConstraintSystem} (A : GapAmplifier S)

/-- Satisfiability is preserved by any number of amplification rounds. -/
theorem unsat_iterate_zero (k : ℕ) (G : S.Graph) (hG : S.unsat G = 0) :
    S.unsat (A.step^[k] G) = 0 := by
  induction k generalizing G with
  | zero => simpa using hG
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      exact ih _ (A.unsat_step_zero G hG)

/-- After `k` rounds the unsat value has been multiplied by `2 ^ k`, unless it has
already saturated at `gap`. -/
theorem unsat_iterate (k : ℕ) (G : S.Graph) :
    min (2 ^ k * S.unsat G) A.gap ≤ S.unsat (A.step^[k] G) := by
  induction k generalizing G with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      have h1 : min (2 ^ k * S.unsat (A.step G)) A.gap ≤ S.unsat (A.step^[k] (A.step G)) :=
        ih _
      refine le_trans ?_ h1
      have hstep : min (2 * S.unsat G) A.gap ≤ S.unsat (A.step G) := A.unsat_step G
      have hpow : (0:ℝ) ≤ 2 ^ k := by positivity
      rcases le_total (2 * S.unsat G) A.gap with h | h
      · have hle : 2 * S.unsat G ≤ S.unsat (A.step G) := by rwa [min_eq_left h] at hstep
        have : 2 ^ k * (2 * S.unsat G) ≤ 2 ^ k * S.unsat (A.step G) :=
          mul_le_mul_of_nonneg_left hle hpow
        have h2 : (2:ℝ) ^ (k + 1) * S.unsat G = 2 ^ k * (2 * S.unsat G) := by ring
        rw [h2]
        exact min_le_min this le_rfl
      · have hg : A.gap ≤ S.unsat (A.step G) := by rwa [min_eq_right h] at hstep
        have : A.gap ≤ 2 ^ k * S.unsat (A.step G) := by
          calc A.gap = 1 * A.gap := (one_mul _).symm
            _ ≤ 2 ^ k * S.unsat (A.step G) := by
                refine mul_le_mul ?_ hg A.gap_nonneg hpow
                exact one_le_pow₀ (by norm_num)
        exact le_min (le_trans (min_le_right _ _) this) (min_le_right _ _)

end GapAmplifier

/-- `2 ^ (Nat.clog 2 m) ≤ 2 * m` for `m ≥ 1`. -/
theorem two_pow_clog_le (m : ℕ) (hm : 1 ≤ m) : 2 ^ Nat.clog 2 m ≤ 2 * m := by
  rcases eq_or_lt_of_le hm with h | h
  · simp [← h]
  · have hlt : 2 ^ (Nat.clog 2 m - 1) < m := Nat.pow_pred_clog_lt_self (by norm_num) h
    have hk : 1 ≤ Nat.clog 2 m := Nat.clog_pos (by norm_num) h
    have : 2 ^ Nat.clog 2 m = 2 * 2 ^ (Nat.clog 2 m - 1) := by
      conv_lhs => rw [show Nat.clog 2 m = (Nat.clog 2 m - 1) + 1 by omega]
      ring
    omega

/--
**Dinur's gap amplification / the PCP theorem (gap form).**

Let `S` be a system of constraint graphs and let `A` be a gap amplifier for `S`
(this is Dinur's main lemma: preprocessing, graph powering and composition with an
assignment tester yield a size-linear, satisfiability-preserving step that doubles the
unsat value up to a constant `gap`).

Then every constraint graph `G` can be transformed into a graph `G'` whose size is
**polynomial** in the size of `G` (bounded by `(2 · size G) ^ ⌈log₂ blowup⌉ · size G`)
such that

* if `G` is satisfiable, so is `G'`;
* if `G` is unsatisfiable, then *every* assignment to `G'` violates at least a `gap`
  fraction of its constraints.

Thus satisfiability of `G` reduces, in polynomial size, to a *constant-gap* promise
problem — the hardness-of-approximation form of the PCP theorem.
-/
theorem pcp_dinur (S : ConstraintSystem) (A : GapAmplifier S) (G : S.Graph)
    (hG : 1 ≤ S.size G) :
    ∃ G' : S.Graph,
      S.size G' ≤ (2 * S.size G) ^ Nat.clog 2 A.blowup * S.size G ∧
      (S.unsat G = 0 → S.unsat G' = 0) ∧
      (S.unsat G ≠ 0 → A.gap ≤ S.unsat G') := by
  set m : ℕ := S.size G with hm
  set k : ℕ := Nat.clog 2 m with hk
  refine ⟨A.step^[k] G, ?_, ?_, ?_⟩
  · -- size bound
    have hsize : ∀ (j : ℕ) (H : S.Graph), S.size (A.step^[j] H) ≤ A.blowup ^ j * S.size H := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
          intro H
          rw [Function.iterate_succ_apply]
          calc S.size (A.step^[j] (A.step H)) ≤ A.blowup ^ j * S.size (A.step H) := ih _
            _ ≤ A.blowup ^ j * (A.blowup * S.size H) :=
                Nat.mul_le_mul_left _ (A.size_step H)
            _ = A.blowup ^ (j + 1) * S.size H := by ring
    refine le_trans (hsize k G) ?_
    refine Nat.mul_le_mul_right _ ?_
    -- `blowup ^ k ≤ (2 * m) ^ clog 2 blowup`
    have hb : A.blowup ≤ 2 ^ Nat.clog 2 A.blowup := Nat.le_pow_clog (by norm_num) _
    calc A.blowup ^ k ≤ (2 ^ Nat.clog 2 A.blowup) ^ k := Nat.pow_le_pow_left hb k
      _ = (2 ^ k) ^ Nat.clog 2 A.blowup := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (2 * m) ^ Nat.clog 2 A.blowup :=
          Nat.pow_le_pow_left (two_pow_clog_le m hG) _
  · intro h
    exact A.unsat_iterate_zero k G h
  · intro h
    have hlb : 1 / (m : ℝ) ≤ S.unsat G := S.one_div_size_le_unsat G h
    have hmpos : (0:ℝ) < (m : ℝ) := by exact_mod_cast hG
    have hpow : (m : ℝ) ≤ 2 ^ k := by
      have : m ≤ 2 ^ k := Nat.le_pow_clog (by norm_num) m
      exact_mod_cast this
    have h1 : (1:ℝ) ≤ 2 ^ k * S.unsat G := by
      calc (1:ℝ) = (m : ℝ) * (1 / (m : ℝ)) := by field_simp
        _ ≤ 2 ^ k * S.unsat G := by
            refine mul_le_mul hpow hlb (by positivity) (by positivity)
    have := A.unsat_iterate k G
    refine le_trans ?_ this
    exact le_min (le_trans A.gap_le_one h1) le_rfl

/-! ### The hypotheses are consistent

A concrete constraint system with a gap amplifier of gap `1`, showing that
`CS.pcp_dinur` is not vacuous. -/

/-- A toy constraint system: graphs are `Option ℕ`, `none` is a satisfiable graph and
`some n` is an unsatisfiable graph whose unsat value is `min (2 ^ n / 2) 1`. -/
noncomputable def toySystem : ConstraintSystem where
  Graph := Option ℕ
  size := fun _ => 2
  unsat := fun G => match G with
    | none => 0
    | some n => min (2 ^ n / 2) 1
  unsat_nonneg := by
    rintro (_ | n)
    · simp
    · exact le_min (by positivity) (by norm_num)
  unsat_le_one := by
    rintro (_ | n) <;> simp
  one_div_size_le_unsat := by
    rintro (_ | n) h
    · simp at h
    · have : (1:ℝ) / 2 ≤ 2 ^ n / 2 := by
        have : (1:ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        linarith
      simpa using le_min this (by norm_num)

/-- A gap amplifier for `toySystem` with gap `1`. -/
noncomputable def toyAmplifier : GapAmplifier toySystem where
  step := fun G => match G with
    | none => none
    | some n => some (n + 1)
  blowup := 1
  gap := 1
  gap_nonneg := by norm_num
  gap_le_one := le_rfl
  size_step := by rintro (_ | n) <;> simp [toySystem]
  unsat_step := by
    rintro (_ | n)
    · simp [toySystem]
    · show min (2 * min ((2:ℝ) ^ n / 2) 1) 1 ≤ min ((2:ℝ) ^ (n + 1) / 2) 1
      have h2 : (2:ℝ) * min ((2:ℝ) ^ n / 2) 1 = min ((2:ℝ) ^ (n + 1) / 2) 2 := by
        rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
        congr 1 <;> ring
      rw [h2]
      refine le_min ?_ (min_le_right _ _)
      exact le_trans (min_le_left _ _) (min_le_left _ _)
  unsat_step_zero := by
    rintro (_ | n) h
    · simp [toySystem]
    · exfalso
      have : (0:ℝ) < min ((2:ℝ) ^ n / 2) 1 := by
        refine lt_min (by positivity) (by norm_num)
      simp only [toySystem] at h
      linarith

example : toyAmplifier.gap = 1 := rfl

end CS

