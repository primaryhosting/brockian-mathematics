import Mathlib

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

/-
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dinur's gap amplification and the PCP theorem (statement)

We formalise binary constraint satisfaction instances (`CS.ConstraintGraph`) together with their
`UNSAT` value, and prove the outer, iterative structure of Dinur's proof of the PCP theorem
(`CS.pcp_dinur`): from a single gap-amplification step — preserving perfect completeness,
doubling the `UNSAT` value up to a constant threshold, and increasing the size by at most a
constant factor — iterating logarithmically many times yields a reduction with a constant gap
and polynomial size blowup.  We also check that these hypotheses are not vacuous
(`CS.pcp_dinur_hypotheses_nonvacuous`).
-/

set_option autoImplicit false

namespace CS

/-- A finite constraint graph (a binary constraint satisfaction instance): `numE` constraints,
each attached to an ordered pair of the `numV` variables, each variable taking values in an
alphabet of size `alphSize`, and each constraint given by a decidable binary relation. -/
structure ConstraintGraph where
  /-- number of variables -/
  numV : ℕ
  /-- size of the alphabet -/
  alphSize : ℕ
  /-- number of constraints -/
  numE : ℕ
  /-- the pair of variables each constraint acts on -/
  ends : Fin numE → Fin numV × Fin numV
  /-- the constraint relation attached to each edge -/
  ok : Fin numE → Fin alphSize → Fin alphSize → Bool

/-- The fraction of constraints of `G` violated by the assignment `a`. -/
noncomputable def ConstraintGraph.unsatFrac (G : ConstraintGraph)
    (a : Fin G.numV → Fin G.alphSize) : ℝ :=
  ((Finset.univ.filter
      (fun e : Fin G.numE => ¬ G.ok e (a (G.ends e).1) (a (G.ends e).2))).card : ℝ)
    / (G.numE : ℝ)

/-- The `UNSAT` value of a constraint graph: the least fraction of constraints violated by
any assignment (with the convention that an instance with no constraints has `UNSAT = 0`). -/
noncomputable def ConstraintGraph.unsat (G : ConstraintGraph) : ℝ :=
  ⨅ a : Fin G.numV → Fin G.alphSize, G.unsatFrac a

/-- Iterating the gap-amplification step: after `k` steps the `UNSAT` value is at least
`min (2 ^ k * unsat G) α`. -/
theorem unsat_iterate_lower_bound {T : ConstraintGraph → ConstraintGraph} {alpha : ℝ}
    (halpha : 0 < alpha)
    (hamp : ∀ H : ConstraintGraph, min (2 * H.unsat) alpha ≤ (T H).unsat)
    (G : ConstraintGraph) :
    ∀ k : ℕ, min ((2 : ℝ) ^ k * G.unsat) alpha ≤ (T^[k] G).unsat := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := hamp (T^[k] G)
      rw [Function.iterate_succ_apply']
      refine le_trans ?_ hstep
      refine le_min ?_ (min_le_right _ _)
      rcases le_total ((2 : ℝ) ^ k * G.unsat) alpha with h | h
      · rw [min_eq_left h] at ih
        have hpow : (2 : ℝ) ^ (k + 1) * G.unsat = 2 * ((2 : ℝ) ^ k * G.unsat) := by
          rw [pow_succ]; ring
        have h2 : min ((2 : ℝ) ^ (k + 1) * G.unsat) alpha ≤ 2 * ((2 : ℝ) ^ k * G.unsat) := by
          rw [← hpow]; exact min_le_left _ _
        linarith
      · rw [min_eq_right h] at ih
        have h1 : min ((2 : ℝ) ^ (k + 1) * G.unsat) alpha ≤ alpha := min_le_right _ _
        linarith

/-- Iterating the preservation of perfect completeness. -/
theorem unsat_iterate_eq_zero {T : ConstraintGraph → ConstraintGraph}
    (hcomplete : ∀ H : ConstraintGraph, H.unsat = 0 → (T H).unsat = 0) :
    ∀ (k : ℕ) (H : ConstraintGraph), H.unsat = 0 → (T^[k] H).unsat = 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      intro H hH
      rw [Function.iterate_succ_apply]
      exact ih _ (hcomplete H hH)

/-- Iterating a size-blowup bound. -/
theorem numE_iterate_le {T : ConstraintGraph → ConstraintGraph} {C : ℕ}
    (hsize : ∀ H : ConstraintGraph, (T H).numE ≤ C * H.numE) (G : ConstraintGraph) :
    ∀ k : ℕ, (T^[k] G).numE ≤ C ^ k * G.numE := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      calc (T (T^[k] G)).numE ≤ C * (T^[k] G).numE := hsize _
        _ ≤ C * (C ^ k * G.numE) := by
              exact Nat.mul_le_mul_left C ih
        _ = C ^ (k + 1) * G.numE := by ring

/--
**Dinur's gap amplification and the PCP theorem (statement).**

Assume we are given Dinur's gap-amplification step: a transformation `T` of constraint graphs
(over a fixed alphabet) which

* preserves perfect completeness (`hcomplete`: satisfiable instances stay satisfiable),
* doubles the `UNSAT` value up to a constant threshold `alpha`
  (`hamp`: `unsat (T H) ≥ min (2 * unsat H) alpha`),
* and blows up the size by at most a constant factor `C` (`hsize`).

Then for every unsatisfiable instance `G` there is a number of iterations `k` such that the
composed reduction `T^[k]`

* still maps satisfiable instances to satisfiable instances,
* maps `G` to an instance with constant gap `unsat (T^[k] G) ≥ alpha`,
* increases the size by at most a factor `C ^ k`,
* with `k` logarithmic in `1 / unsat G` (i.e. `2 ^ k ≤ max 1 (2 * alpha / unsat G)`), so that
  the total size blowup `C ^ k` is polynomial.

This is exactly the outer structure of Dinur's proof of the PCP theorem: iterating the
gap-amplification lemma `O(log n)` times turns a decision problem into a constant-gap
constraint satisfaction problem with only a polynomial increase in size.
-/
theorem pcp_dinur {T : ConstraintGraph → ConstraintGraph} {alpha : ℝ} {C : ℕ}
    (halpha : 0 < alpha)
    (hcomplete : ∀ H : ConstraintGraph, H.unsat = 0 → (T H).unsat = 0)
    (hamp : ∀ H : ConstraintGraph, min (2 * H.unsat) alpha ≤ (T H).unsat)
    (hsize : ∀ H : ConstraintGraph, (T H).numE ≤ C * H.numE)
    (G : ConstraintGraph) (hG : 0 < G.unsat) :
    ∃ k : ℕ,
      (∀ H : ConstraintGraph, H.unsat = 0 → (T^[k] H).unsat = 0) ∧
      alpha ≤ (T^[k] G).unsat ∧
      (T^[k] G).numE ≤ C ^ k * G.numE ∧
      (2 : ℝ) ^ k ≤ max 1 (2 * alpha / G.unsat) := by
  -- there is some `k` with `2 ^ k * unsat G ≥ alpha`
  have hex : ∃ k : ℕ, alpha ≤ (2 : ℝ) ^ k * G.unsat := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (R := ℝ) (alpha / G.unsat)
      (by norm_num : (1:ℝ) < 2)
    refine ⟨k, ?_⟩
    rw [div_lt_iff₀ hG] at hk
    linarith
  classical
  obtain ⟨k, hk, hmin⟩ :
      ∃ k : ℕ, alpha ≤ (2 : ℝ) ^ k * G.unsat ∧
        ∀ j, j < k → ¬ alpha ≤ (2 : ℝ) ^ j * G.unsat :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  refine ⟨k, unsat_iterate_eq_zero hcomplete k, ?_, numE_iterate_le hsize G k, ?_⟩
  · have h := unsat_iterate_lower_bound halpha hamp G k
    rwa [min_eq_right hk] at h
  · rcases Nat.eq_zero_or_pos k with h0 | hpos
    · simp [h0]
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hlt : (2 : ℝ) ^ m * G.unsat < alpha := lt_of_not_ge (hmin m (by omega))
      have hb : (2 : ℝ) ^ (m + 1) ≤ 2 * alpha / G.unsat := by
        rw [le_div_iff₀ hG, pow_succ]
        nlinarith
      exact le_trans hb (le_max_right _ _)

/-! ### Non-vacuity of the hypotheses of `CS.pcp_dinur` -/

/-- The empty (hence satisfiable) constraint graph. -/
def trivialCG : ConstraintGraph :=
  { numV := 1, alphSize := 1, numE := 0, ends := Fin.elim0, ok := Fin.elim0 }

/-- A single variable with a single, always violated, constraint: `UNSAT = 1`. -/
def falseCG : ConstraintGraph :=
  { numV := 1, alphSize := 1, numE := 1, ends := fun _ => (0, 0), ok := fun _ _ _ => false }

theorem unsat_eq_zero_of_numE_eq_zero (G : ConstraintGraph) (h : G.numE = 0) : G.unsat = 0 := by
  have : ∀ a : Fin G.numV → Fin G.alphSize, G.unsatFrac a = 0 := by
    intro a
    simp [ConstraintGraph.unsatFrac, h]
  rw [ConstraintGraph.unsat]
  simp only [this]
  rcases isEmpty_or_nonempty (Fin G.numV → Fin G.alphSize) with hI | hI
  · exact Real.iInf_of_isEmpty _
  · exact ciInf_const

theorem unsat_trivialCG : trivialCG.unsat = 0 :=
  unsat_eq_zero_of_numE_eq_zero _ rfl

theorem unsat_falseCG : falseCG.unsat = 1 := by
  have hfrac : ∀ a : Fin falseCG.numV → Fin falseCG.alphSize, falseCG.unsatFrac a = 1 := by
    intro a
    simp [ConstraintGraph.unsatFrac, falseCG]
  haveI : Nonempty (Fin falseCG.numV → Fin falseCG.alphSize) :=
    ⟨fun _ => ⟨0, by norm_num [falseCG]⟩⟩
  rw [ConstraintGraph.unsat]
  simp only [hfrac]
  exact ciInf_const

open Classical in
/-- A (very crude) transformation satisfying all the hypotheses of `CS.pcp_dinur`, witnessing
that they are not contradictory. -/
noncomputable def toyStep (H : ConstraintGraph) : ConstraintGraph :=
  if H.unsat ≤ 0 then trivialCG else falseCG

/-- The hypotheses of `CS.pcp_dinur` are satisfiable: there really are transformations with
perfect completeness, gap doubling up to a threshold, and linear size blowup, together with an
unsatisfiable instance. -/
theorem pcp_dinur_hypotheses_nonvacuous :
    ∃ (T : ConstraintGraph → ConstraintGraph) (alpha : ℝ) (C : ℕ) (G : ConstraintGraph),
      0 < alpha ∧
      (∀ H : ConstraintGraph, H.unsat = 0 → (T H).unsat = 0) ∧
      (∀ H : ConstraintGraph, min (2 * H.unsat) alpha ≤ (T H).unsat) ∧
      (∀ H : ConstraintGraph, (T H).numE ≤ C * H.numE) ∧
      0 < G.unsat := by
  classical
  refine ⟨toyStep, 1, 1, falseCG, one_pos, ?_, ?_, ?_, by rw [unsat_falseCG]; norm_num⟩
  · intro H hH
    simp only [toyStep, if_pos (le_of_eq hH)]
    exact unsat_trivialCG
  · intro H
    by_cases h : H.unsat ≤ 0
    · simp only [toyStep, if_pos h, unsat_trivialCG]
      exact le_trans (min_le_left _ _) (by linarith)
    · simp only [toyStep, if_neg h, unsat_falseCG]
      exact min_le_right _ _
  · intro H
    by_cases h : H.unsat ≤ 0
    · simp [toyStep, if_pos h, trivialCG]
    · have hE : H.numE ≠ 0 := by
        intro h0
        exact h (le_of_eq (unsat_eq_zero_of_numE_eq_zero H h0))
      simp only [toyStep, if_neg h, falseCG, one_mul]
      omega

end CS

