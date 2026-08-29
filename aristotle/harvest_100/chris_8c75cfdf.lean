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

/-- A finite constraint satisfaction problem (CSP) instance: `numVars` variables taking
values in an alphabet of size `alphabetSize`, together with a nonempty list of Boolean
constraints on assignments. -/
structure CSP where
  numVars : ℕ
  alphabetSize : ℕ
  alphabet_pos : 0 < alphabetSize
  constraints : List ((Fin numVars → Fin alphabetSize) → Bool)
  constraints_ne : constraints ≠ []

namespace CSP

/-- Assignments of the CSP `G`. -/
def Assignment (G : CSP) : Type := Fin G.numVars → Fin G.alphabetSize

instance (G : CSP) : Fintype G.Assignment := by
  have : NeZero G.alphabetSize := ⟨G.alphabet_pos.ne'⟩
  unfold Assignment
  infer_instance

instance (G : CSP) : Nonempty G.Assignment := by
  have : NeZero G.alphabetSize := ⟨G.alphabet_pos.ne'⟩
  unfold Assignment
  infer_instance

instance (G : CSP) : DecidableEq G.Assignment := by
  have : NeZero G.alphabetSize := ⟨G.alphabet_pos.ne'⟩
  unfold Assignment
  infer_instance

/-- The number of constraints of `G` (its size). -/
def size (G : CSP) : ℕ := G.constraints.length

/-- The number of constraints of `G` violated by the assignment `a`. -/
def numFalsified (G : CSP) (a : G.Assignment) : ℕ :=
  G.constraints.countP (fun c => !(c a))

/-- `G` is satisfiable if some assignment satisfies all of its constraints. -/
def Satisfiable (G : CSP) : Prop := ∃ a : G.Assignment, ∀ c ∈ G.constraints, c a = true

/-- The unsat value of `G`: the least fraction of constraints violated by an assignment. -/
noncomputable def unsat (G : CSP) : ℝ :=
  (Finset.univ : Finset G.Assignment).inf' Finset.univ_nonempty
    (fun a => (G.numFalsified a : ℝ) / G.size)

theorem size_pos (G : CSP) : 0 < G.size :=
  List.length_pos_iff.mpr G.constraints_ne

theorem numFalsified_le_size (G : CSP) (a : G.Assignment) : G.numFalsified a ≤ G.size :=
  List.countP_le_length

theorem exists_unsat_eq (G : CSP) :
    ∃ a : G.Assignment, G.unsat = (G.numFalsified a : ℝ) / G.size := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := G.Assignment))
    (fun a => (G.numFalsified a : ℝ) / G.size)
  exact ⟨a, ha⟩

theorem unsat_le (G : CSP) (a : G.Assignment) :
    G.unsat ≤ (G.numFalsified a : ℝ) / G.size :=
  Finset.inf'_le _ (Finset.mem_univ a)

theorem unsat_nonneg (G : CSP) : 0 ≤ G.unsat := by
  obtain ⟨a, ha⟩ := G.exists_unsat_eq
  rw [ha]
  positivity

theorem unsat_le_one (G : CSP) : G.unsat ≤ 1 := by
  obtain ⟨a, ha⟩ := G.exists_unsat_eq
  rw [ha]
  rw [div_le_one (by exact_mod_cast G.size_pos)]
  exact_mod_cast G.numFalsified_le_size a

theorem numFalsified_eq_zero_iff (G : CSP) (a : G.Assignment) :
    G.numFalsified a = 0 ↔ ∀ c ∈ G.constraints, c a = true := by
  unfold numFalsified
  rw [List.countP_eq_zero]
  constructor
  · intro h c hc
    have := h c hc
    simpa using this
  · intro h c hc
    simp [h c hc]

theorem unsat_eq_zero_iff (G : CSP) : G.unsat = 0 ↔ G.Satisfiable := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := G.exists_unsat_eq
    refine ⟨a, ?_⟩
    rw [← G.numFalsified_eq_zero_iff a]
    have hs : (0 : ℝ) < G.size := by exact_mod_cast G.size_pos
    have hz : ((G.numFalsified a : ℝ)) / G.size = 0 := by rw [← ha, h]
    have := (div_eq_zero_iff.mp hz).resolve_right hs.ne'
    exact_mod_cast this
  · rintro ⟨a, ha⟩
    have h0 : G.numFalsified a = 0 := (G.numFalsified_eq_zero_iff a).mpr ha
    have hle : G.unsat ≤ 0 := by
      have := G.unsat_le a
      rwa [h0, Nat.cast_zero, zero_div] at this
    exact le_antisymm hle G.unsat_nonneg

/-- An unsatisfiable CSP violates at least one out of `size` constraints, so its unsat value
is at least `1 / size`. -/
theorem inv_size_le_unsat (G : CSP) (h : ¬ G.Satisfiable) : (1 : ℝ) / G.size ≤ G.unsat := by
  obtain ⟨a, ha⟩ := G.exists_unsat_eq
  have hs : (0 : ℝ) < G.size := by exact_mod_cast G.size_pos
  have h1 : 1 ≤ G.numFalsified a := by
    rcases Nat.eq_zero_or_pos (G.numFalsified a) with h0 | h0
    · exact absurd ⟨a, (G.numFalsified_eq_zero_iff a).mp h0⟩ h
    · exact h0
  rw [ha]
  have : (1 : ℝ) ≤ (G.numFalsified a : ℝ) := by exact_mod_cast h1
  gcongr

end CSP

/-- A one-constraint CSP that is satisfiable. -/
def trivSat : CSP :=
  { numVars := 0, alphabetSize := 1, alphabet_pos := Nat.one_pos,
    constraints := [fun _ => true], constraints_ne := by simp }

/-- A one-constraint CSP that is unsatisfiable, with unsat value `1`. -/
def trivUnsat : CSP :=
  { numVars := 0, alphabetSize := 1, alphabet_pos := Nat.one_pos,
    constraints := [fun _ => false], constraints_ne := by simp }

theorem trivSat_satisfiable : trivSat.Satisfiable := by
  refine ⟨Classical.arbitrary _, ?_⟩
  intro c hc
  simp [trivSat] at hc
  simp [hc]

theorem trivSat_unsat : trivSat.unsat = 0 :=
  (CSP.unsat_eq_zero_iff _).mpr trivSat_satisfiable

theorem trivSat_size : trivSat.size = 1 := rfl

theorem trivUnsat_size : trivUnsat.size = 1 := rfl

theorem trivUnsat_unsat : trivUnsat.unsat = 1 := by
  obtain ⟨a, ha⟩ := trivUnsat.exists_unsat_eq
  have hnf : trivUnsat.numFalsified a = 1 := by
    simp [CSP.numFalsified, trivUnsat]
  rw [ha, hnf, trivUnsat_size]
  norm_num

/-- The hypotheses of `CS.pcp_dinur` are consistent: some transformation satisfies all of them.
This rules out the statement being vacuously true. -/
theorem amplification_hypotheses_consistent :
    ∃ (amp : CSP → CSP) (C : ℕ) (α : ℝ), 0 < α ∧ α ≤ 1 ∧
      (∀ G : CSP, (amp G).size ≤ C * G.size) ∧
      (∀ G : CSP, G.Satisfiable → (amp G).Satisfiable) ∧
      (∀ G : CSP, min α (2 * G.unsat) ≤ (amp G).unsat) := by
  refine ⟨fun G => if G.Satisfiable then trivSat else trivUnsat, 1, 1, one_pos, le_rfl,
    ?_, ?_, ?_⟩
  · intro G
    have h := G.size_pos
    by_cases hG : G.Satisfiable <;> simp [hG, trivSat_size, trivUnsat_size] <;> omega
  · intro G hG
    simpa [hG] using trivSat_satisfiable
  · intro G
    by_cases hG : G.Satisfiable
    · have h0 : G.unsat = 0 := (CSP.unsat_eq_zero_iff _).mpr hG
      simp [hG, h0, trivSat_unsat]
    · simp only [hG, if_false, trivUnsat_unsat]
      exact min_le_left _ _

variable {amp : CSP → CSP}

/-- Iterating a size-`C`-blow-up transformation `t` times blows the size up by at most `C ^ t`. -/
theorem size_iterate_le {C : ℕ} (hsize : ∀ G : CSP, (amp G).size ≤ C * G.size)
    (G : CSP) (t : ℕ) : (amp^[t] G).size ≤ C ^ t * G.size := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc (amp (amp^[n] G)).size ≤ C * (amp^[n] G).size := hsize _
      _ ≤ C * (C ^ n * G.size) := Nat.mul_le_mul_left _ ih
      _ = C ^ (n + 1) * G.size := by ring

/-- Completeness is preserved along the iteration. -/
theorem satisfiable_iterate (hcomp : ∀ G : CSP, G.Satisfiable → (amp G).Satisfiable)
    (G : CSP) (t : ℕ) (h : G.Satisfiable) : (amp^[t] G).Satisfiable := by
  induction t with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hcomp _ ih

/-- Iterating the gap-amplification step `t` times multiplies the unsat value by `2 ^ t`,
up to the cap `α`. -/
theorem gap_iterate {α : ℝ} (hα0 : 0 < α)
    (hgap : ∀ G : CSP, min α (2 * G.unsat) ≤ (amp G).unsat) (G : CSP) (t : ℕ) :
    min α (2 ^ t * G.unsat) ≤ (amp^[t] G).unsat := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hstep : min α (2 ^ (n + 1) * G.unsat) ≤ 2 * min α (2 ^ n * G.unsat) := by
      have h2m : 2 * min α (2 ^ n * G.unsat) = min (2 * α) (2 ^ (n + 1) * G.unsat) := by
        rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        ring
      rw [h2m]
      exact min_le_min (by linarith) le_rfl
    calc min α (2 ^ (n + 1) * G.unsat)
        ≤ min α (2 * (amp^[n] G).unsat) :=
          le_min (min_le_left _ _) (le_trans hstep (by linarith [ih]))
      _ ≤ (amp (amp^[n] G)).unsat := hgap _

/-- **Dinur's gap amplification proof of the PCP theorem.**

Assume a gap-amplification step `amp` on CSP instances with parameters `C` (size blow-up) and
`α > 0` (gap cap), which
* increases the size by at most a constant factor `C`;
* maps satisfiable instances to satisfiable instances (completeness);
* at least doubles the unsat value, up to the cap `α` (soundness / gap amplification).

Then iterating `amp` for `log₂(size) + 1` rounds is a gap reduction with constant gap `α`:
the resulting instance has size polynomial in the original size, it is satisfiable whenever the
original one is, and its unsat value is at least the absolute constant `α` whenever the original
instance is unsatisfiable.  This is exactly the reduction underlying the PCP theorem. -/
theorem pcp_dinur (amp : CSP → CSP) (C : ℕ) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hsize : ∀ G : CSP, (amp G).size ≤ C * G.size)
    (hcomp : ∀ G : CSP, G.Satisfiable → (amp G).Satisfiable)
    (hgap : ∀ G : CSP, min α (2 * G.unsat) ≤ (amp G).unsat)
    (G : CSP) :
    (amp^[Nat.log 2 G.size + 1] G).size ≤ C ^ (Nat.log 2 G.size + 1) * G.size ∧
    (G.Satisfiable → (amp^[Nat.log 2 G.size + 1] G).Satisfiable) ∧
    (¬ G.Satisfiable → α ≤ (amp^[Nat.log 2 G.size + 1] G).unsat) := by
  refine ⟨size_iterate_le hsize G _, fun h => satisfiable_iterate hcomp G _ h, fun h => ?_⟩
  set t := Nat.log 2 G.size + 1 with ht
  have hs : (0 : ℝ) < G.size := by exact_mod_cast G.size_pos
  have hu : (1 : ℝ) / G.size ≤ G.unsat := G.inv_size_le_unsat h
  have hlt : G.size < 2 ^ t := Nat.lt_pow_succ_log_self (by norm_num) G.size
  have hltR : (G.size : ℝ) ≤ (2 : ℝ) ^ t := by
    have : ((G.size : ℝ)) ≤ ((2 ^ t : ℕ) : ℝ) := by exact_mod_cast hlt.le
    simpa using this
  have hone : (1 : ℝ) ≤ 2 ^ t * G.unsat := by
    have h1 : (2 : ℝ) ^ t * (1 / G.size) ≤ 2 ^ t * G.unsat := by
      have : (0 : ℝ) < 2 ^ t := by positivity
      exact mul_le_mul_of_nonneg_left hu this.le
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ t * (1 / G.size) := by
      rw [mul_one_div, le_div_iff₀ hs, one_mul]
      exact hltR
    linarith
  have hmin : min α ((2 : ℝ) ^ t * G.unsat) = α := min_eq_left (by linarith)
  have := gap_iterate hα0 hgap G t
  rwa [hmin] at this

end CS

