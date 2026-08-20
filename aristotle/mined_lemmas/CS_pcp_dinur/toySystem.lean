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
