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
