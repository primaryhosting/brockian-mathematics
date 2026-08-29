/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Cert

/-! ## Arithmetic: an injective pairing function on `Nat` -/

/-- Szudzik-style pairing function. -/

theorem run_no_fault_of_verdict (a : Artifact) (m : Machine)
    (hv : (reprove a).verdict = true) (hm : m.fault = false) : (run a m).fault = false := by
  have hall : ∀ i ∈ a.code, Instr.allowed a.policy i = true := by
    have := hv
    simp only [reprove, isolated, List.all_eq_true] at this
    exact this
  unfold run
  revert hall
  generalize a.code = l
  intro hall
  induction l generalizing m with
  | nil => exact hm
  | cons i is ih =>
      rw [List.foldl_cons]
      exact ih (step a.policy m i) (fun j hj => hall j (List.mem_cons_of_mem _ hj))
        (step_no_fault a.policy m i (hall i (List.mem_cons_self ..)) hm)

end PCA.Cert

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

