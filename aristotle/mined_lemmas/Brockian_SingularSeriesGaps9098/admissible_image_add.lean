/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
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

namespace Brockian

/-- A finite set of natural numbers is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuple conjecture: its singular series is nonzero) when,
for every prime `p`, the elements of the set miss at least one residue class mod `p`. -/

theorem admissible_image_add {B : Finset ℕ} (hB : Admissible B) (t : ℕ) :
    Admissible (B.image (· + t)) := by
  intro p hp
  obtain ⟨r, hrp, hr⟩ := hB p hp
  refine ⟨(r + t) % p, Nat.mod_lt _ hp.pos, ?_⟩
  intro b hb
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
  intro hEq
  have hcr : c % p = r % p := Nat.ModEq.add_right_cancel' t hEq
  exact hr c hc (by rw [hcr, Nat.mod_eq_of_lt hrp])

/-- The dense `9`-tuple pattern `{0, 2, 6, 8, 12, 18, 20, 26, 30}`: nine offsets of
diameter `30`. -/
