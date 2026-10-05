/-
  Proof of `Brockian.AdmissibilityHLCriterion.not_admissible_of_residueImage_univ`.

  The corpus module `Brockian.AdmissibilityHLCriterion` is not part of this project, so
  the three corpus declarations the goal is phrased in terms of (`residueImage`,
  `OmitsResidue`, `Admissible`) are reproduced here verbatim, in their original
  namespace, purely so that the statement elaborates.  Nothing else is restated.

  Note on the ambient instance: `Finset.univ : Finset (ZMod p)` needs `Fintype (ZMod p)`,
  which Mathlib provides from `NeZero p`.  In this standalone file that instance is
  supplied by a section `variable [NeZero p]` (harmless, since `p` is prime); the proof
  body itself is exactly the requested one and uses nothing beyond `hp` and `h`.
-/
import Mathlib

set_option autoImplicit false

open Finset

namespace Brockian.AdmissibilityHLCriterion

/-- The residue classes mod `p` occupied by a finite integer tuple `H`. -/

def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → OmitsResidue p H

section

variable {p : ℕ} [NeZero p]

/-- If the reduction of `S` mod some prime `p` covers every residue class, then `S` omits
no class mod `p`, hence `S` is not admissible. -/
