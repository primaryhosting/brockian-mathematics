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

set_option maxHeartbeats 1000000

namespace Brockian

/-- `residueCount H p` is the number of distinct residue classes modulo `p`
occupied by the shifts in the tuple `H`. -/

noncomputable def residueCount (H : Finset ℤ) (p : ℕ) : ℕ :=
  (H.image (fun h : ℤ => (h : ZMod p))).card

/-- A finite set of integer shifts is *admissible* (in the sense of Hardy–Littlewood)
when, for every prime `p`, it misses at least one residue class modulo `p`. -/
