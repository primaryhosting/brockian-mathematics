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

namespace Brockian

/-- A finite set of integers is **admissible** if for every prime `p` it misses at least one
residue class modulo `p` (equivalently, the local factor of the Hardy–Littlewood singular
series attached to the tuple is nonzero at every prime). -/

theorem admissible_gap_1246 : Admissible ({0, (1246 : ℤ)} : Finset ℤ) :=
  admissible_even_gaps_1240_1250 1246 (by norm_num) (by norm_num) (by decide)

end Brockian

#print axioms Brockian.SingularSeriesGaps12401250
#print axioms Brockian.admissible_even_gaps_1240_1250
#print axioms Brockian.admissible_gap_1246

