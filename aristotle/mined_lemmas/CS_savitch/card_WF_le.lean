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

import Mathlib
import RequestProject.Savitch.Enc

/-!
# The Savitch simulator and its correctness

We build, from a nondeterministic machine `M` and a recursion depth `K`, a
deterministic machine `savitchDM M K` which decides, by Savitch's recursive midpoint
search, whether the sink vertex `none` of the configuration graph of `M` is reachable
from the start vertex within `2 ^ K` steps.  If `cV M ≤ 2 ^ K` this is exactly
acceptance by `M`.
-/

namespace CS
namespace Savitch

variable {Sigma : Type}


theorem card_WF_le (M : NMachine Sigma) (K : ℕ) :
    Fintype.card {s : Raw M // WFraw M K s} ≤
      ((Fintype.card M.S + 1) * (Fintype.card M.S + 1) * (K + 1) + 2 + 2) *
        ((Fintype.card M.S + 1) * (Fintype.card M.S + 1) * (K + 1) *
          (Fintype.card M.S + 1) * 2 + 1) ^ (K + 1) := by
  have h := Fintype.card_le_of_injective (fun s : {s : Raw M // WFraw M K s} => encRaw M K s.1)
    (fun s t h => Subtype.ext (encRaw_inj s.2 t.2 h))
  refine le_trans h (le_of_eq ?_)
  simp only [RawE, Fintype.card_prod, Fintype.card_sum, Fintype.card_bool, Fintype.card_fun,
    Fintype.card_option, Fintype.card_fin, cV]
  ring

end Savitch
end CS

