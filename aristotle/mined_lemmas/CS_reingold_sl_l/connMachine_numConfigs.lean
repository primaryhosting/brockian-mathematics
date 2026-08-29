import Mathlib
import RequestProject.ReingoldSlL

/-!
## Existence of universal exploration sequences

The hypothesis `CS.HasPolyUES` used in `RequestProject/ReingoldSlL.lean` asks for universal
exploration sequences of *polynomial* length; producing such short sequences is the deep part
of Reingold's theorem and is not formalised.  Here we prove, unconditionally, that universal
exploration sequences of *some* finite length always exist (`CS.exists_ues`).  This shows that
the notion is satisfiable — the only missing ingredient in `CS.HasPolyUES` is the polynomial
length bound.
-/

set_option autoImplicit false

namespace CS

namespace RotGraph

variable {n d : ℕ}

/-- The walk of length `k` only depends on the first `k` offsets. -/

lemma connMachine_numConfigs (n d T : ℕ) [NeZero d] (seq : ℕ → Fin d) :
    (connMachine n d T seq).numConfigs = n * d * (n * ((T + 1) * 2)) := by
  simp [numConfigs, connMachine]

/-- The state of the connectivity machine after `k` steps: it holds the `min k T`-th point of
the exploration walk, the target vertex, the counter `min k T`, and the bit recording whether
the target has been visited so far. -/
