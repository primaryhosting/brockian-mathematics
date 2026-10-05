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

lemma walk_succ (G : RotGraph n d) (seq : ℕ → Fin d) (p : Fin n × Fin d) (k : ℕ) :
    G.walk seq p (k+1) = G.stepE (seq k) (G.walk seq p k) := rfl

/-- Soundness of the exploration walk: it never leaves the connected component of its
starting vertex. -/
