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

lemma walk_reachable (G : RotGraph n d) (seq : ℕ → Fin d) (p : Fin n × Fin d) (k : ℕ) :
    G.Reachable p.1 (G.walk seq p k).1 := by
  induction k with
  | zero => exact Relation.ReflTransGen.refl
  | succ k ih => exact ih.tail (G.adj_rot _)

end RotGraph

/-! ## Universal exploration sequences -/

/-- `seq` is a universal exploration sequence of length `T` for `d`-regular rotation graphs
on `Fin n`: from any start vertex, following the offsets of `seq` for at most `T` steps
visits every vertex of the connected component of the start vertex. -/
