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

lemma SymMachine.reachable_iff {d : ℕ} (S : SymMachine d) (u v : S.C) :
    letI := S.fintypeC
    S.toRotGraph.Reachable (Fintype.equivFin S.C u) (Fintype.equivFin S.C v)
      ↔ Relation.ReflTransGen S.Adj u v := by
  letI := S.fintypeC
  set e : S.C ≃ Fin (Fintype.card S.C) := Fintype.equivFin S.C with he
  constructor
  · intro h
    have hlift := Relation.ReflTransGen.lift (f := fun x => e.symm x)
      (fun a b hab => (S.toRotGraph_adj_iff (e.symm a) (e.symm b)).1 (by simpa [he] using hab)) h
    simpa [he] using hlift
  · intro h
    exact Relation.ReflTransGen.lift (f := fun x => e x)
      (fun a b hab => (S.toRotGraph_adj_iff a b).2 hab) h

/-- Turning a `Machine` run on a fixed input graph, from a fixed initial configuration,
into a `DetMachine`. -/
