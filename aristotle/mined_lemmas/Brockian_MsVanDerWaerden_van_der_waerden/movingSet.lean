import Mathlib
namespace Brockian.MsVanDerWaerden

open Combinatorics Finset

/-- The set of "moving" coordinates of a combinatorial line. -/

private def movingSet {k : ℕ} {ι : Type} [Fintype ι] (l : Line (Fin k) ι) : Finset ι :=
  Finset.univ.filter (fun i => l.idxFun i = none)

/-- The constant part of the sum along a combinatorial line. -/
