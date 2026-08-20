import Mathlib
namespace Brockian.MsVanDerWaerden

open Combinatorics Finset

/-- The set of "moving" coordinates of a combinatorial line. -/

private def lineConst {k : ℕ} {ι : Type} [Fintype ι] (l : Line (Fin k) ι) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i => l.idxFun i ≠ none), ((l.idxFun i).map Fin.val).getD 0

/-- Summing the coordinates of a point on a combinatorial line in `ι → Fin k` gives an
arithmetic progression in the parameter `x`. -/
