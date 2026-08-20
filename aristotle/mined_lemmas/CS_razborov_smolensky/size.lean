import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


def size : Circuit → ℕ
  | .var _ => 1
  | .const _ => 1
  | .cnot c => c.size + 1
  | .cor cs => (cs.map size).sum + 1
  | .cand cs => (cs.map size).sum + 1
  | .cmod cs => (cs.map size).sum + 1

/-- The depth of a circuit, i.e. the maximal number of `AND`/`OR`/`MOD` gates on a
path from the output to an input.  (`NOT` gates are not counted; this only makes the
main theorem stronger.) -/
