/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Statement: NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` commands to precede every declaration, including module
docstrings, so the header above is a plain block comment.)
-/
import Mathlib
import RequestProject.Savitch.Model
import RequestProject.Savitch.Walk
import RequestProject.Savitch.Sim
import RequestProject.Savitch.Semantics
import RequestProject.Savitch.Space

/-!
The space-bounded machine model, the classes `CS.NSPACE`, `CS.DSPACE`,
`CS.PSPACE` and `CS.NPSPACE`, and the simulator used in the proof are defined in
the files `RequestProject/Savitch/*.lean`.

A machine reads its input through a head whose position is determined by its
memory value, and it works in space `g` if on inputs of length `n` all reachable
memory values lie in a set of at most `2 ^ g n` values depending only on `n`
(the standard correspondence between `s` tape cells and `2 ^ O(s)`
configurations).  The classes `NSPACE g` and `DSPACE g` are closed under
constant factors by definition, as usual for space classes.

Savitch's theorem is proved for space bounds `f` with `n + 1 ≤ 2 ^ f n`
(i.e. `f n ≥ log₂ (n+1)`), the standard hypothesis `f (n) ≥ log n`.
-/

namespace CS

/-- **Savitch's theorem**: a language recognized by a nondeterministic machine in
space `f` (with `f n ≥ log₂ (n + 1)`) is recognized by a deterministic machine in
space `O(f²)`, i.e. `NSPACE f ⊆ DSPACE (f²)`. -/

def stepD (m : SMem N.Mem) (o : Option Bool) : SMem N.Mem :=
  match m with
  | .scan i => match o with
      | some _ => .scan (i + 1)
      | none => .outer i (cands N S i)
  | .outer n todo => match todo with
      | [] => .outer n []
      | b :: bs => if N.acc b then .call n bs N.start b (g n) [] else .outer n bs
  | .call n todo a b k st => match k with
      | 0 => .ret n todo (decide (a = b ∨ b ∈ N.next a o)) st
      | k + 1 => match cands N S n with
          | [] => .ret n todo false st
          | m :: ms => .call n todo a m k (⟨a, b, k, m, ms, false⟩ :: st)
  | .ret n todo v st => match st with
      | [] => if v then .acc else .outer n todo
      | fr :: st' =>
          if v then
            (if fr.second then .ret n todo true st'
             else .call n todo fr.cur fr.b fr.k
                    (⟨fr.a, fr.b, fr.k, fr.cur, fr.rest, true⟩ :: st'))
          else
            match fr.rest with
            | [] => .ret n todo false st'
            | m :: ms => .call n todo fr.a m fr.k (⟨fr.a, fr.b, fr.k, m, ms, false⟩ :: st')
  | .acc => .acc

/-- The input position read by the simulator. -/
