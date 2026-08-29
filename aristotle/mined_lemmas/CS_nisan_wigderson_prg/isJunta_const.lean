import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace CS

open Finset

/-- Real-valued indicator of a boolean: `1` for `true`, `0` for `false`. -/

lemma isJunta_const (α : ℕ) {l : ℕ} (b : Bool) : IsJunta α (fun _ : Fin l → Bool => b) :=
  ⟨∅, by simp, fun _ _ _ => rfl⟩

/-- A generic "hybrid argument": if the endpoints of a sequence of `m` steps differ by more
than `ε`, some single step contributes more than `ε / m`. -/
