import Mathlib

/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set

namespace Frontier

open Classical in
/-- The `U`-generic colour at `n`: the colour `b` such that `{m | c n m = b} ∈ U`. -/

lemma rstep_snd_sub_color (c : ℕ → ℕ → Bool) (b : Bool) (p : ℕ × Set ℕ) :
    (rstep c b p).2 ⊆ {x | c (rstep c b p).1 x = b} ∩ Ioi (rstep c b p).1 :=
  fun _ hx => ⟨hx.1.2, hx.2⟩

/-- The iterates of `rstep` have decreasing second components. -/
