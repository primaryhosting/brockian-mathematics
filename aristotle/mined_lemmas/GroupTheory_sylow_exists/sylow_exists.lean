import Mathlib

/-!
# Sylow Exists
Category: Frontier Wave 2 (deeper machinery)
Target: GroupTheory.sylow_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace GroupTheory

/-- **Sylow's first theorem**: for a finite group `G` and a prime `p`, a Sylow `p`-subgroup
of `G` exists, i.e. the type `Sylow p G` is nonempty.

The primality hypothesis `hp` is kept because it is part of the requested statement; it is in
fact not needed, since `Sylow p G` is nonempty for every natural number `p` (the trivial
subgroup is a `p`-group, and every `p`-subgroup of a finite group is contained in a maximal
one). -/

theorem sylow_exists (G : Type*) [Group G] [Fintype G] (p : ℕ) (hp : p.Prime) :
    Nonempty (Sylow p G) := by
  rcases eq_or_ne p 0 with h | h
  · exact absurd h hp.ne_zero
  · exact Sylow.nonempty

/-- Every `p`-subgroup of a finite group is contained in a Sylow `p`-subgroup. -/
