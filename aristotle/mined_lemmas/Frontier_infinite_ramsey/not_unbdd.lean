/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-- `Unbdd A` says that the set of naturals satisfying `A` is unbounded, i.e. infinite. -/

theorem not_unbdd {A : Nat → Prop} (h : ¬ Unbdd A) : ∃ n, ∀ m, n < m → ¬ A m :=
  Classical.byContradiction fun hcon =>
    h fun n => Classical.byContradiction fun hn => hcon ⟨n, fun m hm hAm => hn ⟨m, hm, hAm⟩⟩

/-- Infinite pigeonhole for two colours: if `A` is unbounded and `f` is a two-colouring of `Nat`,
then one of the two colour classes inside `A` is still unbounded. -/
