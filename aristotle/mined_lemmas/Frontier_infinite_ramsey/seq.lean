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

noncomputable def seq (c : Nat → Nat → Bool) : Nat → St c
  | 0 => ⟨fun _ => True, fun n => ⟨n + 1, by omega, trivial⟩⟩
  | n + 1 => ⟨(stepOf c (seq c n)).B, (stepOf c (seq c n)).unbdd⟩

/-- The `n`-th chosen point. -/
