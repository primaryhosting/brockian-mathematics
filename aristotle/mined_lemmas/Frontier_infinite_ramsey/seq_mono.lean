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

theorem seq_mono (c : Nat → Nat → Bool) {m n : Nat} (h : m ≤ n) {b : Nat} (hb : (seq c n).A b) :
    (seq c m).A b := by
  induction n with
  | zero => have : m = 0 := by omega
            subst this; exact hb
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact ih (by omega) (seq_succ_apply c n b hb).1
    · have : m = n + 1 := by omega
      subst this; exact hb

