import RequestProject.ISMachine

/-!
# Completeness of the counting machine

If `t` is not reachable from `s`, then the counting machine has an accepting computation:
all the guesses it has to make are correct guesses, and all the certificates it has to
produce do exist.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS


@[simp] lemma Lit.holds_always {n : ℕ} (x : Fin n → Bool) :
    (Lit.always (n := n)).holds x ↔ True := Iff.rfl

/-- A nondeterministic machine on inputs of length `n`, presented by its configuration
graph. -/
structure Mach (n : ℕ) where
  /-- The set of configurations. -/
  V : Type
  /-- Configurations form a finite type. -/
  fV : Fintype V
  /-- The initial configuration. -/
  start : V
  /-- The accepting configuration. -/
  acc : V
  /-- The guard controlling the transition from one configuration to another. -/
  edge : V → V → Lit n

attribute [instance] Mach.fV

/-- One computation step of `M` on input `x`. -/
