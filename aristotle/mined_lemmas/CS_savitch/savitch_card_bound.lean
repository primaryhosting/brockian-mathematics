import RequestProject.Savitch.Machine

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Savitch's theorem

We model a space-`s` machine by its configuration graph: it has at most `2 ^ s`
configurations (`s` bits of workspace), a start configuration, an acceptance
predicate, and a transition relation (a relation for nondeterministic machines, a
function for deterministic ones).  A nondeterministic machine accepts when some
accepting configuration is reachable from the start configuration; a deterministic
machine accepts when its (unique) run visits an accepting configuration.

The main theorem `CS.savitch` states `NSPACE f ⊆ DSPACE (9 * (f + 1) ^ 2)`, i.e.
nondeterministic space `f` is contained in deterministic space `O(f ^ 2)`, and
`CS.PSPACE_eq_NPSPACE` deduces `PSPACE = NPSPACE`.
-/

namespace CS

open Savitch

/-- A nondeterministic machine using space `s`: at most `2 ^ s` configurations. -/
structure NMachine (s : ℕ) where
  /-- Number of configurations. -/
  size : ℕ
  /-- The space bound: `s` bits of workspace. -/
  hsize : size ≤ 2 ^ s
  /-- The (nondeterministic) transition relation. -/
  step : Fin size → Fin size → Bool
  /-- The initial configuration. -/
  start : Fin size
  /-- The accepting configurations. -/
  acc : Fin size → Bool

/-- A nondeterministic machine accepts if some accepting configuration is reachable. -/

theorem savitch_card_bound {n s : ℕ} (hn : n ≤ 2 ^ (s + 1)) :
    (n * n + 2) * (2 * (n * n * n) + 1) ^ (s + 1) ≤ 2 ^ (9 * (s + 1) ^ 2) := by
  set t := s + 1 with ht
  have ht1 : 1 ≤ t := by omega
  have h1 : n * n + 2 ≤ 2 ^ (2 * t + 1) := by
    have hnn : n * n ≤ 2 ^ (2 * t) := by
      calc n * n ≤ 2 ^ t * 2 ^ t := Nat.mul_le_mul hn hn
      _ = 2 ^ (2 * t) := by rw [← pow_add]; ring_nf
    have h2 : (2 : ℕ) ≤ 2 ^ (2 * t) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc n * n + 2 ≤ 2 ^ (2 * t) + 2 ^ (2 * t) := by omega
    _ = 2 ^ (2 * t + 1) := by rw [pow_succ]; ring
  have h2 : 2 * (n * n * n) + 1 ≤ 2 ^ (3 * t + 2) := by
    have hnnn : n * n * n ≤ 2 ^ (3 * t) := by
      calc n * n * n ≤ 2 ^ t * 2 ^ t * 2 ^ t := Nat.mul_le_mul (Nat.mul_le_mul hn hn) hn
      _ = 2 ^ (3 * t) := by rw [← pow_add, ← pow_add]; ring_nf
    have hle : 2 * (n * n * n) ≤ 2 ^ (3 * t + 1) := by
      calc 2 * (n * n * n) ≤ 2 * 2 ^ (3 * t) := by omega
      _ = 2 ^ (3 * t + 1) := by rw [pow_succ]; ring
    have h1' : (1 : ℕ) ≤ 2 ^ (3 * t + 1) := Nat.one_le_two_pow
    calc 2 * (n * n * n) + 1 ≤ 2 ^ (3 * t + 1) + 2 ^ (3 * t + 1) := by omega
    _ = 2 ^ (3 * t + 2) := by rw [pow_succ, pow_succ]; ring
  calc (n * n + 2) * (2 * (n * n * n) + 1) ^ t
      ≤ 2 ^ (2 * t + 1) * (2 ^ (3 * t + 2)) ^ t := Nat.mul_le_mul h1 (Nat.pow_le_pow_left h2 t)
  _ = 2 ^ (2 * t + 1 + (3 * t + 2) * t) := by rw [← pow_mul, ← pow_add]
  _ ≤ 2 ^ (9 * t ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-! ### Turning an abstract deterministic dynamical system into a `DMachine` -/

