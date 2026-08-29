/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Savitch.Model
import RequestProject.Savitch.Stack

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Savitch's theorem

`NSPACE f ⊆ DSPACE (f²)`.

Given a nondeterministic machine with at most `2 ^ (c * f n + c)` configurations we build a
deterministic machine which decides, by Savitch's midpoint recursion, whether an accepting
configuration is reachable in the configuration graph.  The deterministic machine stores an
explicit recursion stack of depth `c * f n + c + 2`, each frame holding a constant number of
configurations and indices, hence it has `2 ^ O(f n ^ 2)` configurations.

As a corollary, `PSPACE = NPSPACE`.
-/

namespace CS

open Savitch

section Construction

variable (M : NMachine)

/-- The vertices of the configuration graph: the configurations of `M`, together with an extra
sink `none` which is reachable exactly from the accepting configurations.  Thus `M` accepts iff
the sink is reachable from the initial configuration. -/
abbrev Vtx (M : NMachine) (n : ℕ) : Type := Option (M.Conf n)

instance vtxFinite (n : ℕ) : Finite (Vtx M n) := by
  haveI := M.finite n; infer_instance

noncomputable instance vtxFintype (n : ℕ) : Fintype (Vtx M n) := Fintype.ofFinite _

noncomputable instance vtxDecEq (n : ℕ) : DecidableEq (Vtx M n) := Classical.decEq _

/-- An enumeration of the vertices of the configuration graph. -/

theorem savMachine_card_le (M : NMachine) (c : ℕ) (sf : ℕ → ℕ)
    (hcard : ∀ n, Nat.card (M.Conf n) ≤ 2 ^ (c * sf n + c)) (n : ℕ) :
    Nat.card ((savMachine M c sf).Conf n) ≤
      2 ^ ((16 * c ^ 2 + 30 * c + 16) * sf n ^ 2 + (16 * c ^ 2 + 30 * c + 16)) := by
  have hlen : (enum M n).length = Nat.card (Vtx M n) := length_enum M n
  have hNX : Nat.card (Vtx M n) ≤ 2 ^ (c * sf n + c + 1) := card_vtx_le M c sf hcard n
  set s := c * sf n + c with hs
  set NX := Nat.card (Vtx M n) with hNXdef
  have hbase : Nat.card ((savMachine M c sf).Conf n) ≤
      ((savK c sf n + 1) * NX * NX * ((enum M n).length + 1) * 2 + 1) ^ (savK c sf n + 1) * 3 :=
    card_valid_le _ _
  have hKeq : savK c sf n = s + 1 := rfl
  have hone : (1 : ℕ) ≤ 2 ^ (s + 1) := Nat.one_le_two_pow
  have a1 : savK c sf n + 1 ≤ 2 ^ (s + 1) := by
    rw [hKeq]; exact two_pow_ge_succ (s + 1)
  have a3 : NX + 1 ≤ 2 ^ (s + 2) := by
    have h2 : (2 : ℕ) ^ (s + 2) = 2 ^ (s + 1) + 2 ^ (s + 1) := by ring
    omega
  have step1 : (savK c sf n + 1) * NX * NX * ((enum M n).length + 1) * 2 + 1 ≤
      2 ^ (4 * s + 7) := by
    rw [hlen]
    have hmul : (savK c sf n + 1) * NX * NX * (NX + 1) * 2 ≤
        2 ^ (s + 1) * 2 ^ (s + 1) * 2 ^ (s + 1) * 2 ^ (s + 2) * 2 := by
      gcongr
    have heq : (2 : ℕ) ^ (s + 1) * 2 ^ (s + 1) * 2 ^ (s + 1) * 2 ^ (s + 2) * 2 =
        2 ^ (4 * s + 6) := by ring
    have hlast : (2 : ℕ) ^ (4 * s + 7) = 2 ^ (4 * s + 6) + 2 ^ (4 * s + 6) := by ring
    have hpos : (1 : ℕ) ≤ 2 ^ (4 * s + 6) := Nat.one_le_two_pow
    omega
  have step2 : ((savK c sf n + 1) * NX * NX * ((enum M n).length + 1) * 2 + 1) ^
      (savK c sf n + 1) * 3 ≤ 2 ^ ((4 * s + 7) * (s + 2) + 2) := by
    calc ((savK c sf n + 1) * NX * NX * ((enum M n).length + 1) * 2 + 1) ^ (savK c sf n + 1) * 3
        ≤ (2 ^ (4 * s + 7)) ^ (savK c sf n + 1) * 3 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left step1 _)
      _ = 2 ^ ((4 * s + 7) * (s + 2)) * 3 := by rw [hKeq, ← pow_mul]
      _ ≤ 2 ^ ((4 * s + 7) * (s + 2)) * 4 := by omega
      _ = 2 ^ ((4 * s + 7) * (s + 2) + 2) := by ring
  refine hbase.trans (step2.trans (Nat.pow_le_pow_right (by norm_num) ?_))
  simpa [hs] using savitch_exponent_le c (sf n)

/-! ### Savitch's theorem -/

/-- **Savitch's theorem**: every language decided by a nondeterministic machine in space `O(f)`
is decided by a deterministic machine in space `O(f²)`. -/
