/-!
# Euclid Gcd Correct
Category: Computer Science
Target: CS.euclid_gcd_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to be the very first commands in a file,
-- so no `import` line can precede the header comment above. All results used here
-- (`Nat.gcd`, `Nat.gcd_rec`, `Nat.gcd_comm`, `Nat.dvd_gcd`, `Nat.gcd_dvd_left`,
-- `Nat.gcd_dvd_right`, `Nat.mod_lt`) are available without any extra imports.

set_option autoImplicit false

namespace CS

/-- Euclid's algorithm: repeatedly replace `(a, b)` by `(b, a % b)` until the second
argument is `0`. The `termination_by`/`decreasing_by` clauses (discharged by
`Nat.mod_lt`) constitute the termination proof: the recursion is well founded
because the second argument strictly decreases at each step. -/
def euclid : Nat → Nat → Nat
  | a, 0 => a
  | a, (b + 1) => euclid (b + 1) (a % (b + 1))
  termination_by _ b => b
  decreasing_by exact Nat.mod_lt _ (Nat.succ_pos b)

@[simp] theorem euclid_zero (a : Nat) : euclid a 0 = a := by
  simp [euclid]

theorem euclid_succ (a b : Nat) : euclid a (b + 1) = euclid (b + 1) (a % (b + 1)) := by
  simp [euclid]

/-- One step of Euclid's algorithm preserves the gcd. -/
theorem gcd_succ_step (a b : Nat) : Nat.gcd a (b + 1) = Nat.gcd (b + 1) (a % (b + 1)) := by
  rw [Nat.gcd_comm a (b + 1), Nat.gcd_rec (b + 1) a, Nat.gcd_comm]

/-- Euclid's algorithm computes `Nat.gcd`. -/
theorem euclid_eq_gcd (a b : Nat) : euclid a b = Nat.gcd a b := by
  match b with
  | 0 => simp
  | (b + 1) =>
    rw [euclid_succ, euclid_eq_gcd (b + 1) (a % (b + 1)), gcd_succ_step]
  termination_by b
  decreasing_by exact Nat.mod_lt _ (Nat.succ_pos b)

/--
**Correctness and termination of Euclid's algorithm.**

The function `CS.euclid` is defined by well-founded recursion on its second argument
(hence it terminates on every input), and for all `a b : Nat` its output `CS.euclid a b`:

* agrees with `Nat.gcd a b`;
* divides both `a` and `b`;
* is divisible by every common divisor of `a` and `b`;

i.e. it is a greatest common divisor of `a` and `b`.
-/
theorem euclid_gcd_correct (a b : Nat) :
    euclid a b = Nat.gcd a b ∧
      euclid a b ∣ a ∧ euclid a b ∣ b ∧
      ∀ d : Nat, d ∣ a → d ∣ b → d ∣ euclid a b := by
  refine ⟨euclid_eq_gcd a b, ?_, ?_, ?_⟩
  · rw [euclid_eq_gcd]; exact Nat.gcd_dvd_left a b
  · rw [euclid_eq_gcd]; exact Nat.gcd_dvd_right a b
  · intro d hda hdb
    rw [euclid_eq_gcd]
    exact Nat.dvd_gcd hda hdb

end CS

