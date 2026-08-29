/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained and uses no imports, so that the header
comment above can be the very first thing in the file: Lean requires `import`
commands to precede every other command, including module documentation.
Consequently primality is developed from scratch here, as `Brockian.IsPrimeNat`.
The companion file `RequestProject/GoldbachWheelK2_1153Mathlib.lean` imports
Mathlib, proves `IsPrimeNat n ↔ Nat.Prime n`, and restates the main result in
Mathlib's vocabulary.
-/

namespace Brockian

/-- `IsPrimeNat n` is the usual definition of primality for natural numbers:
`n` is at least `2` and its only divisors are `1` and `n`. -/

theorem noDivBelow_sound :
    ∀ (n k : Nat), noDivBelow n k = true → ∀ d, 2 ≤ d → d < k → d < n → n % d ≠ 0 := by
  intro n k
  induction k with
  | zero => intro _ d _ hd; omega
  | succ k ih =>
    intro h d hd2 hdk hdn
    simp only [noDivBelow, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
    obtain ⟨h1, h2⟩ := h
    rcases Nat.lt_or_ge d k with hlt | hge
    · exact ih h2 d hd2 hlt hdn
    · have hdk' : d = k := by omega
      subst hdk'
      rcases h1 with h1 | h1
      · omega
      · exact h1

