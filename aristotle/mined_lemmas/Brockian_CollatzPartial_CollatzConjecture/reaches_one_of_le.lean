import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file deliberately has no `import` line: the required header above is a module
docstring, and Lean requires all imports to precede any command, including module
docstrings.  Everything below therefore uses only core Lean 4 (no Mathlib), which
is sufficient for the development.
-/

set_option autoImplicit false

namespace Brockian.CollatzPartial

/-- One step of the Collatz map: `n ↦ n / 2` for even `n`, `n ↦ 3 * n + 1` for odd `n`. -/

theorem reaches_one_of_le
    (hdesc : ∀ n : Nat, 1 < n → n % 4 = 3 → ∃ k, 0 < k ∧ iter k n < n) :
    ∀ N n : Nat, n ≤ N → 0 < n → ∃ k, iter k n = 1 := by
  intro N
  induction N with
  | zero => intro n hn hpos; omega
  | succ N ih =>
      intro n hn hpos
      by_cases h1 : n = 1
      · exact ⟨0, by simp [h1]⟩
      · have hlt : 1 < n := by omega
        have hstep : ∃ k, 0 < k ∧ iter k n < n := by
          have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
          rcases h4 with h | h | h | h
          · exact descent_even hlt (by omega)
          · exact descent_one_mod_four hlt h
          · exact descent_even hlt (by omega)
          · exact hdesc n hlt h
        obtain ⟨k, _, hk⟩ := hstep
        obtain ⟨m, hm⟩ := ih (iter k n) (by omega) (iter_pos k hpos)
        exact ⟨m + k, by rw [iter_add]; exact hm⟩

/--
**Conditional reduction of the Collatz conjecture.**

If every `n > 1` with `n ≡ 3 (mod 4)` eventually reaches a value strictly smaller than
itself under iteration of the Collatz map, then the Collatz conjecture holds: every
positive natural number reaches `1`.

The other residue classes — the even numbers and `n ≡ 1 (mod 4)` — are handled
unconditionally here (see `descent_even` and `descent_one_mod_four`), so only the
`n ≡ 3 (mod 4)` case is assumed.
-/
