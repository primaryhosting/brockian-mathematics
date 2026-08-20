/-
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean does not allow a module docstring before `import`; the header is repeated verbatim
-- as the module docstring immediately below the imports.)
import Mathlib

/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

/-!
## Overview

We prove Ladner's theorem: *if `P ≠ NP` then there is an NP-intermediate language*, i.e. a
language in `NP` which is neither in `P` nor `NP`-complete.

Complexity theory is not available in Mathlib, so the development is carried out over an
explicit abstract model of polynomial time computation, packaged as the structure
`PolyFramework` below.  Strings are encoded as natural numbers, the *size* (bit length) of a
string `x` being `Nat.size x`, and a *language* is a function `ℕ → Bool`.

A `PolyFramework` consists of an enumeration `Red : ℕ → ℕ → ℕ` of the polynomial time
computable functions (`Red e` is the function computed by the `e`-th polynomial time program),
together with a degree function `deg` (`Red e` runs in time `(size x + 2) ^ deg e`), subject to
the standard closure properties of polynomial time:  closure under composition, pairing,
conditionals, basic arithmetic, bit counting, *clocked universal simulation* (running a program
with a unary time budget is polynomial), *bounded search* (searching a unary sized range for a
certificate is polynomial) and *iteration* (iterating a polynomial time function a unary number
of times, along an orbit whose sizes stay polynomially bounded, is polynomial).

All of these are standard true facts about polynomial time; they are taken as the hypotheses of
the theorem rather than as Lean `axiom`s, so the final result is axiom clean.
-/

namespace Ladner

/-- The number of set bits of `h` at positions `< m`. -/

theorem PLang_of_bounded (L : ℕ → Bool)
    (hcert : ∀ x y, F.Red vIdx (Nat.pair x y) = 1 → y ≤ 2 ^ ((Nat.size x + 2) ^ dL))
    (hLdef : ∀ x, L x = true ↔ ∃ y, F.Red vIdx (Nat.pair x y) = 1)
    (hb : ∃ B, ∀ n, fF F vIdx dL n ≤ B) : PLang F L := by
  obtain ⟨n₀, c, hstab, hnoj, hs0⟩ := bounded_stabilizes F vIdx dL hb
  have hsz : ∀ x, 2 ^ n₀ ≤ x → n₀ ≤ Nat.size x := by
    intro x hx
    have := size_le_size_of_le hx
    rw [Nat.size_pow] at this
    omega
  by_cases hpar : c % 2 = 0
  · have hAe := stuck_even F vIdx dL L hcert hLdef n₀ c hstab hnoj hs0 hpar
    have hPA : PLang F (Adiag F vIdx dL L) := (PLang_iff_Mach F _).mpr ⟨c / 2, hAe⟩
    refine PLang_of_eventually_eq F (2 ^ n₀) (Adiag F vIdx dL L) L hPA ?_
    intro x hx
    have hfx : fF F vIdx dL (Nat.size x) = c := hstab _ (hsz x hx)
    rw [Adiag, hfx, hpar]
    simp
  · have hAo := stuck_odd F vIdx dL L hcert hLdef n₀ c hstab hnoj hs0 hpar
    set T : ℕ → Bool := fun y => if y < 2 ^ n₀ then Adiag F vIdx dL L y else false with hT
    have hPT : PLang F T := by
      refine PLang_of_eventually_eq F (2 ^ n₀) (fun _ => false) T ?_ ?_
      · exact pf_congr (pf_const F 0) (by funext x; simp)
      · intro x hx
        simp [hT, Nat.not_lt.mpr hx]
    have hLT : ∀ x, L x = T (F.Red (c / 2) x) := by
      intro x
      rw [hAo x]
      by_cases hlt : F.Red (c / 2) x < 2 ^ n₀
      · simp [hT, hlt]
      · have hfx : fF F vIdx dL (Nat.size (F.Red (c / 2) x)) = c :=
          hstab _ (hsz _ (by omega))
        simp [hT, hlt, Adiag, hfx, hpar]
    have hcomp : PF F (fun x => if T (F.Red (c / 2) x) then 1 else 0) :=
      pf_comp F hPT (pf_Red F (c / 2))
    exact pf_congr hcomp (by funext x; rw [hLT x])

/-- If the gap function is unbounded, the diagonal language is not polynomial time. -/
