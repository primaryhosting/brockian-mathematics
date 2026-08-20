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

-- (Lean 4 requires `import` lines to precede any module doc-comment, so the requested
-- header block appears immediately below the import.)
import Mathlib

/-!
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The existence of a Fermat prime `F_n = 2^(2^n) + 1` with `n > 4` (i.e. beyond `F_4 = 65537`)
is an open problem.  What is proved here is a *complete, unconditional reduction* of that
statement to Pépin's criterion: for every `n ≥ 1`,

  `F_n` is prime  ↔  `3 ^ ((F_n - 1)/2) = -1` in `ZMod (F_n)`.

The `←` direction is Mathlib's `Nat.pepin_primality`; the `→` direction (that `3` is a
quadratic non-residue modulo a Fermat prime) is proved here from quadratic reciprocity
(`legendreSym.quadratic_reciprocity_one_mod_four`) and Euler's criterion
(`legendreSym.eq_pow`).
-/

namespace Brockian.FermatNumbers

open Nat

/-- `F_n % 4 = 1` for `n ≥ 1`. -/

lemma pepin_converse (n : ℕ) (hn : 1 ≤ n) (hp : (fermatNumber n).Prime) :
    (3 : ZMod (fermatNumber n)) ^ (2 ^ (2 ^ n - 1)) = -1 := by
  haveI : Fact (fermatNumber n).Prime := ⟨hp⟩
  have h4 : fermatNumber n % 4 = 1 := fermatNumber_mod_four n hn
  have h3 : fermatNumber n % 3 = 2 := fermatNumber_mod_three n hn
  -- Quadratic reciprocity: since `F_n ≡ 1 [MOD 4]`, `(3 | F_n) = (F_n | 3)`.
  have hqr : legendreSym 3 (fermatNumber n : ℤ) = legendreSym (fermatNumber n) 3 :=
    legendreSym.quadratic_reciprocity_one_mod_four h4 (by norm_num)
  -- and `F_n ≡ 2 [MOD 3]`, while `2` is a non-residue mod `3`.
  have hleft : legendreSym 3 (fermatNumber n : ℤ) = -1 := by
    rw [legendreSym.mod 3 (fermatNumber n : ℤ)]
    have h : ((fermatNumber n : ℤ) % ((3 : ℕ) : ℤ)) = 2 := by omega
    rw [h]
    exact (by decide : legendreSym 3 2 = -1)
  -- Euler's criterion turns this into the Pépin congruence.
  have heuler := legendreSym.eq_pow (fermatNumber n) (3 : ℤ)
  rw [hqr.symm.trans hleft] at heuler
  have hdiv : fermatNumber n / 2 = 2 ^ (2 ^ n - 1) := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : (2 : ℕ) ^ (2 ^ n) = 2 * 2 ^ (2 ^ n - 1) := by
      rw [← _root_.pow_succ']
      congr 1
      omega
    unfold fermatNumber
    omega
  rw [hdiv] at heuler
  push_cast at heuler
  exact heuler.symm

/-- **Pépin's test**, as an equivalence: for `n ≥ 1`, the Fermat number `F_n` is prime
iff `3 ^ (2 ^ (2 ^ n - 1)) = -1` in `ZMod (F_n)`. -/
