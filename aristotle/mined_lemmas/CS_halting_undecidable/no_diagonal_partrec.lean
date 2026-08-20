/-
# Halting Undecidable
Category: Computer Science
Target: CS.halting_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

open Nat.Partrec Nat.Partrec.Code Denumerable

/-- **Diagonalization lemma.**  There is no partial recursive function `d` that halts on
input `n` exactly when the `n`-th program fails to halt on input `n`. -/

theorem no_diagonal_partrec :
    ¬ ∃ d : ℕ →. ℕ, Partrec d ∧
        ∀ n : ℕ, (d n).Dom ↔ ¬ (eval (ofNat Nat.Partrec.Code n) n).Dom := by
  rintro ⟨d, hd, hspec⟩
  -- `d` has a code `c`; instantiate the specification at the encoding of `c` itself.
  obtain ⟨c, hc⟩ := exists_code.1 (Partrec.nat_iff.mp hd)
  have h := hspec (Encodable.encode c)
  rw [Denumerable.ofNat_encode, hc] at h
  exact (iff_not_self h).elim

/-- **The halting problem is undecidable.**

There is no total computable function `H` which, given (a code for) a program `p` and an
input `x`, decides whether `p` halts on `x`.  Here programs are the partial recursive
codes `Nat.Partrec.Code`, `eval p x` is the (possibly divergent) run of `p` on input `x`,
and "`p` halts on `x`" means `(eval p x).Dom`. -/
