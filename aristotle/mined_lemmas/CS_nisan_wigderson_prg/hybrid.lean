import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

/-- Real-valued indicator of a Boolean value. -/

noncomputable def hybrid (G : Fin m → (Fin ℓ → Bool) → Bool) (D : (Fin m → Bool) → Bool)
    (k : ℕ) : ℝ :=
  hybSum G D k / (2 ^ ℓ * 2 ^ m)

/-- The Nisan–Wigderson / Yao next-bit predictor for the `i`-th output bit, built from the
distinguisher `D`, the earlier generator components `G j` (`j < i`), a fixed string `r` of
random bits and a bit `c` telling whether to complement the output. -/
