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

/-
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-! ... -/` module docstring
-- because Lean 4 does not allow a module docstring to precede the `import` line.)

import Mathlib

/-!
## Overview

A "spectral model" for Goldbach's conjecture is an abstract family of finite *spectra*
`spec n ⊆ ℕ`, one for each natural number `n`, whose points are primes `p ≤ n` whose
"reflection" `n - p` is again prime, and which is required to be non-degenerate
(non-empty) at every even `n ≥ 4`.

The schema theorem of interest is

  `Nonempty SpectralModel → Goldbach`,

i.e. *Goldbach from a spectral model*.  The named hypothesis is `Nonempty SpectralModel`.

The main result `goldbach_from_spectral_model` below is stated **unconditionally**: it
upgrades the one-way schema to an equivalence,

  `Nonempty SpectralModel ↔ Goldbach`,

by exhibiting the *canonical* spectral model built from the true Goldbach spectrum.
In particular the named hypothesis is exactly as strong as Goldbach's conjecture itself, so
no proof of the schema can be made unconditional by discharging that hypothesis with less
than a proof of Goldbach; conversely, the model-theoretic detour costs nothing.

We also record genuinely unconditional content: the canonical spectrum is symmetric under
reflection, its non-emptiness is equivalent to `n` being a sum of two primes, and it is
non-empty for every even `4 ≤ n ≤ 200` (a kernel-checked finite certificate), which yields
Goldbach's conjecture in that range.
-/

namespace Brockian.GoldbachSchema

/-- `p` and `q` are a Goldbach pair for `n`. -/

theorem goldbachSpectrum_nonempty_of_le_200 {n : ℕ} (hn : Even n) (h4 : 4 ≤ n)
    (hle : n ≤ 200) : (goldbachSpectrum n).Nonempty := by
  obtain ⟨p, hp, hp1, hp2⟩ :=
    goldbach_certificate_200 n (Finset.mem_range.2 (by omega)) ⟨hn, h4⟩
  exact ⟨p, mem_goldbachSpectrum.2 ⟨Nat.lt_succ_iff.1 (Finset.mem_range.1 hp), hp1, hp2⟩⟩

/-- Goldbach's conjecture holds unconditionally for all even `n` with `4 ≤ n ≤ 200`. -/
