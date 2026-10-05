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
def IsGoldbachPair (n p q : ℕ) : Prop := Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- Goldbach's conjecture: every even `n ≥ 4` is a sum of two primes. -/
def Goldbach : Prop := ∀ n : ℕ, Even n → 4 ≤ n → ∃ p q : ℕ, IsGoldbachPair n p q

/-- A *spectral model* for Goldbach's conjecture: an abstract family of finite spectra,
supported on primes `p ≤ n` with prime reflection `n - p`, which is non-degenerate at
every even `n ≥ 4`. -/
structure SpectralModel where
  /-- The spectrum attached to `n`. -/
  spec : ℕ → Finset ℕ
  /-- Spectral points are primes. -/
  prime_of_mem : ∀ {n p : ℕ}, p ∈ spec n → Nat.Prime p
  /-- Spectral points are bounded by `n`. -/
  le_of_mem : ∀ {n p : ℕ}, p ∈ spec n → p ≤ n
  /-- The reflection of a spectral point is prime. -/
  prime_sub_of_mem : ∀ {n p : ℕ}, p ∈ spec n → Nat.Prime (n - p)
  /-- Non-degeneracy at the even points `n ≥ 4`. -/
  nonempty_of_even : ∀ {n : ℕ}, Even n → 4 ≤ n → (spec n).Nonempty

/-- The canonical (Goldbach) spectrum of `n`: the primes `p ≤ n` with `n - p` prime. -/
def goldbachSpectrum (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun p => Nat.Prime p ∧ Nat.Prime (n - p)

lemma mem_goldbachSpectrum {n p : ℕ} :
    p ∈ goldbachSpectrum n ↔ p ≤ n ∧ Nat.Prime p ∧ Nat.Prime (n - p) := by
  simp [goldbachSpectrum]

/-- The canonical spectrum is invariant under the reflection `p ↦ n - p`. -/
lemma goldbachSpectrum_reflect {n p : ℕ} (hp : p ∈ goldbachSpectrum n) :
    n - p ∈ goldbachSpectrum n := by
  rw [mem_goldbachSpectrum] at hp ⊢
  obtain ⟨hle, hp1, hp2⟩ := hp
  refine ⟨Nat.sub_le _ _, hp2, ?_⟩
  rwa [Nat.sub_sub_self hle]

/-- Non-emptiness of the canonical spectrum at `n` is exactly the Goldbach property of `n`. -/
lemma goldbachSpectrum_nonempty_iff {n : ℕ} :
    (goldbachSpectrum n).Nonempty ↔ ∃ p q : ℕ, IsGoldbachPair n p q := by
  constructor
  · rintro ⟨p, hp⟩
    rw [mem_goldbachSpectrum] at hp
    exact ⟨p, n - p, hp.2.1, hp.2.2, Nat.add_sub_cancel' hp.1⟩
  · rintro ⟨p, q, hp, hq, hpq⟩
    refine ⟨p, mem_goldbachSpectrum.2 ⟨hpq ▸ Nat.le_add_right p q, hp, ?_⟩⟩
    have hnp : n - p = q := by omega
    rwa [hnp]

/-- Any spectral model produces Goldbach pairs. -/
lemma goldbach_of_spectralModel (M : SpectralModel) : Goldbach := by
  intro n hn h4
  obtain ⟨p, hp⟩ := M.nonempty_of_even hn h4
  exact ⟨p, n - p, M.prime_of_mem hp, M.prime_sub_of_mem hp,
    Nat.add_sub_cancel' (M.le_of_mem hp)⟩

/-- Conversely, Goldbach's conjecture yields the canonical spectral model. -/
def spectralModelOfGoldbach (h : Goldbach) : SpectralModel where
  spec := goldbachSpectrum
  prime_of_mem hp := (mem_goldbachSpectrum.1 hp).2.1
  le_of_mem hp := (mem_goldbachSpectrum.1 hp).1
  prime_sub_of_mem hp := (mem_goldbachSpectrum.1 hp).2.2
  nonempty_of_even hn h4 := goldbachSpectrum_nonempty_iff.2 (h _ hn h4)

/-- **Goldbach from a spectral model**, unconditionally.

The named hypothesis `Nonempty SpectralModel` of the schema
`Nonempty SpectralModel → Goldbach` is not an extra assumption at all: it is *equivalent*
to Goldbach's conjecture.  Hence the schema is here stated and proved with no hypotheses,
as an equivalence, the forward direction being the schema itself and the backward direction
the construction of the canonical spectral model. -/
theorem goldbach_from_spectral_model : Nonempty SpectralModel ↔ Goldbach :=
  ⟨fun ⟨M⟩ => goldbach_of_spectralModel M, fun h => ⟨spectralModelOfGoldbach h⟩⟩

/-!
## Unconditional finite content

The canonical spectrum is non-empty at every even `4 ≤ n ≤ 200`; this is checked by the
kernel.  It gives Goldbach's conjecture unconditionally over that range.
-/

set_option maxRecDepth 20000 in
private lemma goldbach_certificate_200 :
    ∀ n ∈ Finset.range 201, (Even n ∧ 4 ≤ n) →
      ∃ p ∈ Finset.range (n + 1), Nat.Prime p ∧ Nat.Prime (n - p) := by decide

/-- The canonical spectrum is non-empty at every even `n` with `4 ≤ n ≤ 200`. -/
theorem goldbachSpectrum_nonempty_of_le_200 {n : ℕ} (hn : Even n) (h4 : 4 ≤ n)
    (hle : n ≤ 200) : (goldbachSpectrum n).Nonempty := by
  obtain ⟨p, hp, hp1, hp2⟩ :=
    goldbach_certificate_200 n (Finset.mem_range.2 (by omega)) ⟨hn, h4⟩
  exact ⟨p, mem_goldbachSpectrum.2 ⟨Nat.lt_succ_iff.1 (Finset.mem_range.1 hp), hp1, hp2⟩⟩

/-- Goldbach's conjecture holds unconditionally for all even `n` with `4 ≤ n ≤ 200`. -/
theorem goldbach_le_200 {n : ℕ} (hn : Even n) (h4 : 4 ≤ n) (hle : n ≤ 200) :
    ∃ p q : ℕ, IsGoldbachPair n p q :=
  goldbachSpectrum_nonempty_iff.1 (goldbachSpectrum_nonempty_of_le_200 hn h4 hle)

/-- The unconditional additive part of Goldbach's circle of ideas: every `n ≥ 2` is a sum of
primes.  Proved by strong induction on `n`. -/
theorem exists_prime_list_sum {n : ℕ} (hn : 2 ≤ n) :
    ∃ l : List ℕ, (∀ p ∈ l, Nat.Prime p) ∧ l.sum = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hp : Nat.Prime n
    · exact ⟨[n], by simpa using hp, by simp⟩
    · have h4 : 4 ≤ n := by
        rcases Nat.lt_or_ge n 4 with h | h
        · interval_cases n <;> simp_all (config := { decide := true })
        · exact h
      obtain ⟨l, hl, hsum⟩ := ih (n - 2) (by omega) (by omega)
      exact ⟨2 :: l, by
        intro p hpmem
        rcases List.mem_cons.1 hpmem with rfl | hpl
        · exact Nat.prime_two
        · exact hl p hpl, by simp [hsum]; omega⟩

end Brockian.GoldbachSchema

