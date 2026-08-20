# Sieve context: the parity problem and the singular-series bridge

*How the constellation-sieve program sits inside classical analytic number theory — the honest
ceiling (the parity problem) and the dictionary from our verified objects to the field's standard
ones (the Hardy–Littlewood singular series, Maynard–Tao admissible tuples). Calibrated against
`terrytao.wordpress.com` (918-post index, 2007–2026).*

---

## 1. The parity problem — our honest ceiling, named

Our constellation results are unconditional **finite** structure theorems; they say nothing about
the infinitude of twin primes or any constellation. The precise reason is a celebrated obstruction,
not a hedge:

> **The parity problem** (Tao, *Open question: the parity problem in sieve theory*, 2007):
> “sieve theory is largely unable to distinguish numbers with an odd number of prime factors from
> an even number.” Any sieve lower bound on the primes is annihilated when weighted by the Liouville
> function `λ(n)`, so pure sieving yields upper bounds and almost-primes, **never** the infinitude of
> primes or twins.

Our exact wheel counts `∏(p − ν_p)` are the **admissibility side of a sieve**; they therefore
inherit the parity barrier. Breaking it requires ingredients outside admissibility data:

- bilinear / Vaughan-type sums (Tao–Green style),
- a relative-density input (primes inside a pseudorandom almost-prime set),
- or Siegel-zero leverage.

References on the blog: [parity problem in sieve theory (2007)](https://terrytao.wordpress.com/2007/06/05/open-question-the-parity-problem-in-sieve-theory/) ·
[a general parity problem obstruction (2014)](https://terrytao.wordpress.com/2014/11/21/a-general-parity-problem-obstruction/) ·
[parity obstruction for binary Goldbach (2014)](https://terrytao.wordpress.com/2014/07/09/the-parity-problem-obstruction-for-the-binary-goldbach-problem-with-bounded-error/) ·
[Erdős 385 — parity & Siegel zeroes (2024)](https://terrytao.wordpress.com/2024/08/19/erdos-problem-385-the-parity-problem-and-siegel-zeroes/).

**How we state scope, going forward:** not merely “we do not prove infinitude,” but
*“the parity problem is the exact obstruction our finite confinement cannot cross; crossing it needs
bilinear sums, a relative-density input, or Siegel-zero leverage — none of which are
admissibility/singular-series facts.”*

---

## 2. The singular-series bridge — our objects are the field's objects

A quiet but important finding of the calibration: the corpus **already speaks the standard
language**; it simply was not presented that way.

### 2.1 Local factor = Hardy–Littlewood local factor

`Brockian.SingularSeries.localFactor` is, verbatim, the classical singular-series local factor:

```
localFactor G p  =  (1 − ν_p/p) · (1 − 1/p)^{−k},   k = |G|,   ν_p = #(G mod p)
```

so `singularSeries G = ∏_p localFactor G p` **is** the Hardy–Littlewood constant `𝔖(G)` that
appears in the Maynard–Tao sieve and the prime-tuple conjectures.

**Verified anchors (AXLE @ lean-4.32.0, axiom-clean):**

| Field object | Our verified theorem |
|---|---|
| Twin factor at `p = 2` (`= 2`) | `SingularSeries.MoreExamples.localFactor_evenPair_two` |
| **Twin odd-prime factor `(p−2)·p/(p−1)²`** | **`SingularSeriesBridge.localFactor_twinGap_odd`** (new) |
| Positivity of that factor for `p ≥ 3` | `SingularSeriesBridge.localFactor_twinGap_odd_pos` (new) |
| `𝔖({0,2}) > 0` (twin singular series) | `SingularSeries.Examples.singular_series_pos_twinGap` |
| `𝔖(G) > 0` for any admissible `G` (unconditional) | `SingularSeries.Convergence.singular_series_pos'` |
| Convergence of the ∞-product | `SingularSeriesConvergence.singularSeriesFinite_tendsto_pos` |

The new `SingularSeriesBridge` module writes the twin factor in the **exact closed form a number
theorist expects**, `(p − 2)·p/(p − 1)²`, so the objects are recognizable on sight.

### 2.2 Admissibility = Maynard–Tao admissibility

`Brockian.AdmissibilityHLCriterion` already defines admissibility in the standard form:

- `OmitsResidue p H` — `H` omits at least one residue class mod `p` (the Maynard–Tao condition);
- `Admissible H := ∀ p prime, OmitsResidue p H`;
- `admissible_iff_nu_lt`, `admissible_iff_card_image_lt`, `admissible_iff_exists_avoiding_start` —
  the equivalences a working paper uses.

Together with `AdmissibilityCRT` / `AdmissibilityKTuple`, we hold the admissible-tuple machinery in
field-standard language and in a verified form — which is genuinely thin in Mathlib.

### 2.3 The constellation counts are the same thing

`ConstellationLocalCount.local_admissible_count_prime` (`p − ν_p`) and
`ConstellationWheel.twin_wheel_count` (`∏(p−2)`) are the integer-count face of the same local data;
`localFactor` is its real-analytic normalization. `local_admissible_count_prime` gives `p − ν_p`;
dividing by `p` and normalizing by `(1−1/p)^k` yields `localFactor`. So the constellation program and
the singular-series program are two faces of one verified object.

---

## 3. Calibration takeaways (full roadmap: the Tao-guided map)

- **Supplement.** Adopt the singular-series / admissible-tuple vocabulary explicitly (done in
  `SingularSeriesBridge` + §2); add a clearly-separated Cramér/random-model heuristic track alongside
  the exact/finite theorems.
- **Guide.** Follow the 254A three-beat exposition (statement → motivation → rigorous proof) and the
  “Lean companion” presentation model (prose ↔ Lean ↔ certificate) — which the lab's proof-drawer
  already embodies.
- **Differentiate.** Our edge is *full independent machine-verification + certificate-per-theorem +
  proof⊕visualization in one artifact*. Honest counterweight: the “geometric confinement / five-point
  spectrum” is a repackaging of classical admissibility through graph spectra — modest novelty as
  frontier mathematics; the defensible value is verification, presentation, and pedagogy.
- **Quality.** Formalize what is genuinely unformalized (admissible-tuple / singular-series facts —
  we already have several); standardize notation to `𝔖` and `(1 − ν_p/p)`; the **Gilbreath** opening
  (Tao's July-2026 deterministic analysis + visualizer) is a concrete, current target — and we already
  hold verified finite Gilbreath facts in `GilbreathConjecture` (`gilbreath_row{1..10}_head = 1`).

Scope, restated: everything here is finite/unconditional; none of it is a proof of any infinitude
conjecture. The parity problem is precisely why.
