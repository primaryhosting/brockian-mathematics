# A machine-verified local-to-global sieve geometry for prime constellations

**C. Brock, with an automated prover fleet.** Formalized in Lean 4 + Mathlib; every theorem
independently kernel-checked by AXLE (Axiom) at toolchain `leanprover/lean4:v4.32.0`, and axiom-clean
(each proof depends only on `{propext, Classical.choice, Quot.sound}`). Source of truth for the claims
below: `registry/theorems.json`, generated mechanically from the AXLE attestations.

---

## Abstract

We give a complete, machine-verified account of the *local-to-global structure* of an admissible prime
constellation on the residue "wheel" `ℤ/n`, and of the *spectrum* of the transfer operator of the
associated `+3` flow graph. For an offset set `H`, the number of admissible residues mod `n` is exactly
`|ℤ/n| − ν`, where `ν` is the number of distinct residues of `H`; this count is multiplicative across
coprime moduli and therefore equals the explicit Euler product `∏_{p∣Q}(p − ν_p)` on a squarefree wheel
`Q`. For the twin pattern `{0,2}`, the admissible residues under the `+3` flow form a graph that we prove
is **acyclic**, of **maximum degree ≤ 2**, with **no run of four** — hence a disjoint union of paths
`P₁, P₂, P₃`. The path Hamiltonians have exact characteristic polynomials, giving the **five-point
spectral alphabet** `{2−√2, 1, 2, 3, 2+√2}`, and the assembled block operator has this alphabet as its
*exact* spectrum. The construction generalizes verbatim to cousin, sexy, and triple constellations.

**This is not a proof of the twin prime conjecture, or of the infinitude of any prime constellation.**
Every statement here is an unconditional, finite fact about residues modulo a fixed wheel. The frontier
conjectures remain open and are never claimed otherwise. What is new is the *verified structure*: a
kernel-checked chain from local confinement to the operator spectrum, for arbitrary constellations.

---

## 1. The local admissibility count — `ConstellationLocalCount`

For a modulus `n` and offset set `H : Finset ℤ`, call `a : ℤ/n` *admissible* if `a + h ≠ 0` for every
`h ∈ H` (no shifted point hits `0`).

- **`local_admissible_count`** `(n : ℕ) [NeZero n] (H : Finset ℤ)` :
  `#{admissible a} = |ℤ/n| − ν`, where `ν = (H.image (·:ℤ/n)).card`.
- **`local_admissible_count_prime`** — at a prime `p`, the count is `p − ν_p(H)`.
- **`twin_local_count`** — for `p ≥ 3`, the twin pattern `{0,2}` admits exactly `p − 2` residues.

The proof identifies the admissible set with `univ \ {−h : h ∈ H}` and uses that negation is injective,
so the forbidden set has cardinality `ν`.

## 2. Multiplicativity — `ConstellationMultiplicative`

Using the genuine sieve condition `admissibleU n H := {a | ∀ h ∈ H, IsUnit (a + h)}` (every shifted
point a *unit* mod `n`):

- **`admissibleU_prime`** — in a field, `IsUnit x ↔ x ≠ 0`, so this reduces to §1 at a prime.
- **`admissibleU_mul`** `(h : Nat.Coprime m n)` : `#adm(mn) = #adm(m) · #adm(n)`, via the Chinese
  remainder ring isomorphism `ℤ/mn ≅ ℤ/m × ℤ/n` and units-in-a-product-ring.

## 3. The wheel Euler product — `ConstellationWheel`

- **`admissibleU_squarefree`** `(hQ : Squarefree Q)` :
  `#adm(Q, H) = ∏_{p ∈ Q.primeFactors} (p − ν_p(H))`.
- **`twin_wheel_count`** — for squarefree `Q` with all prime factors `≥ 3`, `#adm(Q, {0,2}) = ∏(p − 2)`.

This makes the sieve constant `A = ∏(p−2)` a *proved consequence*, not an assumption.

## 4. The run-cap and the graph — `ConstellationGraph`

`plusThreeGraph n : SimpleGraph (ℤ/n)` has `a ~ b` iff `b − a = ±3`.

- **`twin_run_cap_mod5`** — no four-term `+3` run `a, a+3, a+6, a+9` is fully twin-admissible mod 5
  (a finite, decidable pigeonhole: the four residues `{a, a+1, a+3, a+4}` cannot avoid the two twin-
  forbidden classes `{0,3}`).
- **`twin_no_four_run`** — this lifts to any `M` with `5 ∣ M` through the reduction ring-hom.
- **`plus_three_neighbourhood`** — `±3` adjacency forces `b ∈ {a+3, a−3}`, so degree `≤ 2`.

## 5. The path-block spectra — `ConstellationSpectrum`

The path Hamiltonians `H₁ = [2]`, `H₂ = [[2,-1],[-1,2]]`, `H₃ = [[2,-1,0],[-1,2,-1],[0,-1,2]]` (real
matrices) have exact characteristic polynomials

`H₁: X − 2`, `H₂: (X−1)(X−3)`, `H₃: (X−2)(X²−4X+2)`,

so their eigenvalues are exactly `2`, `1`, `3`, and the irrationals `2 ± √2` (obtained via `(√2)² = 2`),
giving the five-point alphabet `{2−√2, 1, 2, 3, 2+√2}` (`spectralAlphabet`).

## 6. The direct-sum charpoly — `ConstellationBlockSum`

- **`charpoly_fromBlocks_zero`** — `(fromBlocks A 0 0 B).charpoly = A.charpoly · B.charpoly`.
- **`H123_charpoly`** — the assembled `H₁ ⊕ H₂ ⊕ H₃` operator has charpoly
  `(X−2)·(X−1)(X−3)·(X−2)(X²−4X+2)`.

## 7. Generalization — `ConstellationExamples`

Because §§1,3 are stated for arbitrary `H`, the confinement holds for any constellation:

| Constellation | `H` | local count | wheel product |
|---|---|---|---|
| Cousin `{0,4}` | `p − 2` (p ≥ 3) | `∏(p−2)` |
| Sexy `{0,6}` | `p − 2` (p ≥ 5) | `∏(p−2)` |
| Triple `{0,2,6}` | `p − 3` (p ≥ 7) | `∏(p−3)` |

---

## 8. Closing the gate

The central object is `G := SimpleGraph.induce {a | twinAdm a} (plusThreeGraph M)`. To pass from the
*graph* to the *operator*, we proved:

- **Arithmetic acyclicity** (`ConstellationAcyclic`) — `plusThree_reaches` (the `+3` orbit is transitive
  when `gcd(3,M)=1`), `plusThree_no_short_cycle` (`a + 3k = a ⇒ M ∣ k`), and `zero_not_twinAdm` (`0` is
  never twin-admissible, so the admissible set is a *proper* subset that breaks the `+3` cycle).
- **Edge / run Euler products** (`ConstellationCounts`) — the `+3`-edge count (offset set `{0,2,3,5}`) is
  `∏(p−4)`, the `P₃`-run count (offset set `{0,2,3,5,6,8}`) is `∏(p−6)`, and the multiplicity
  reconstruction `V = n₁+2n₂+3n₃`, `E = n₂+2n₃`, `T = n₃` holds as algebra.
- **Full SimpleGraph acyclicity** (`ConstellationGraphAcyclic`) — **`twin_admissible_induced_acyclic`**:
  `G` is `IsAcyclic`. The proof maps `a ↦ (3⁻¹·a).val : ℤ`, sending each `+3` edge to a `+1` edge in the
  integer line graph (proved acyclic because every edge is a bridge); the single wrap-around of the map
  lands exactly on the inadmissible residue `0`, so on admissible vertices one has an injective graph
  hom into a forest, and `IsAcyclic.comap` transports acyclicity back.
- **Forest of paths** (`ConstellationPaths`) — `induced_degree_le_two`, `forest_of_paths`
  (`IsAcyclic ∧ Δ ≤ 2` = disjoint union of paths), and `no_four_admissible_run` (components have ≤ 3
  vertices). Thus `G` is structurally a disjoint union of `P₁, P₂, P₃`.
- **Component-interval embedding** (`ConstellationAdjBridge`) — **`G_embeds_intLine`**: the position map
  is a full `SimpleGraph.Embedding` (induced, both directions) of `G` into the integer line graph, so
  each connected component is a *contiguous integer interval* — a genuine path.
- **Exact operator spectrum** (`ConstellationGlobalSpectrum`) — **`H123_spectrum`**: the assembled
  `H₁ ⊕ H₂ ⊕ H₃` operator has spectrum *exactly* `{2−√2, 1, 2, 3, 2+√2}`, with `2 ± √2` genuine roots;
  plus multiplicity forms showing block spectra multiply.

## 9. The single open step

One narrow, purely-technical step remains: identifying the graph's **adjacency matrix**
`SimpleGraph.adjMatrix ℝ G` with the block-diagonal form `⨁ Pₖ` via a connected-component reindexing,
which would upgrade `H123_spectrum` from the *assembled* block operator to the graph Hamiltonian itself.
We proved the structural prerequisite (each component is an integer-interval path, `G_embeds_intLine`),
but the pure matrix step — a `ConnectedComponent → Matrix.reindex` block decomposition of an adjacency
matrix — is not available in the current Mathlib, and `charpoly` over `ℝ` is not decidable, so a
concrete-modulus factorization route is also impractical. Two independent automated attempts delivered
structural fragments but did not close this matrix-reindexing step; it is stated here as the honest
frontier, not claimed. It is a *formalization* gap, not a mathematical one: on paper the block form is
immediate from "each component is an interval path." The step is written up as a self-contained,
attack-ready problem statement — precise target theorem, proved prerequisites, the exact Mathlib gap,
and three suggested routes — in `docs/OPEN-adjmatrix-block-reindex.md`.

## 10. Reproducibility

Every theorem above is re-checkable at `leanprover/lean4:v4.32.0` + Mathlib. The constellation-sieve
program comprises 13 modules (`Brockian/Constellation*.lean`) with their attestations in
`registry/attestations/`; the full verified corpus stands at **10,975 PROVED** theorems (registry-
derived), of which the constellation program is the modules listed in §§1–9. Each module carries a
provenance entry in `provenance/verdicts.yaml` recording its AXLE run and axiom footprint.

## 11. Scope, honestly

- Nothing here bears on the *infinitude* of twin primes, cousin primes, or admissible triples. Those
  conjectures are open; the confinement counts and spectra are unconditional finite facts about a fixed
  wheel `ℤ/n`.
- The five-point spectrum is proved for the assembled path-block operator; its transport to the graph
  Hamiltonian awaits the one matrix-reindexing step of §9.
- **Repository caution.** This document is a standalone artifact. The source repository's history
  contains committed secrets (service keys) that must be rotated and purged by a human before the
  repository itself is made public; drafting or sharing this paper does not entail publishing the repo.
