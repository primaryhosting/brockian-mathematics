# The Constellation Sieve Spectrum — a verified local-to-global geometry of prime constellations

*Every theorem below is machine-checked by AXLE (Axiom) at `lean-4.32.0` + Mathlib, axiom-clean
(⊆ `{propext, Classical.choice, Quot.sound}`), and registered from its attestation. Nothing here is
asserted; it is proved. Modules live in `Brockian/Constellation*.lean`.*

## What this is — and what it is not

This program formalizes, brick by kernel-checked brick, the **local-to-global structure of where a
prime constellation can live on the residue "wheel" ℤ/n**, and the **spectrum of the transfer operator**
of the resulting graph. It is a **finite, unconditional** structure theorem.

**It is NOT a proof of the twin prime conjecture, or of any open conjecture.** It says nothing about
whether infinitely many twins exist. The confinement counts are exact facts about residues modulo a
squarefree wheel; the frontier problems remain open, and this program never claims otherwise.

## The bricks (each an integrated, AXLE-verified module)

**Brick 1 — local admissibility count** (`ConstellationLocalCount`). For a modulus `n` and offset set
`H : Finset ℤ`, a residue `a` is *admissible* when no shifted point `a + h` hits `0`. Then
`#{admissible a} = |ℤ/n| − ν`, where `ν = #{h mod n}` is the number of distinct offset residues. At a
prime `p` this is `p − ν_p(H)`. The **twin confinement**: for `p ≥ 3`, the pattern `{0,2}` admits
**exactly `p − 2`** residues (`twin_local_count`).

**Brick 2 — multiplicativity** (`ConstellationMultiplicative`). Using the genuine sieve condition
`admissibleU` (every `a + h` a *unit* mod `n`), the count is **multiplicative across coprime moduli**:
`admissibleU_mul` proves `#adm(mn) = #adm(m)·#adm(n)` for coprime `m, n` via the Chinese-remainder ring
isomorphism `ℤ/mn ≅ ℤ/m × ℤ/n` and unit-in-product-ring. `admissibleU_prime` bridges to Brick 1.

**Brick 3 — the wheel Euler product** (`ConstellationWheel`). By induction over the prime factorization,
for squarefree `Q`: `#admissibleU(Q, H) = ∏_{p∣Q} (p − ν_p(H))`. Specialized to twins:
`= ∏_{p∣Q} (p − 2)`. This makes the sieve constant `A = ∏(p−2)` a **proved consequence**, not an
assumption — closing a gate the original twin-sieve write-up left open.

**Brick 4 — the run-cap and the graph** (`ConstellationGraph`). `twin_run_cap_mod5`: **no four-term
`+3` run `a, a+3, a+6, a+9` is fully twin-admissible mod 5** — a finite, decidable pigeonhole (the four
residues occupy distinct classes but twin-admissibility forbids two of five). `twin_no_four_run` lifts
it to any `M` divisible by 5 through the reduction ring-hom (units map to units). `plusThreeGraph` is a
genuine `SimpleGraph (ℤ/n)`; `plus_three_neighbourhood` bounds degree by 2. Together: the wheel graph
decomposes into paths of length **at most 3** — proved, not asserted.

**Brick 5 — the operator spectrum** (`ConstellationSpectrum`). The path-graph Hamiltonians are genuine
real matrices `H₁ = [2]`, `H₂ = [[2,-1],[-1,2]]`, `H₃ = [[2,-1,0],[-1,2,-1],[0,-1,2]]`. Their **exact
characteristic polynomials** are proved: `X−2`, `(X−1)(X−3)`, `(X−2)(X²−4X+2)`. Hence the eigenvalues
are exactly `2`, `1`, `3`, and the irrationals `2 ± √2` (the last via `(√2)² = 2`), giving the
**five-point spectral alphabet** `{2−√2, 1, 2, 3, 2+√2}`. This is the operator theorem the earlier
(rejected) twin-sieve package never constructed — it had multiplicity bookkeeping but no matrix.

**Brick 6 — the block assembly** (`ConstellationBlockSum`, in progress). The direct-sum characteristic
polynomial law: the spectrum of a block-diagonal assembly of the path Hamiltonians is the product of
their spectra, giving the global multiplicities.

## It is a general constellation theory (`ConstellationExamples`)

Bricks 1 and 3 are stated for an arbitrary offset set `H`, so the confinement applies to *any* prime
constellation. Verified instances beyond twins:

| Constellation | `H` | local count | wheel product |
|---|---|---|---|
| Cousin primes | `{0,4}` | `p − 2` (`p ≥ 3`) | `∏_{p∣Q}(p − 2)` |
| Sexy primes | `{0,6}` | `p − 2` (`p ≥ 5`) | `∏_{p∣Q}(p − 2)` |
| Prime triple | `{0,2,6}` | `p − 3` (`p ≥ 7`) | `∏_{p∣Q}(p − 3)` |

Each is proved by computing `ν_p(H)` exactly (the offsets are pairwise distinct mod `p` above the stated
bound) and instantiating the general Brick-1 (local) and Brick-3 (wheel) theorems. The infinitude of
cousin primes, sexy primes, or admissible triples remains **open** — unaffected by these finite counts.

## Closing the gate — mostly done (see the paper)

The graph→operator gate has been driven nearly to a full close (all AXLE-verified @4.32, axiom-clean):
- **Arithmetic acyclicity** (`ConstellationAcyclic`), **edge/run Euler products** `∏(p−4)`, `∏(p−6)` +
  reconstruction `V=n₁+2n₂+3n₃` (`ConstellationCounts`).
- **Full SimpleGraph acyclicity** (`ConstellationGraphAcyclic.twin_admissible_induced_acyclic`) — the
  induced twin-admissible `+3` graph is `IsAcyclic`, via a `pos`-map embedding into the integer line
  graph. This is the piece the earlier twin-sieve campaign never formalized.
- **Forest of paths** (`ConstellationPaths`) — degree ≤ 2, `IsAcyclic ∧ Δ≤2`, no 4-vertex run: the graph
  is a disjoint union of `P₁, P₂, P₃`.
- **Component-interval embedding** (`ConstellationAdjBridge.G_embeds_intLine`) — each component is a
  contiguous integer interval (a genuine path).
- **Exact operator spectrum** (`ConstellationGlobalSpectrum.H123_spectrum`) — the assembled block
  operator's spectrum is *exactly* `{2−√2, 1, 2, 3, 2+√2}`.

**The matrix-infrastructure step is now closed** (independently AXLE-verified @ `lean-4.32.0`,
axiom-clean; Codex lane). `GraphComponentMatrix` proves the general fact — a finite graph's vertex type
is canonically `≃ Σ` of its connected-component fibers (`componentEquiv`), any matrix with vanishing
cross-component entries reindexes to a `blockDiagonal'` (`reindex_componentEquiv_eq_blockDiagonal'`), and
its characteristic polynomial factors as `∏` of the component-block charpolys
(`charpoly_eq_prod_componentBlocks`), specialized to `adjMatrix` and to `r•I − A`. `ConstellationGateClose`
applies it to the actual twin graph: **`graph_hamiltonian_charpoly_components`** — the real graph
Hamiltonian's charpoly `= ∏` over its genuine connected components. This closes the `adjMatrix`→block
reindexing that the earlier automated attempts could not.

**The one remaining open step** is now the *combinatorial* residual: identify each actual component
block's charpoly with `H₁`, `H₂`, or `H₃` (each component is a `P₁/P₂/P₃`, already proved structurally by
`G_embeds_intLine` + `forest_of_paths`) and group the factors by the arithmetic multiplicities `n₁,n₂,n₃`,
yielding the actual graph's spectrum `= {2−√2, 1, 2, 3, 2+√2}`. This packaging is genuinely open (WIP in
`SieveSpectrumDeletion`), and — as always — it remains a finite structural result, *not* a proof of
twin-prime infinitude. Full write-up: `docs/CONSTELLATION-SIEVE-PAPER.md`.
