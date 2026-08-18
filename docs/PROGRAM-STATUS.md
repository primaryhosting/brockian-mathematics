# Brockian Verified Mathematics — Program Status

> **Staleness note (2026-08-18):** Snapshot last updated 2026-08-04. The live
> `registry/theorems.json` now records **PROVED 11,126 / DISCHARGED 7** (confirmed as a verified
> no-op regeneration in commit `ee94165`); the "Commits in the last 6 hours" figure is frozen from
> snapshot time. Regenerate before quoting numbers. Note: no script currently regenerates this
> file — `scripts/gen_program_report.py` writes `docs/PROGRAM-REPORT.md` (itself stale at PROVED
> 10,568), and `scripts/gen_registry.py` regenerates the registry, not this doc; numbers here must
> be synced by hand from the registry summary until a generator exists.

*A status report. Numbers below are copied from the `registry/theorems.json` summary (mechanically
generated from AXLE attestations) at snapshot time; sync by hand from the registry summary after
`python3 scripts/gen_registry.py`.*

## Snapshot

| Metric | Value |
|---|---|
| Theorems **PROVED** (AXLE-verified, axiom-clean) | **10,975** |
| Open problems mapped on the frontier | **34** |
| **CONDITIONAL** reductions (honest, named-hypothesis) | 20 |
| **DISCHARGED** (conditional → unconditional) | 7 |
| Open-conjecture markers (unproven `def`s) | 40 |
| Commits in the last 6 hours | 34 |

Verifier: **AXLE (Axiom)** at `lean-4.32.0` + Mathlib. Entries marked `PROVED` carry independent
kernel-check attestations and acceptable axiom sets (normally a subset of
`{propext, Classical.choice, Quot.sound}`). Harvest candidates additionally pass statement-fidelity,
no-theater, registry-consistency, and manifest checks before integration. Full local `lake build`
remains a CI/local verification layer when compute is available; the 2026-08-03 harvest used AXLE
instead of the compute-constrained workstation.

## What's been built — four pillars

1. **Why Five (unification).** The pentagon, the golden ratio, and the number five proved to be *one
   phenomenon* across four independent lenses — spectral (φ−1 ∈ spec C₅), Galois (quadratic real
   cyclotomic field), trigonometric (2cos 2π/5 = φ−1), representation-theoretic (the golden eigenspace
   is a forced 2-dim D₅ subrepresentation) — plus the divisibility law φ−1 ∈ spec(Cₙ) ⟺ 5∣n.
   See `docs/WHY-FIVE.md`.
2. **The Open Frontier (breadth).** 34 famous unsolved problems, each with a verified proved-region and
   a precisely-drawn open boundary. Contains genuine structural theorems (11 is the *unique*
   even-length palindromic prime; Rₙ prime ⇒ n prime; Fermat numbers pairwise coprime; 78557 is
   Sierpiński and 509203 is Riesel via full covering-congruence proofs) and proved inter-problem
   implications (Oppermann ⇒ Legendre; Mersenne ⟺ even-perfect; superperfect ⇒ Mersenne-prime).
   See `docs/OPEN-FRONTIER.md`.
3. **The honesty firewall (trust).** A three-layer overclaim firewall that *rejected* dishonest inputs
   (an RH-cluster proof with 4 exact gaps; a false Erdős paper) and refuses to mark any conjecture
   "solved." Every "OPEN" is genuinely open — the refusal is the moat.
4. **Unbounded operator theory (depth).** The concrete harmonic-oscillator Schwartz core is dense and
   symmetric; deficiency-trivial ESA is equivalent to a self-adjoint graph closure; weighted-Rellich
   factorizations imply compact unit resolvents; and those compact resolvents have nonzero point
   spectrum of finite multiplicity. Maximal quadratic multiplication now has explicit non-real
   resolvents and is essentially self-adjoint, and unitary transfer gives a Fourier-defined free
   Laplacian with ESA. The physically normalized multiplier is now correctly `4*pi^2*xi^2`, and
   the full bounded Kato-Rellich theorem is unconditional and applied to the concrete `-d^2+V`
   operator. Identifying the normalized spectral operator with the Schwartz differential core,
   oscillator ESA, and the concrete weighted compact embedding remain explicit analytic blockers.

## Strategy — three parallel lanes, one firewall

- **Frontier lane** (curated) — accept a new finite module only when it tests a new general theorem or
  adds a materially useful structural reduction. Automatic range/count expansion is paused.
- **Hard-proof lane** (Harmonic / Aristotle) — heavy theorems offloaded to stronger compute. A large
  **moonshot corpus** was harvested this session: ~60 famous classical theorems proved by Aristotle,
  each **independently AXLE-verified @lean-4.32.0** and axiom-clean before integration — Zsygmondy,
  Turán, Schur, Erdős–Szekeres, Dilworth, Mirsky, Cayley's formula, Van der Waerden, Sperner, LYM,
  Perron–Frobenius, Birkhoff–von Neumann, Pell, Thue, Proth, Pépin, quadratic Gauss sum, Cauchy–Davenport,
  Mason–Stothers, Machin, Binet, Zeckendorf, derangements, e² irrational, Menelaus, Ceva, Heron, Ptolemy,
  Napoleon, Viète, British-flag, Hermite–Hadamard, and more. The gate rejected every return that failed
  our 4.32 kernel, carried a `sorry`, cited a phantom (non-core) lemma, or failed the axiom-footprint
  probe — those were re-queued via `aristotle continue`, not force-fit. Earlier hard theorems also
  harvested and integrated, each AXLE-verified @4.32 and axiom-clean:
  Euler's form for odd perfect numbers, Mersenne-exponent-prime, Korselt⇒Carmichael (Fermat little
  theorem for all bases), the full Wilson iff, odd-perfect ≡ 1 mod 4, every even perfect number is
  triangular, the two-coin Frobenius representability bound, and the **Erdős–Ginzburg–Ziv** zero-sum
  theorem (a cornerstone of additive combinatorics). The discipline that emerged: *Harmonic proposes,
  our AXLE @4.32 disposes* — three returns were **rejected** at the gate: two built against the Mathlib
  Archive (4.28 surface) and one relied on numerals reducing definitionally (`1 % 9` ≠ `1` at 4.32);
  all were re-queued with corrective instructions (no-Archive / explicit `omega` mod-closes). A returned
  tarball once carried the wrong label — the namespace guard caught it and it integrated under its true
  name. A 24-archive audit on 2026-08-03 additionally integrated Wolstenholme and Kummer, quarantined
  a Lean-4.28-only Sylvester-Schur return, and rejected duplicate attestations. Of the operator jobs,
  bounded Kato-Rellich is integrated, the unscaled Fourier target was correctly refuted, oscillator ESA
  returned without a proof, and compact resolvent plus the corrected Fourier target remain active.
  Independent verification, not the upstream claim, is
  authoritative. See `docs/ARISTOTLE-HARVEST-2026-08-03.md`.
- **Depth lane** (primary) — oscillator ESA, the concrete weighted Rellich embedding, unbounded
  spectral mapping, and Mathlib extraction of the general Weyl/Cayley results.

## The frontier (34 problems, by family)

- **Prime gaps & distribution:** Twin, Sophie Germain, Polignac (cousin/sexy), Andrica, Legendre
  (Landau 3), Oppermann, Brocard-gap, Landau n²+1 (Landau 4), Gilbreath.
- **Prime forms & exponent constraints:** Mersenne / even perfect, Fermat, Repunit, Wilson, Sierpiński,
  Riesel, Cullen–Woodall, Fortunate, Palindromic, Ruth–Aaron.
- **Perfect & divisor-sum family:** Odd perfect, Superperfect, Hyperperfect, Quasiperfect, Unitary
  perfect, Amicable, Betrothed, Weird, Ore harmonic, Perfect totient.
- **Elementary & classic:** Erdős–Straus, Collatz, Lehmer totient, Giuga, Carmichael / Korselt,
  Brocard n!+1.

Emergent thread — the **"does an odd X exist?"** cluster: odd perfect, odd Giuga, odd weird, odd
superperfect, odd harmonic (Ore). Five ancient existence questions sharing one shape.

## Goals

- **Deepen the general core** — prioritize reusable analytic and algebraic theorems over raw counts.
- **Discharge conditionals** — convert CONDITIONAL reductions to unconditional PROVED where the named
  hypothesis is a classical theorem (free-Laplacian / Kato essential self-adjointness).
- **Deepen** — land genuine hard theorems via Harmonic's compute.
- **Make it legible** — public verified labs so the work is inspectable, not just asserted.

## Next steps

- Poll and audit the two remaining Harmonic operator targets; port every return to Lean 4.32 before AXLE
  integration.
- Prove the Schwartz/Fourier intertwining theorem, then use it to transfer the spectral free-Laplacian
  ESA result to the intended differential operator.
- Prove **oscillator ESA** and instantiate the concrete **weighted Rellich** compact embedding.
- Add unbounded spectral mapping and eigenvalue isolation after compact resolvent is instantiated.
- Prepare `WeylUpstream`, `WeylMultiplicationUpstream`, `WeylKatoRellich`, and the
  compact-eigenspace theorem as Mathlib-quality submissions.
- Refresh the **Lovable labs** (`/frontier` + `/why-five` on Prime Explorer 3D, project `dd8308ac`) as
  the frontier grows; publish to prod.
- Submit **more hard targets** to Harmonic in parallel.

## The discipline, restated

Open conjectures are recorded as unproven definitions and never discharged. Any theorem whose proof
would rest on an open node is rejected by the firewall. RH-conditional nodes are never submitted to
Harmonic — proving them would be "solving RH." More compute only ever adds real, verified results;
it never fabricates.
