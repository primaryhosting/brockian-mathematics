# Brockian Verified Mathematics — Program Status

*A live status report. Every number here is derived from `registry/theorems.json` (mechanically
generated from AXLE attestations); nothing is hand-asserted. Regenerate with
`python3 scripts/gen_registry.py`.*

## Snapshot

| Metric | Value |
|---|---|
| Theorems **PROVED** (AXLE-verified, axiom-clean) | **10,381** |
| Open problems mapped on the frontier | **34** |
| **CONDITIONAL** reductions (honest, named-hypothesis) | 21 |
| **DISCHARGED** (conditional → unconditional) | 6 |
| Open-conjecture markers (unproven `def`s) | 38 |
| Commits in the last 6 hours | 34 |

Verifier: **AXLE (Axiom)** at `lean-4.32.0` + Mathlib. Every theorem is independently kernel-checked,
axiom-clean (⊆ `{propext, Classical.choice, Quot.sound}`), and CI-gated (`lake build` + AXLE +
overclaim-firewall + no-theater lint) on every commit.

## What's been built — three pillars

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

## Strategy — three parallel lanes, one firewall

- **Frontier lane** (agent fleet, every 15 min) — decide-checkable partial results, one new
  open-problem module per cycle: concrete verified instances + structural theorems + an honestly
  stated open conjecture. Reliable breadth engine.
- **Hard-proof lane** (Harmonic / Aristotle) — heavy theorems offloaded to stronger compute (Euler's
  form for odd perfect numbers, Mersenne-exponent-prime, Korselt⇒Carmichael, Wilson). Solutions return,
  get AXLE-verified, and become new PROVED entries. Currently 4 jobs confirmed queued.
- **Depth lane** (corpus loop, parallel) — sustained expansion of the verified core; shares the same
  registry + firewall; coherence-gated so nothing lands unbacked.

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

- **Widen the atlas** — keep adding open problems with verified proved-regions.
- **Discharge conditionals** — convert CONDITIONAL reductions to unconditional PROVED where the named
  hypothesis is a classical theorem (free-Laplacian / Kato essential self-adjointness).
- **Deepen** — land genuine hard theorems via Harmonic's compute.
- **Make it legible** — public verified labs so the work is inspectable, not just asserted.

## Next steps

- Harvest returning **Harmonic proofs** (Euler form, Mersenne-exponent, Korselt⇒Carmichael, Wilson)
  and integrate the AXLE-verified ones.
- Continue the **15-minute frontier rotation** (Firoozbakht, Erdős–Graham, practical numbers, …).
- Refresh the **Lovable labs** (`/frontier` + `/why-five` on Prime Explorer 3D, project `dd8308ac`) as
  the frontier grows; publish to prod.
- Submit **more hard targets** to Harmonic in parallel.

## The discipline, restated

Open conjectures are recorded as unproven definitions and never discharged. Any theorem whose proof
would rest on an open node is rejected by the firewall. RH-conditional nodes are never submitted to
Harmonic — proving them would be "solving RH." More compute only ever adds real, verified results;
it never fabricates.
