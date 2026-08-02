# QuantumProof Formal Targets Inventory

**Agent:** QP-INVENTORY  
**Date:** 2026-08-02  
**Maps to:** Verified Intelligence deploy vector — QuantumProof × IonQ / PQC  
**Companion:** [2026-08-02-verified-intelligence-strategy-brief.md](./2026-08-02-verified-intelligence-strategy-brief.md)

**Registry SSOT (live tip):** `/Users/acutis/Projects/brockian-mathematics/REGISTRY.md`  
**Counts at inventory time:** PROVED **1477** · DEFINITION **306** · CONDITIONAL **21** · DISCHARGED **6** · CONJECTURE **1** (Lean 4.32.0, AXLE-attested).  
**Rule:** Partner language must match this registry (or a pinned commit export), not campaign/pitch totals.

---

## 1. Current product stage

| Layer | What exists | Maturity | Formal/proof status |
|-------|-------------|----------|---------------------|
| **Migration scanner** | `Projects/QuantumProof/migration-scanner` (TS/Node, TLS/PEM scan, vulnerability score + roadmap); `migration-scanner-demo` (Python/Docker samples) | **Prototype / top-of-funnel demo** — heuristic score, not compliance-grade CBOM | **No** Lean props over scan outputs; product claim of “audit-grade proof artifacts” is aspirational |
| **BSH (Brockian Spectral Hash)** | `quantumproof-bsh/` (Rust `bsh-core`, WASM, KAT vectors, CLI); `bsh-rust/` sibling; NIST packet under `docs/nist_submission/` + `nist-submission/` | **Research implementation** — not production-ready | Math *motif* (D₅, φ, pentagonal constants) is registry-backed; **sponge security, uniformity-as-crypto, and bit-level correctness are not** registry PROVED |
| **NIST / IP packaging** | Full bundle drafts, counsel packets, provisional drafts, board memos; `00_DO_NOT_SEND_UNTIL_IP_CLEARANCE.txt` | **Packetized, hold for clearance** | Spec §6 cites old 53-theorem corpus; live registry is larger but still **not** a BSH security proof |
| **Formal claims (public)** | Concept summary, investor one-pager, TQC pitch deck, arXiv draft `brockian-fibonacci-anyon` | **Marketing + research narrative** ahead of product | Strong algebraic substrate in Brockian core; **anyon/TQC packaging is marketing-heavy** (see §4) |
| **QRNG bridge** | `edge-functions/qrng-bridge` — ANU QRNG → CSPRNG fallback, chi-squared score field | **Thin service** | Entropy *scoring* is operational; **no** formal model of quantum entropy or source authentication |
| **KMS bridge** | AWS/Azure wrap proxy for BSH-derived keys | **Proxy design** | No formal hybrid-KEM / wrap lemmas |
| **Lean assets co-located with QP** | `riemann_labs_lean_snapshot/` (names only — **0-byte stubs**); `lean-exporter/brockian_proofs.json` (legacy campaign export ~1379 “proven”); live proofs in **brockian-mathematics** | Snapshot **not usable** | **Canonical corpus:** `Projects/brockian-mathematics` only |
| **IonQ** | Investor materials: **$10k research grant** (QPU jobs / R&D signal) | Partnership **signal**, not a shipped joint product | Demo path should be **registry-badged lemmas under stated assumptions**, not “quantum AI” |

**Honest stage label:** *PQC migration demo + BSH research IP + verified-math research bridge.*  
The Verified Intelligence **deploy** vector is defined as: formalize small security/entropy/hybrid claims → AXLE/registry → evidence attached to scanner/migration/QPU post-processing — **not** “full TQC stack verified.”

### Asset map (paths)

| Asset | Path |
|-------|------|
| Migration scanner | `/Users/acutis/Projects/QuantumProof/migration-scanner` |
| BSH ref impl | `/Users/acutis/Projects/QuantumProof/quantumproof-bsh` |
| NIST hold pack | `/Users/acutis/Projects/QuantumProof/quantumproof-bsh/docs/nist_submission` |
| BSH formal/NIST export | `/Users/acutis/Projects/QuantumProof/docs/ip/QUA-17_BSH_Formal_Spec_NIST_v1.1_export_2026-04-27.md` |
| TQC pitch | `/Users/acutis/Projects/QuantumProof/brockian-tqc-pitch-deck.md` |
| Anyon paper draft | `/Users/acutis/Projects/QuantumProof/arxiv-paper/brockian-fibonacci-anyon.tex` (+ copy under brockian-mathematics `paper/`) |
| QRNG / KMS | `/Users/acutis/Projects/QuantumProof/edge-functions` |
| Live Lean + registry | `/Users/acutis/Projects/brockian-mathematics` (`Brockian/`, `REGISTRY.md`, `registry/theorems.json`) |
| D₅ / golden / metallic / kernel | `Brockian/D5*.lean`, `Core.lean`, `MetallicFamily.lean`, `MetallicRealization.lean`, `TransitionKernel.lean`, `Equidistribution*.lean` |

---

## 2. Table of formal targets

Status legend:

- **proved in Brockian** — name appears PROVED (or DEFINITION) in live registry with AXLE @ lean-4.32.0  
- **draft** — stated in Lean module comments / paper / NIST math framing but open, conditional, or incomplete  
- **marketing-only** — pitch/spec language without a matching registry PROVED badge for that claim  
- **missing** — needed for IonQ/PQC deploy vector; no artifact

| id | statement sketch | status | priority for IonQ demo |
|----|------------------|--------|------------------------|
| **QP-PHI-01** | φ² = φ+1; φ > 1; Binet formula | **proved in Brockian** (`Core.phi_sq`, `Core.binet_formula`, …) | **P0** (demo substrate; already done) |
| **QP-FIBQ-01** | Fibonacci Q-matrix `[[1,1],[1,0]]` has charpoly X²−X−1; φ is eigenvalue | **proved in Brockian** (`MetallicRealization.metallicMatrix_one`, `fibQ_charpoly`, `fibQ_mulVec_golden`, `golden_hasEigenvalue`) | **P0** (honest “Fibonacci matrix” story without anyon physics) |
| **QP-MET-01** | Metallic means M_a as eigenvalues of `[[a,1],[1,0]]`; trace/det identities | **proved in Brockian** (`MetallicRealization.*`) | P1 (generalization; optional demo) |
| **QP-D5-01** | D₅ group / faithful action on C₅; Aut(C₅) ≅ D₅ | **proved in Brockian** (`Automorphism*`, `D5Representation`, character/isotypic modules) | **P0** (BSH motif + TQC “braid algebra” *algebra only*) |
| **QP-D5-02** | D₅ Laplacian / adjacency modes; golden appears in C₅ spectrum | **proved in Brockian** (`D5LaplacianModes`, `Connectivity*`, `Spectral.golden_unique_to_five`) | P1 (spectral narrative) |
| **QP-TK-01** | Gap-g transition kernel on ZMod q; twin forbidden transition; admissible counts | **proved in Brockian** (`TransitionKernel.*`) | P1 (sieve/kernel story; **not** named “fusion matrix”) |
| **QP-EQ-01** | Combinatorial admissible-config counts / finite equidistribution scaffolds | **proved in Brockian** (many `Equidistribution*` PROVED); full asymptotic equidistribution **CONDITIONAL** | P2 (supports BSH math *motif* only) |
| **QP-ANYON-01** | Twin-prime kernel **is** Fibonacci anyon fusion matrix N_τ | **marketing-only** (pitch + arXiv draft); **0** registry hits for fusion/anyon | **Do not demo as PROVED** |
| **QP-ANYON-02** | Spectral gap ⇒ topological error threshold / gate fidelity bounds | **marketing-only** | **Do not claim** |
| **QP-ANYON-03** | Braid-group / R-matrix / pentagon equation for Fibonacci anyons | **missing** (D₅ ≠ braid-group anyon calculus) | P3 research |
| **QP-BSH-01** | φ-const = ⌊2⁶⁴(φ−1)⌋; pentagonal/D₅ rotation constants well-defined | **missing** as named Lean props over BSH constants (φ algebra exists) | **P0** (2-week AXLE targets) |
| **QP-BSH-02** | BSH-256 permutation is a bijection / invertible on (ℤ/2⁶⁴)⁵ | **missing** | P1 |
| **QP-BSH-03** | BSH sponge capacity-c security / indifferentiability | **missing** (NIST spec explicitly disclaims) | P3 (standard crypto assumptions; not “Brockian theorem”) |
| **QP-BSH-04** | “Mixing layer uniformity is a theorem ⇒ BSH is first hash with proven uniformity” | **marketing-only** / **overclaim** — registry equidistribution is about **prime-pair configs on ZMod**, not BSH state diffusion | **Honesty block** |
| **QP-BSH-05** | Reference impl matches formal bit-model (KAT ⇔ Lean `eval`) | **missing** (KATs exist in Rust/JSON only) | P1 |
| **QP-SCAN-01** | Classification Vulnerable / Hybrid / PQC-Compliant is sound w.r.t. a threat model | **missing** | P2 product formalization |
| **QP-HYB-01** | Hybrid KEM: classical OR PQC encapsulation succeeds under stated model | **missing** | **P0** IonQ-adjacent *crypto* demo |
| **QP-QRNG-01** | Source-authenticated entropy: if source = `anu_qrng` then bytes satisfy stated interface contract | **missing** (runtime only) | **P0** IonQ-facing |
| **QP-QRNG-02** | Chi-squared score thresholds imply statistical uniformity of samples (under i.i.d. model) | **missing** | **P0** (small formal stats lemma) |
| **QP-NIST-01** | NIST submission corpus claims aligned with live registry export | **draft** (old 53/sorry figures in QUA-17 §6) | P1 packaging |
| **QP-SNAP-01** | `riemann_labs_lean_snapshot/*.lean` as shippable proofs | **missing** (empty stubs) | Fix: delete or replace; never cite |

---

## 3. Top 5 smallest formal targets (AXLE-verifiable in ~2 weeks)

These are deliberately **small**, **assumption-scoped**, and **demoable** next to a scanner or QPU/hybrid job. Prefer new tiny modules under Brockian (or a `QuantumProofFormal/` package) that re-export existing PROVED φ/D₅ lemmas rather than reopening Weyl/RH.

| # | Target id | Lean statement sketch (minimal) | Why it fits 2 weeks | IonQ/PQC use |
|---|-----------|----------------------------------|---------------------|--------------|
| 1 | **QP-FIBQ-01 (export)** | Package existing `fibQ_charpoly` / `fibQ_mulVec_golden` / `metallicMatrix_det` as a single **demo theorem list** with registry IDs | **Already PROVED** — work is export + attestation hygiene, not invention | “Machine-checked Fibonacci transfer matrix spectral data” without anyon claims |
| 2 | **QP-BSH-01** | `phi_const_u64 = ⌊(2^64 : ℝ) * (phi - 1)⌋` (or integer form via floor lemmas) + `pentagonal n = n(3n-1)/2` table of first 10 matches BSH constants | Pure arithmetic; finite `decide`/`native_decide`-free pattern already used in Core | Ties BSH “nothing-up-my-sleeve” constants to verified φ |
| 3 | **QP-QRNG-02** | For a fixed sample length N and bin count k: under model “uniform i.i.d. on {0..255}”, chi-squared statistic definition + critical-value inequality as a **Prop** on the *score function*, not on physical QRNG | Finite combinatorics / real inequalities; no hardware model | QPU or ANU bytes → classical score → **proved meaning of the score** |
| 4 | **QP-HYB-01 (toy)** | Abstract hybrid encapsulation: `success ↔ (class_ok ∨ pqc_ok)` (or AND-hybrid policy variant) as pure Prop; one lemma that downgrade is impossible under “verifier requires both” | ~50–100 lines of abstract crypto **model**, no lattice hardness | Partner language: *provable under stated composition assumptions* |
| 5 | **QP-BSH-02 (lite)** | On a **toy** state `(ZMod 2^w)^5` with w small (e.g. w=4 or 8) or abstract group action: D₅ rotate/reflect generators form a **finite group action** / permutations of coordinates (reuse D₅ PROVED) + one invertible round schedule lemma | Reuse `D5*` / `Automorphism.Full`; avoid full 64-bit sponge | Shows “BSH geometry is group-theoretic” without claiming collision resistance |

**Explicitly out of 2-week scope:** full BSH-256 bijectivity on 320-bit state; sponge indifferentiability; anyon braiding; RH; global equidistribution asymptotics (CONDITIONAL).

---

## 4. Honesty risks (TQC pitch vs registry)

| Risk | Pitch / NIST language | Registry / code reality | Severity |
|------|----------------------|-------------------------|----------|
| **Theorem count inflation** | TQC deck: “2,023 machine-verified theorems”; concept summary “1,300+”; lean-exporter ~1379 “proven” | Live **PROVED 1477** (different corpus, different era, different gate). Paper `theorem_table.md` can lag (e.g. 863). | **High** — always pin commit + registry hash |
| **Anyon identity** | “Twin-prime kernel **is** Fibonacci anyon fusion matrix”; “first machine-verified foundations for Fibonacci anyons” | PROVED: Fibonacci **Q-matrix** eigenvalues, D₅ reps, transition kernels for **prime gaps**. **No** fusion/anyon/N_τ/braid lemmas | **Existential** if sold as TQC product |
| **Spectral gap → fault tolerance** | Gap = topological protection; error decays with system size | Algebraic gap facts for φ/C₅ are PROVED; **physics/QEC implication is not formalized** | High |
| **BSH “proven mixing uniformity”** | QUA-17: uniformity of mixing is a *theorem* via Dihedral Equidistribution | Equidistribution modules prove **combinatorial/sieve** facts; several **global** equidistribution results are **CONDITIONAL**. Spec itself admits Lean does **not** prove sponge security | High |
| **BSH implementation vs story** | D₅-structured permutation hash | Audit issues in QUA-17 §10: capacity 64 bits, reflection self-swap, sequential mutation breaking group structure, IV from SHA-512, etc. | High for NIST/product |
| **NIST readiness** | Bundles built | `DO_NOT_SEND_UNTIL_IP_CLEARANCE`; patent status still TBD in investor memo | Medium |
| **Empty Lean snapshot in QP repo** | Suggests local Lean proofs | **0-byte** files under `riemann_labs_lean_snapshot/` | High if partners open the folder |
| **Migration “formal verification”** | Public concept: Lean proofs of KEM/signature/hybrid properties | Scanner is heuristic TLS/code inventory; **no** formal artifacts in repo | Medium–High |
| **QRNG “hardware-validated entropy”** | Product language | Edge function: ANU API optional, **silent CSPRNG fallback** | Medium |
| **Aristotle campaign vs AXLE registry** | Pitch cites Aristotle projects / older Lean 4.24 | Production gate is **AXLE @ 4.32** + axiom cleanliness; dual-prover story is real but **badges must say which** | Medium |

**Firewall sentence for partners:**  
*Algebra of φ, D₅, and the Fibonacci transfer matrix is machine-verified. Topological anyon models, BSH collision resistance, and enterprise PQC compliance proofs are not claimed as PROVED unless a registry row says so.*

---

## 5. Recommended first IonQ joint demo scope

### Name
**“Verified Intelligence on a Quantum-Adjacent Artifact”** — hybrid entropy + composition lemma + registry badge.

### In scope (4–6 weeks engineering + 2 weeks formal polish)

1. **Job:** IonQ QPU (or IonQ-accessible hybrid path) produces a small bitstring *or* classical simulation placeholder with the same interface.  
2. **Classical post-process:** QuantumProof QRNG/KMS-style pipeline records `source`, `bytes`, `chi2_score`, timestamp, job id.  
3. **Formal layer (only what is true):**  
   - Badge **A:** re-export **QP-FIBQ-01 / QP-PHI-01** (registry PROVED) as the *mathematical* credibility surface (“we check algebra the same way we check your claims”).  
   - Badge **B:** new **QP-QRNG-02** lemma: *meaning of the chi-squared score under i.i.d. uniform model*.  
   - Badge **C (optional if ready):** **QP-HYB-01** toy hybrid policy lemma.  
4. **Deliverable UI:** one-pager + torus/registry-style badges: each PROVED name → `registry/theorems.json` entry + AXLE env.  
5. **Scanner hook (optional):** scan a demo domain → CBOM row “entropy source: IonQ job / formal status: Badge B.”

### Out of scope (first demo)

- Fibonacci anyon braiding on IonQ hardware  
- BSH as NIST-finalist or “proven secure hash”  
- Claims that IonQ qubits implement Brockian D₅ physics  
- Full enterprise migration formal verification  

### Success criteria

| Criterion | Pass condition |
|-----------|----------------|
| Honesty | No PROVED badge without registry name + attestation |
| Demo time | < 10 minutes live: job → score → badge |
| Math credibility | ≥ 1 pre-existing PROVED (φ/fibQ/D₅) + ≥ 1 new AXLE-verified IonQ-facing lemma |
| Partner language | “Under stated assumptions …” matches CONDITIONAL/OPEN discipline from strategy brief |

### Sequencing vs strategy brief

Aligns with strategy brief **§5.1 / Phase C**: *1–2 formal security/entropy lemmas end-to-end with registry badges*, not a TQC platform launch.

---

## Appendix A — Registry anchors useful for QP narrative

| Theme | Example PROVED names (non-exhaustive) |
|-------|----------------------------------------|
| Golden / Fibonacci algebra | `Brockian.Core.phi_sq`, `Core.binet_formula`, `MetallicRealization.fibQ_charpoly`, `fibQ_mulVec_golden` |
| Metallic family | `MetallicFamily.metallicMean_sq`, `metallic_one_unique_to_five` |
| D₅ | `Automorphism.Full.aut_equiv_dihedral`, `D5Isotypic.*`, `D5FourierInversion.fourier_inversion` |
| Transition kernel | `TransitionKernel.totalSum_count`, `twin_admissible_singleton`, `forbidden_transition` |
| Equidistribution (finite) | `EquidistributionUniformity.equidistribution_three`, finite scaffold counts |
| Equidistribution (global) | **CONDITIONAL** e.g. `equidistribution_of_asymptotic` |

## Appendix B — What not to put on IonQ slides

1. “2,023 verified theorems prove topological QC.”  
2. “BSH mixing uniformity is machine-proved (therefore secure).”  
3. “Our QRNG is quantum because the API key is set.”  
4. “Migration scanner output is Lean-verified.”  
5. Empty `riemann_labs_lean_snapshot` as evidence.

---

*End of inventory. Do not commit unless a human asks. Regenerate registry counts before external share.*
