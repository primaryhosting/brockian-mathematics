# Observatory

Public claim surface for the Brockian verified core and the Curved Number Line ledger.

## Principle

**Badges are derived, never hand-painted.**

1. Lean proofs are attested (AXLE) and entered in `registry/theorems.json`.
2. `claim_map.yaml` only maps **stable claim IDs** → fully-qualified Lean names.
3. `gen_claims.py` looks up each name in the registry and assigns the register
   (`PROVED` / `CONDITIONAL` / `CONJECTURE` / …).
4. `gen_observatory.py` renders the static page.

If a claim has no Lean link, the map may set `badge_force` to
`not_claimed`, `open`, `aristotle`, `empirical`, or `prose`.

## Regenerate

From the repo root:

```bash
python3 scripts/gen_registry.py
python3 scripts/gen_claims.py
python3 scripts/gen_observatory.py
```

Open `index.html` in a browser (no server required).

## Editing the map

Add or adjust entries in `claim_map.yaml`:

```yaml
- id: GC-1
  title: Local Goldbach count
  book: "Curved Number Line · Vol III · The Local Pulse"
  lean:
    - Brockian.GoldbachComb.gCount_eq
  notes: "Exact for every prime p."
```

Use fully-qualified names as they appear in `REGISTRY.md`. After edits, re-run
`gen_claims.py` and `gen_observatory.py`.

## Book badge legend

| Book badge | Meaning |
|------------|---------|
| **V3-LEAN-RUN** | At least one linked theorem is registry **PROVED** |
| **CONDITIONAL** | Linked implication under a named open hypothesis |
| **CONJECTURE** | Named Prop container, not a theorem |
| **NOT-CLAIMED** | Explicit open problem (twins / Goldbach global / RH) |
| **ARISTOTLE-PENDING** | Sorry-target submitted to Aristotle |
| **OPEN** | Formalization target without a verified decl yet |
