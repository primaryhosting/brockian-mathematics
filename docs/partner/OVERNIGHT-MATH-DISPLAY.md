# Overnight Math Display — running for morning return

**Mission:** prove as much honest, AXLE-verified math as possible before morning.  
**Scheduler:** durable task every **15 minutes** (id `019fc5a1d907`).  
**Generator:** `scripts/overnight_corpus_wave.py` · state: `scripts/overnight_state.json`

## Rules

- No RH / Goldbach / twin-prime / infinitude theater  
- No Claude red Weyl weak-reg / energy / Gate1Closed  
- Surgical commits · AXLE green required · public export after each wave  

## Scoreboard

| Wave | Commit | PROVED | Payload |
|------|--------|--------|---------|
| Epic strike | `76db1fb` | 1955 | Gaps72–100 · Cos31–41 · K2×23/31 |
| Overnight w1 | `456ce7a` | 2137 | Gaps102–130 · Cos43–53 · K2×37/41 |
| Overnight w2 | `6a8dc0f` | 2257 | Gaps132–160 · Cos59–67 · K2×43/47 |
| Overnight w3 | `ebdf30f` | 2406 | Gaps162–200 · Cos71–79 · K2×53/59 |
| Overnight w4 | `7d2b2a3` | 2590 | Gaps202–250 · Cos83–97 · K2×61/67/71 |
| K2×29 fill | `8050917` | 2596 | missing wheel between 23–31 |
| Overnight w5 | `5551d58` | 2794 | Gaps252–300 · Cos101–109 · K2×73/79/83 |
| **Overnight w6** | `aa26aea` | **2985** | Gaps302–350 · Cos113/127/131/137 · K2×89/97/101 |
| Wave 7+ | *15m scheduler* | … | Gaps352–400 · Cos139+ · K2×103+ |

## Display headlines for morning

1. **Grand Pentagon Equivalence** — 4-way TFAE (machine-checked)  
2. **Even-gap singular series continuum 22 → 350** (local S(H) only)  
3. **Spectral degree packs** for primes through **p = 137**  
4. **Local K₂×K_p wheels** through **p = 101** (plus K2×29 fill)  
5. Public registry honesty firewall · **PROVED 2985** and climbing  

## Morning checklist

```bash
cd ~/Projects/brockian-mathematics
git log --oneline -25
python3 -c "import json; print(json.load(open('registry/theorems.json'))['summary'])"
# Torus: paste deploy/torus-lovable/LOVABLE_PROMPT.md when CDP up
```
