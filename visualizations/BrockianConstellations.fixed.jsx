import React, { useState, useMemo } from 'react';

// Corrected replacement for BrockianSpiralPrimordialPrimes.jsx (original
// archived verbatim). The original searched an INADMISSIBLE pattern — offsets
// {0,1,3,5,9,11,15,17,21} cover both residues mod 2, so the only hit below
// 10^6 is the seed tuple at 2 and the plot renders one dot. This version:
//   - uses genuinely admissible constellations, checked by the same ν(p) < p
//     criterion the corpus formalizes (AdmissibilityKTuple)
//   - defaults to patterns that are actually visible below the sieve limit
//     (the densest admissible 8-tuple's SECOND occurrence is ~15.76M — an
//     8-tuple demo below 10^6 would still be a single dot)
//   - makes the mod-5 ray layout intentional: constellation starts occupy
//     exactly q − ν(q) = 5 − ν(5) residue classes, the corpus's q=5→3 law
//     for twin pairs (and the 1-ray case for quadruplets)
//   - alternative golden-angle spiral layout; sieve memoized off the render path

const PATTERNS = {
  twin: { label: 'Twin pairs [0,2] — 3 of 5 rays (q−ν = 3)', offsets: [0, 2] },
  quad: { label: 'Quadruplets [0,2,6,8] — 1 of 5 rays (q−ν = 1)', offsets: [0, 2, 6, 8] },
  quint: { label: 'Quintuplets [0,2,6,8,12] — 1 ray', offsets: [0, 2, 6, 8, 12] }
};

const isAdmissible = (offsets) => {
  for (const p of [2, 3, 5, 7]) {
    const residues = new Set(offsets.map((o) => ((o % p) + p) % p));
    if (residues.size === p) return false; // ν(p) = p → inadmissible
  }
  return true;
};

const BrockianConstellations = () => {
  const [patternKey, setPatternKey] = useState('twin');
  const [layout, setLayout] = useState('rays'); // 'rays' | 'spiral'
  const width = 800;
  const height = 800;
  const centerX = width / 2;
  const centerY = height / 2;
  const LIMIT = 500000;

  const sieve = useMemo(() => {
    const s = new Uint8Array(LIMIT + 1).fill(1);
    s[0] = s[1] = 0;
    for (let i = 2; i * i <= LIMIT; i++) {
      if (s[i]) {
        for (let j = i * i; j <= LIMIT; j += i) s[j] = 0;
      }
    }
    return s;
  }, []);

  const { starts, admissible } = useMemo(() => {
    const offsets = PATTERNS[patternKey].offsets;
    if (!isAdmissible(offsets)) return { starts: [], admissible: false };
    const maxOff = offsets[offsets.length - 1];
    const found = [];
    for (let start = 2; start <= LIMIT - maxOff; start++) {
      if (offsets.every((o) => sieve[start + o])) found.push(start);
    }
    return { starts: found, admissible: true };
  }, [patternKey, sieve]);

  const rayColors = ['#ecc94b', '#48bb78', '#4299e1', '#9f7aea', '#f56565']; // by start mod 5

  const getPoint = (n) => {
    if (layout === 'spiral') {
      const r = 8 * Math.sqrt(n) * (380 / (8 * Math.sqrt(LIMIT))); // uniform density, fits viewBox
      const theta = n * Math.PI * (3 - Math.sqrt(5)); // golden angle
      return { x: centerX + r * Math.cos(theta), y: centerY + r * Math.sin(theta) };
    }
    // rays: angle = true residue class mod 5, radius = sqrt for density
    const mod5 = ((n % 5) + 5) % 5;
    const theta = (2 * Math.PI * mod5) / 5 - Math.PI / 2;
    const r = 380 * Math.sqrt(n / LIMIT);
    return { x: centerX + r * Math.cos(theta), y: centerY + r * Math.sin(theta) };
  };

  const populatedResidues = useMemo(
    () => new Set(starts.filter((s) => s > 5).map((s) => s % 5)),
    [starts]
  );

  return (
    <div className="w-full h-full relative bg-gray-50">
      <div className="absolute top-4 left-4 z-10 bg-white p-4 rounded shadow space-y-3 max-w-sm">
        <div>
          <label className="block text-sm font-medium mb-1">Constellation</label>
          <select
            value={patternKey}
            onChange={(e) => setPatternKey(e.target.value)}
            className="w-full p-2 border rounded"
          >
            {Object.entries(PATTERNS).map(([key, p]) => (
              <option key={key} value={key}>{p.label}</option>
            ))}
          </select>
        </div>
        <div>
          <label className="block text-sm font-medium mb-1">Layout</label>
          <select
            value={layout}
            onChange={(e) => setLayout(e.target.value)}
            className="w-full p-2 border rounded"
          >
            <option value="rays">Pentagon rays (residue mod 5)</option>
            <option value="spiral">Golden-angle spiral</option>
          </select>
        </div>
        <div className="text-sm space-y-1">
          <p>
            <strong>{starts.length}</strong> constellation starts ≤ {LIMIT.toLocaleString()}
            {admissible ? '' : ' — pattern inadmissible (ν(p) = p for some p)'}
          </p>
          <p>
            Populated residues mod 5 (starts &gt; 5):{' '}
            <strong>{[...populatedResidues].sort().join(', ') || '—'}</strong>{' '}
            ({populatedResidues.size} of 5 — the q − ν(5) law)
          </p>
        </div>
      </div>

      <svg viewBox="0 0 800 800" className="w-full h-full">
        {layout === 'rays' &&
          [0, 1, 2, 3, 4].map((m) => {
            const theta = (2 * Math.PI * m) / 5 - Math.PI / 2;
            return (
              <g key={m}>
                <line
                  x1={centerX}
                  y1={centerY}
                  x2={centerX + 380 * Math.cos(theta)}
                  y2={centerY + 380 * Math.sin(theta)}
                  stroke={populatedResidues.has(m) ? '#cbd5e0' : '#edf2f7'}
                  strokeWidth="1"
                  strokeDasharray="4,4"
                />
                <text
                  x={centerX + 395 * Math.cos(theta)}
                  y={centerY + 395 * Math.sin(theta)}
                  fontSize="13"
                  fill="#4a5568"
                  textAnchor="middle"
                >
                  {m}
                </text>
              </g>
            );
          })}

        {starts.map((start) => {
          const point = getPoint(start);
          return (
            <circle
              key={start}
              cx={point.x}
              cy={point.y}
              r="2"
              fill={rayColors[((start % 5) + 5) % 5]}
              opacity="0.75"
            />
          );
        })}
      </svg>
    </div>
  );
};

export default BrockianConstellations;
