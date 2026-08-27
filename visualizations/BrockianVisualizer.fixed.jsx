import React, { useState, useMemo, useCallback } from 'react';

// Corrected copy of BrockianVisualizer.jsx (original archived verbatim).
// Fixes applied per the 2026-08-27 review:
//   - true ZMod 5 residue ((n%5)+5)%5 — negation now displays as the D5
//     reflection on the vertex pentagon instead of being quotiented away
//   - connections built in numeric order; depth sort used only for paint order
//   - integer-exact triangular/pentagonal predicates; exact Fibonacci test
//   - adaptive projection scale (no overflow past the viewBox)
//   - maxNumber slider + showGrid checkbox wired; hover highlights the
//     hovered vertex's whole residue class

const BrockianVisualizer = () => {
  const [rotation, setRotation] = useState(0);
  const [elevation, setElevation] = useState(30);
  const [maxNumber, setMaxNumber] = useState(50);
  const [showNegative, setShowNegative] = useState(true);
  const [selectedTheorem, setSelectedTheorem] = useState('none');
  const [countBy, setCountBy] = useState(1);
  const [showLabels, setShowLabels] = useState(true);
  const [showGrid, setShowGrid] = useState(true);
  const [showConnections, setShowConnections] = useState(true);
  const [highlightedVertex, setHighlightedVertex] = useState(null);

  const mathUtils = useMemo(() => {
    const isPerfectSquare = (m) => {
      if (m < 0) return false;
      const s = Math.round(Math.sqrt(m));
      return s * s === m;
    };
    return {
      isPrime: (n) => {
        if (n < 2) return false;
        for (let i = 2; i * i <= n; i++) {
          if (n % i === 0) return false;
        }
        return true;
      },
      isTriangular: (n) => {
        const m = Math.abs(n);
        const kk = Math.round((Math.sqrt(8 * m + 1) - 1) / 2);
        return (kk * (kk + 1)) / 2 === m;
      },
      isPentagonal: (n) => {
        const m = Math.abs(n);
        if (m === 0) return true;
        const kk = Math.round((1 + Math.sqrt(24 * m + 1)) / 6);
        return (kk * (3 * kk - 1)) / 2 === m;
      },
      // n is Fibonacci iff 5n²+4 or 5n²−4 is a perfect square
      isFibonacci: (n) => {
        const m = Math.abs(n);
        return isPerfectSquare(5 * m * m + 4) || isPerfectSquare(5 * m * m - 4);
      },
      getVertexProperties: (n) => {
        const mod5 = ((n % 5) + 5) % 5; // true ZMod 5 residue, negative-safe
        const vertex = ['A', 'B', 'C', 'D', 'E'][mod5];
        const angle = [90, 162, 234, 306, 18][mod5];
        return { vertex, angle: angle * (Math.PI / 180), mod5 };
      }
    };
  }, []);

  const theorems = useMemo(() => ({
    none: {
      name: "No Theorem (Count By Pattern)",
      description: "View basic counting patterns and vertex structure",
      highlight: (point) => ({
        color: point.isZero ? "#ecc94b" : point.isPositive ? "#48bb78" : "#f56565"
      })
    },
    vertexPatterns: {
      name: "Vertex Patterns (ZMod 5)",
      description: "True residue classes: negation acts as the D5 reflection — −n sits on the mirror vertex of n",
      highlight: (point) => ({
        color:
          point.vertex === 'A' ? "#48bb78" :
          point.vertex === 'B' ? "#4299e1" :
          point.vertex === 'C' ? "#9f7aea" :
          point.vertex === 'D' ? "#f56565" :
          "#ed8936"
      })
    },
    primes: {
      name: "Prime Distribution",
      description: "Primes are positive by definition, so the negative helix stays gray. Vertex A (residue 0) contains only the prime 5; primes > 5 occupy residues {1,2,3,4}.",
      highlight: (point) => ({
        color: mathUtils.isPrime(point.number) ? "#48bb78" : "#a0aec0",
        size: mathUtils.isPrime(point.number) ? 5 : 3
      })
    },
    triangular: {
      name: "Triangular Numbers",
      description: "Triangular numbers form specific patterns",
      highlight: (point) => ({
        color: mathUtils.isTriangular(point.number) ? "#805ad5" : "#a0aec0",
        size: mathUtils.isTriangular(point.number) ? 5 : 3
      })
    },
    pentagonal: {
      name: "Pentagonal Numbers",
      description: "Pentagonal numbers show systematic alignment",
      highlight: (point) => ({
        color: mathUtils.isPentagonal(point.number) ? "#d53f8c" : "#a0aec0",
        size: mathUtils.isPentagonal(point.number) ? 5 : 3
      })
    },
    fibonacci: {
      name: "Fibonacci Pattern",
      description: "Exact test: n is Fibonacci iff 5n²±4 is a perfect square",
      highlight: (point) => ({
        color: mathUtils.isFibonacci(point.number) ? "#ed8936" : "#a0aec0",
        size: mathUtils.isFibonacci(point.number) ? 5 : 3
      })
    }
  }), [mathUtils]);

  const generatePoint = useCallback((n) => {
    const props = mathUtils.getVertexProperties(n);
    const r = Math.abs(n);
    return {
      x: r * Math.cos(props.angle),
      y: r * Math.sin(props.angle),
      z: n,
      number: n,
      vertex: props.vertex,
      isPositive: n > 0,
      isNegative: n < 0,
      isZero: n === 0,
      modulo5: props.mod5
    };
  }, [mathUtils]);

  const scale = 350 / maxNumber; // adaptive: max radius stays inside the viewBox

  const project = useCallback((x, y, z) => {
    const rotRad = (rotation * Math.PI) / 180;
    const elevRad = (elevation * Math.PI) / 180;

    const x1 = x * Math.cos(rotRad) - z * Math.sin(rotRad);
    const z1 = x * Math.sin(rotRad) + z * Math.cos(rotRad);

    const y1 = y * Math.cos(elevRad) - z1 * Math.sin(elevRad);
    const z2 = y * Math.sin(elevRad) + z1 * Math.cos(elevRad);

    return {
      x: 400 + x1 * scale,
      y: 400 + y1 * scale,
      depth: z2
    };
  }, [rotation, elevation, scale]);

  const { drawOrder, connections } = useMemo(() => {
    const numbers = [0];
    for (let i = countBy; i <= maxNumber; i += countBy) {
      numbers.push(i);
      if (showNegative) numbers.push(-i);
    }
    numbers.sort((a, b) => a - b); // numeric order is the polyline order

    const ordered = numbers.map((n) => {
      const point = generatePoint(n);
      return {
        ...point,
        ...project(point.x, point.y, point.z),
        ...theorems[selectedTheorem].highlight(point)
      };
    });

    const conns = ordered.slice(1).map((p, i) => [ordered[i], p]);
    const sorted = [...ordered].sort((a, b) => b.depth - a.depth); // paint order only
    return { drawOrder: sorted, connections: conns };
  }, [maxNumber, countBy, showNegative, generatePoint, project, selectedTheorem, theorems]);

  const dimmed = (point) =>
    highlightedVertex !== null && point.vertex !== highlightedVertex;

  return (
    <div className="w-full h-full relative bg-gray-50">
      <div className="absolute top-4 left-4 z-10 bg-white p-4 rounded shadow space-y-4">
        <div>
          <label className="block text-sm font-medium mb-1">View Controls</label>
          <div className="space-y-2">
            <div>
              <label className="block text-sm">Rotation: {rotation}°</label>
              <input
                type="range"
                min="0"
                max="360"
                value={rotation}
                onChange={(e) => setRotation(Number(e.target.value))}
                className="w-full"
              />
            </div>

            <div>
              <label className="block text-sm">Elevation: {elevation}°</label>
              <input
                type="range"
                min="0"
                max="90"
                value={elevation}
                onChange={(e) => setElevation(Number(e.target.value))}
                className="w-full"
              />
            </div>
          </div>
        </div>

        <div>
          <label className="block text-sm font-medium mb-1">Max Number: {maxNumber}</label>
          <input
            type="range"
            min="10"
            max="200"
            value={maxNumber}
            onChange={(e) => setMaxNumber(Number(e.target.value))}
            className="w-full"
          />
        </div>

        <div>
          <label className="block text-sm font-medium mb-1">Count By: {countBy}</label>
          <input
            type="range"
            min="1"
            max="10"
            value={countBy}
            onChange={(e) => setCountBy(Number(e.target.value))}
            className="w-full"
          />
        </div>

        <div>
          <label className="block text-sm font-medium mb-1">Theorem</label>
          <select
            value={selectedTheorem}
            onChange={(e) => setSelectedTheorem(e.target.value)}
            className="w-full p-2 border rounded"
          >
            {Object.entries(theorems).map(([key, theorem]) => (
              <option key={key} value={key}>{theorem.name}</option>
            ))}
          </select>
        </div>

        <div className="space-y-2">
          <label className="flex items-center space-x-2">
            <input
              type="checkbox"
              checked={showNegative}
              onChange={(e) => setShowNegative(e.target.checked)}
            />
            <span>Show Negative Numbers</span>
          </label>

          <label className="flex items-center space-x-2">
            <input
              type="checkbox"
              checked={showConnections}
              onChange={(e) => setShowConnections(e.target.checked)}
            />
            <span>Show Connections</span>
          </label>

          <label className="flex items-center space-x-2">
            <input
              type="checkbox"
              checked={showLabels}
              onChange={(e) => setShowLabels(e.target.checked)}
            />
            <span>Show Labels</span>
          </label>

          <label className="flex items-center space-x-2">
            <input
              type="checkbox"
              checked={showGrid}
              onChange={(e) => setShowGrid(e.target.checked)}
            />
            <span>Show Grid</span>
          </label>
        </div>
      </div>

      <svg viewBox="0 0 800 800" className="w-full h-full">
        {showGrid && (
          <circle
            cx={400}
            cy={400}
            r={350}
            fill="none"
            stroke="#ddd"
            strokeWidth="1"
            strokeDasharray="4,4"
          />
        )}

        {showConnections && connections.map(([a, b], index) => (
          <line
            key={`conn-${index}`}
            x1={a.x}
            y1={a.y}
            x2={b.x}
            y2={b.y}
            stroke={b.color}
            strokeWidth="1"
            opacity={dimmed(b) ? 0.08 : 0.3}
          />
        ))}

        {drawOrder.map((point) => (
          <g key={point.number}>
            <circle
              cx={point.x}
              cy={point.y}
              r={point.size || (point.isZero ? 6 : 4)}
              fill={point.color}
              opacity={dimmed(point) ? 0.15 : 0.8}
              onMouseEnter={() => setHighlightedVertex(point.vertex)}
              onMouseLeave={() => setHighlightedVertex(null)}
            />
            {showLabels && (Math.abs(point.number) <= 5 || point.isZero) && (
              <text
                x={point.x + 10}
                y={point.y + 5}
                fontSize="12"
                fill="#4a5568"
              >
                {point.number}
              </text>
            )}
          </g>
        ))}
      </svg>

      <div className="absolute top-4 right-4 bg-white p-4 rounded shadow max-w-xs">
        <h3 className="font-bold mb-2">{theorems[selectedTheorem].name}</h3>
        <p className="text-sm">{theorems[selectedTheorem].description}</p>
        {highlightedVertex && (
          <p className="text-sm mt-2 font-medium">
            Vertex {highlightedVertex} — residue class{' '}
            {['A', 'B', 'C', 'D', 'E'].indexOf(highlightedVertex)} (mod 5)
          </p>
        )}
      </div>
    </div>
  );
};

export default BrockianVisualizer;
