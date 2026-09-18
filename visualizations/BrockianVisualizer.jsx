import React, { useState, useMemo, useCallback } from 'react';

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

  const mathUtils = useMemo(() => ({
    isPrime: (n) => {
      if (n < 2) return false;
      for (let i = 2; i <= Math.sqrt(n); i++) {
        if (n % i === 0) return false;
      }
      return true;
    },
    isTriangular: (n) => {
      const k = Math.sqrt(2 * Math.abs(n) + 0.25) - 0.5;
      return k === Math.floor(k);
    },
    isPentagonal: (n) => {
      const k = (1 + Math.sqrt(24 * Math.abs(n) + 1)) / 6;
      return k === Math.floor(k);
    },
    isFibonacci: (() => {
      const fibSet = new Set([0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]);
      return (n) => fibSet.has(Math.abs(n));
    })(),
    getVertexProperties: (n) => {
      const absN = Math.abs(n);
      const mod5 = absN % 5;
      const vertex = ['A', 'B', 'C', 'D', 'E'][mod5];
      const angle = [90, 162, 234, 306, 18][mod5];
      return {
        vertex,
        angle: angle * (Math.PI / 180),
        mod5
      };
    }
  }), []);

  const theorems = useMemo(() => ({
    none: {
      name: "No Theorem (Count By Pattern)",
      description: "View basic counting patterns and vertex structure",
      highlight: (point) => ({
        color: point.isZero ? "#ecc94b" : point.isPositive ? "#48bb78" : "#f56565"
      })
    },
    vertexPatterns: {
      name: "Vertex Patterns",
      description: "Each vertex shows distinct geometric patterns",
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
      description: "Distribution of prime numbers across vertices",
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
      description: "Fibonacci numbers create unique geometric patterns",
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

  const project = useCallback((x, y, z) => {
    const rotRad = (rotation * Math.PI) / 180;
    const elevRad = (elevation * Math.PI) / 180;

    const x1 = x * Math.cos(rotRad) - z * Math.sin(rotRad);
    const z1 = x * Math.sin(rotRad) + z * Math.cos(rotRad);

    const y1 = y * Math.cos(elevRad) - z1 * Math.sin(elevRad);
    const z2 = y * Math.sin(elevRad) + z1 * Math.cos(elevRad);

    return {
      x: 400 + x1 * 20,
      y: 400 + y1 * 20,
      z: z2,
      depth: z2
    };
  }, [rotation, elevation]);

  const projectedPoints = useMemo(() => {
    const points = [];
    points.push(generatePoint(0));

    for (let i = countBy; i <= maxNumber; i += countBy) {
      points.push(generatePoint(i));
      if (showNegative) {
        points.push(generatePoint(-i));
      }
    }

    return points
      .map(point => ({
        ...point,
        ...project(point.x, point.y, point.z),
        ...theorems[selectedTheorem].highlight(point)
      }))
      .sort((a, b) => b.depth - a.depth);
  }, [maxNumber, countBy, showNegative, generatePoint, project, selectedTheorem, theorems]);

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
        </div>
      </div>

      <svg viewBox="0 0 800 800" className="w-full h-full">
        {showGrid && (
          <circle
            cx={400}
            cy={400}
            r={200}
            fill="none"
            stroke="#ddd"
            strokeWidth="1"
            strokeDasharray="4,4"
          />
        )}

        {showConnections && projectedPoints.map((point, index) => {
          if (index === 0) return null;
          const prevPoint = projectedPoints[index - 1];
          return (
            <line
              key={`conn-${index}`}
              x1={prevPoint.x}
              y1={prevPoint.y}
              x2={point.x}
              y2={point.y}
              stroke={point.color}
              strokeWidth="1"
              opacity="0.3"
            />
          );
        })}

        {projectedPoints.map((point, index) => (
          <g key={index}>
            <circle
              cx={point.x}
              cy={point.y}
              r={point.size || (point.isZero ? 6 : 4)}
              fill={point.color}
              opacity={0.8}
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

      <div className="absolute top-4 right-4 bg-white p-4 rounded shadow">
        <h3 className="font-bold mb-2">{theorems[selectedTheorem].name}</h3>
        <p className="text-sm">{theorems[selectedTheorem].description}</p>
      </div>
    </div>
  );
};

export default BrockianVisualizer;
