import React, { useState, useEffect } from 'react';

const BrockianSpiralPrimordialPrimes = () => {
  const [primordialConstellations, setPrimordialConstellations] = useState([]);
  const width = 800;
  const height = 800;
  const centerX = width / 2;
  const centerY = height / 2;
  const k = 0.004; // Scaling factor

  useEffect(() => {
    const sieveOfEratosthenes = (limit) => {
      const sieve = new Array(limit + 1).fill(true);
      sieve[0] = sieve[1] = false;
      for (let i = 2; i * i <= limit; i++) {
        if (sieve[i]) {
          for (let j = i * i; j <= limit; j += i) {
            sieve[j] = false;
          }
        }
      }
      return sieve;
    };

    const findPrimordialConstellations = (limit) => {
      const sieve = sieveOfEratosthenes(limit);
      const primes = [2, 3, 5, 7, 11, 13, 17, 19, 23];
      const gaps = [2, 4, 2, 4, 2, 4, 2, 4];
      const constellations = [];

      for (let start = 2; start <= limit - gaps.reduce((a, b) => a + b, 0); start++) {
        if (sieve[start]) {
          let isConstellation = true;
          for (let i = 0; i < gaps.length; i++) {
            if (!sieve[start + primes[i+1] - primes[0]]) {
              isConstellation = false;
              break;
            }
          }
          if (isConstellation) {
            constellations.push(start);
          }
        }
      }
      return constellations;
    };

    setPrimordialConstellations(findPrimordialConstellations(1000000));
  }, []);

  const getPointOnSpiral = (n) => {
    const r = k * n;
    const theta = (2 * Math.PI * (n % 5)) / 5;
    return {
      x: centerX + r * Math.cos(theta),
      y: centerY + r * Math.sin(theta)
    };
  };

  const getColor = (n) => {
    const colors = ['#FF0000', '#00FF00', '#0000FF', '#FFFF00', '#FF00FF', '#00FFFF', '#FFA500', '#800080', '#008000'];
    return colors[parseInt(n.toString()[0]) - 1];
  };

  return (
    <svg width={width} height={height}>
      {primordialConstellations.map((prime, index) => {
        const point = getPointOnSpiral(prime);
        const color = getColor(prime);
        return (
          <g key={index}>
            <circle cx={point.x} cy={point.y} r="2" fill={color} />
          </g>
        );
      })}
    </svg>
  );
};

export default BrockianSpiralPrimordialPrimes;
