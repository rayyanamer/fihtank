(function () {
  "use strict";

  const canvas = document.getElementById("world");
  const ctx = canvas.getContext("2d", { alpha: false });

  let cellSize = 3;
  let cols = 220;
  let rows = 124;

  const BG_UINT32 = 0xff0d0905;
  let gridPixels = new Uint32Array(0);
  let gridGlow = new Uint8Array(0);
  let gridDepth = new Float32Array(0);
  let imgData = null;
  let imgBuf32 = null;

  const colorCache = new Map();

  function hexToUint32(hex) {
    let val = colorCache.get(hex);
    if (val !== undefined) return val;
    const n = parseInt(hex.slice(1), 16);
    const r = (n >> 16) & 255;
    const g = (n >> 8) & 255;
    const b = n & 255;
    val = (255 << 24) | (b << 16) | (g << 8) | r;
    colorCache.set(hex, val);
    return val;
  }

  const BAYER_4X4 = [
    [0 / 16, 8 / 16, 2 / 16, 10 / 16],
    [12 / 16, 4 / 16, 14 / 16, 6 / 16],
    [3 / 16, 11 / 16, 1 / 16, 9 / 16],
    [15 / 16, 7 / 16, 13 / 16, 5 / 16]
  ];

  const jar = {
    left: 20,
    right: 200,
    top: 10,
    bottom: 114,
    sandTop: 96,
    waterLine: 24,
    centerX: 110,
    halfW: 90
  };

  let grassStalks = [];
  let stemPlants = [];
  let rocks = [];
  let bubbles = [];
  let motes = [];
  let sandPebbles = [];
  let surfaceRipples = [];
  let foodPellets = [];
  let heartParticles = [];

  let backRockIndices = [];
  let midRockIndices = [];
  let frontRockIndices = [];
  let backGrassIndices = [];
  let midGrassIndices = [];
  let frontGrassIndices = [];
  let backStemIndices = [];
  let midStemIndices = [];
  let frontStemIndices = [];

  const pointer = {
    x: -999,
    y: -999,
    prevX: -999,
    prevY: -999,
    active: false,
    inWater: false
  };

  const FISH_STATE = {
    CRUISING: 0,
    ORBITING: 1,
    RESTING: 2,
    ALERT: 3,
    FORAGING: 4
  };

  const fish = {
    x: 110,
    y: 60,
    vx: 0.28,
    vy: 0.0,
    angle: 0,
    targetAngle: 0,
    speed: 0.30,
    baseSpeed: 0.30,
    tailPhase: 0,
    finPhase: 0,
    gillPhase: 0,
    state: FISH_STATE.CRUISING,
    stateTimer: 2.0,
    energy: 0.85,
    orbitTarget: null,
    orbitAngle: 0,
    orbitRadius: 13,
    restPos: { x: 110, y: 80 },
    targetFood: null,
    eatFlutterTimer: 0,
    depth: 0.5,
    targetDepth: 0.5,
    turnCooldown: 0,
    alertTimer: 0
  };

  let lastTime = 0;
  let elapsed = 0;
  let stepScale = 1;

  function clamp(val, min, max) {
    return val < min ? min : val > max ? max : val;
  }

  function lerp(a, b, t) {
    return a + (b - a) * t;
  }

  function angleDiff(target, current) {
    let diff = (target - current) % (Math.PI * 2);
    if (diff > Math.PI) diff -= Math.PI * 2;
    if (diff < -Math.PI) diff += Math.PI * 2;
    return diff;
  }

  function randRange(min, max) {
    return min + Math.random() * (max - min);
  }

  function ditherPass(v, x, y) {
    const bx = (x | 0) & 3;
    const by = (y | 0) & 3;
    const clamped = v < 0 ? 0 : v > 1 ? 1 : v;
    return clamped > BAYER_4X4[by][bx];
  }

  function ditherMixUint(colA, colB, t, x, y) {
    return ditherPass(t, x, y) ? colB : colA;
  }

  function resizeWorld() {
    const width = window.innerWidth || document.documentElement.clientWidth || 800;
    const height = window.innerHeight || document.documentElement.clientHeight || 600;

    cellSize = clamp(Math.round(Math.min(width, height) / 215), 2, 4);

    cols = Math.max(80, Math.floor(width / cellSize));
    rows = Math.max(60, Math.floor(height / cellSize));

    canvas.width = cols;
    canvas.height = rows;

    const padX = Math.max(6, Math.floor(cols * 0.08));
    const padY = Math.max(5, Math.floor(rows * 0.07));
    jar.left = padX;
    jar.right = Math.max(jar.left + 40, cols - 1 - padX);
    jar.top = padY;
    jar.bottom = Math.max(jar.top + 32, rows - 1 - padY);
    jar.waterLine = clamp(
      jar.top + Math.floor((jar.bottom - jar.top) * 0.16),
      jar.top + 5,
      jar.bottom - 18
    );
    jar.sandTop = clamp(
      jar.bottom - Math.max(8, Math.floor((jar.bottom - jar.top) * 0.16)),
      jar.waterLine + 14,
      jar.bottom - 5
    );
    jar.centerX = (jar.left + jar.right) * 0.5;
    jar.halfW = Math.max(1, (jar.right - jar.left) * 0.5);

    allocateGrid();
    populateEcosystem();
  }

  function allocateGrid() {
    const total = cols * rows;
    gridPixels = new Uint32Array(total);
    gridGlow = new Uint8Array(total);
    gridDepth = new Float32Array(total);
    imgData = ctx.createImageData(cols, rows);
    imgBuf32 = new Uint32Array(imgData.data.buffer);
  }

  function clearGrid() {
    gridPixels.fill(BG_UINT32);
    gridGlow.fill(0);
    gridDepth.fill(-1);
  }

  function setPixel(x, y, colUint, glow, depth) {
    const gx = Math.round(x);
    const gy = Math.round(y);
    if (gx < 0 || gx >= cols || gy < 0 || gy >= rows) return;
    const idx = gy * cols + gx;
    if (depth >= gridDepth[idx]) {
      gridPixels[idx] = colUint;
      gridGlow[idx] = glow ? 1 : 0;
      gridDepth[idx] = depth;
    }
  }

  function isEmptyCell(x, y) {
    const gx = Math.round(x);
    const gy = Math.round(y);
    if (gx < 0 || gx >= cols || gy < 0 || gy >= rows) return false;
    return gridPixels[gy * cols + gx] === BG_UINT32;
  }

  function depthScale(depth) {
    const d = depth < 0 ? 0 : depth > 1 ? 1 : depth;
    return 0.68 + 0.64 * d;
  }

  function cylindricalShift(x, depth) {
    const normX = (x - jar.centerX) / jar.halfW;
    return normX * normX * normX * (depth - 0.5) * 3.8;
  }

  function populateEcosystem() {
    const innerLeft = jar.left + 8;
    const innerRight = jar.right - 8;
    const innerWidth = Math.max(36, innerRight - innerLeft);
    const floorY = jar.sandTop;

    rocks = [];
    const rockCount = innerWidth > 130 ? 5 : 4;
    const rockDefs = [
      { rxFrac: 0.17, width: 20, height: 10, depth: 0.22, light: "#75899e", dark: "#2b3540" },
      { rxFrac: 0.45, width: 28, height: 13, depth: 0.54, light: "#8fa4b8", dark: "#343e4a" },
      { rxFrac: 0.78, width: 22, height: 11, depth: 0.28, light: "#798da3", dark: "#2d3742" },
      { rxFrac: 0.31, width: 18, height: 9, depth: 0.84, light: "#a8bdd1", dark: "#3f4b59" },
      { rxFrac: 0.67, width: 21, height: 10, depth: 0.90, light: "#b2c7db", dark: "#43505e" }
    ];

    for (let i = 0; i < rockCount; i++) {
      const def = rockDefs[i % rockDefs.length];
      const scale = depthScale(def.depth);
      const w = clamp(Math.round(def.width * scale), 10, Math.floor(innerWidth * 0.24));
      const h = clamp(Math.round(def.height * scale), 6, Math.floor((floorY - jar.waterLine) * 0.22));
      const cx = Math.round(innerLeft + def.rxFrac * innerWidth + randRange(-3, 3));
      const x0 = clamp(Math.round(cx - w * 0.5), jar.left + 4, jar.right - w - 3);
      const yBaseShift = Math.round((def.depth - 0.5) * 2.5);
      const y0 = clamp(floorY - h + 1 + yBaseShift, jar.waterLine + 6, jar.bottom - h);

      rocks.push({
        x: x0,
        y: y0,
        w,
        h,
        depth: def.depth,
        light: hexToUint32(def.light),
        dark: hexToUint32(def.dark),
        highlight: hexToUint32("#d8ecff"),
        glintTimer: 0
      });
    }

    grassStalks = [];
    const stalkCount = clamp(Math.floor(innerWidth / 4.2), 28, 72);
    const maxGrassHeight = Math.max(16, floorY - jar.waterLine - 6);
    const grassPalettes = [
      { dark: hexToUint32("#0e3d29"), mid: hexToUint32("#1c734b"), tip: hexToUint32("#4ad18c") },
      { dark: hexToUint32("#124b33"), mid: hexToUint32("#248f5d"), tip: hexToUint32("#63e6a1") },
      { dark: hexToUint32("#0b3322"), mid: hexToUint32("#176340"), tip: hexToUint32("#3ec27e") }
    ];

    for (let i = 0; i < stalkCount; i++) {
      const t = stalkCount === 1 ? 0.5 : i / (stalkCount - 1);
      const clusterOffset = Math.sin(t * Math.PI * 6 + i * 0.7) * 4.5;
      const baseX = clamp(
        Math.round(innerLeft + t * innerWidth + clusterOffset),
        jar.left + 4,
        jar.right - 4
      );

      const band = i % 5;
      let depth;
      if (band === 0) depth = randRange(0.12, 0.26);
      else if (band === 1) depth = randRange(0.28, 0.44);
      else if (band === 2) depth = randRange(0.46, 0.58);
      else if (band === 3) depth = randRange(0.62, 0.78);
      else depth = randRange(0.80, 0.96);

      const pScale = depthScale(depth);
      const height = clamp(
        Math.round(randRange(maxGrassHeight * 0.34, maxGrassHeight * 0.92) * lerp(0.82, 1.12, depth)),
        11,
        maxGrassHeight
      );

      grassStalks.push({
        baseX,
        baseY: clamp(floorY + Math.round((depth - 0.5) * 2.6), jar.sandTop - 1, jar.bottom - 3),
        height,
        thickness: clamp(randRange(1.2, 2.2) * pScale, 1.0, 3.2),
        depth,
        phase: randRange(0, Math.PI * 2),
        swaySpeed: randRange(1.05, 1.95),
        swayAmp: randRange(2.0, 4.8) * lerp(0.75, 1.2, depth),
        nudgeVel: 0,
        nudgeOffset: 0,
        palette: grassPalettes[i % grassPalettes.length]
      });
    }

    stemPlants = [];
    const stemCount = clamp(Math.floor(innerWidth / 28), 4, 9);
    const stemPalettes = [
      { stem: hexToUint32("#18593c"), leafDark: hexToUint32("#1d7a50"), leafLight: hexToUint32("#54d996") },
      { stem: hexToUint32("#1b5246"), leafDark: hexToUint32("#237866"), leafLight: hexToUint32("#5ce0c5") }
    ];

    for (let i = 0; i < stemCount; i++) {
      const frac = (i + 0.5) / stemCount;
      const baseX = clamp(
        Math.round(innerLeft + frac * innerWidth + randRange(-5, 5)),
        jar.left + 6,
        jar.right - 6
      );
      const depth = i % 2 === 0 ? randRange(0.24, 0.46) : randRange(0.60, 0.86);
      const height = clamp(
        Math.round(randRange(maxGrassHeight * 0.45, maxGrassHeight * 0.85)),
        14,
        maxGrassHeight - 2
      );

      stemPlants.push({
        baseX,
        baseY: clamp(floorY + Math.round((depth - 0.5) * 2.4), jar.sandTop - 1, jar.bottom - 3),
        height,
        depth,
        phase: randRange(0, Math.PI * 2),
        swaySpeed: randRange(0.95, 1.65),
        swayAmp: randRange(2.2, 4.4),
        nudgeVel: 0,
        nudgeOffset: 0,
        leafStep: Math.max(4, Math.round(5 * depthScale(depth))),
        leafLen: Math.max(3, Math.round(4.2 * depthScale(depth))),
        palette: stemPalettes[i % stemPalettes.length]
      });
    }

    sandPebbles = [];
    const pebbleColors = [hexToUint32("#c4aa79"), hexToUint32("#786340"), hexToUint32("#9c8357")];
    const pebbleCount = Math.floor(innerWidth / 4.8);
    for (let i = 0; i < pebbleCount; i++) {
      const pDepth = randRange(0.15, 0.95);
      const pScale = depthScale(pDepth);
      sandPebbles.push({
        x: randRange(jar.left + 5, jar.right - 5),
        y: randRange(floorY + 1, jar.bottom - 1.5),
        rx: randRange(1.3, 2.6) * pScale,
        ry: randRange(0.8, 1.6) * pScale,
        depth: pDepth,
        color: pDepth > 0.6 ? pebbleColors[0] : pDepth > 0.35 ? pebbleColors[2] : pebbleColors[1]
      });
    }
    sandPebbles.sort((a, b) => a.depth - b.depth);

    motes = [];
    const moteCount = clamp(Math.floor(innerWidth / 5.5), 20, 52);
    for (let i = 0; i < moteCount; i++) {
      const mDepth = randRange(0.12, 0.95);
      motes.push({
        x: randRange(jar.left + 5, jar.right - 5),
        y: randRange(jar.waterLine + 3, floorY - 3),
        vx: randRange(-0.07, 0.07) * depthScale(mDepth),
        vy: randRange(-0.05, 0.03),
        depth: mDepth,
        phase: randRange(0, Math.PI * 2)
      });
    }

    bubbles = [];
    surfaceRipples = [];
    foodPellets = [];
    heartParticles = [];

    for (let i = 0; i < 14; i++) {
      const bDepth = randRange(0.15, 0.95);
      spawnBubble(
        randRange(jar.left + 10, jar.right - 10),
        randRange(jar.waterLine + 5, floorY - 3),
        randRange(1.0, 2.3) * depthScale(bDepth),
        bDepth
      );
    }

    rebuildLayerCaches();

    fish.x = clamp(fish.x, jar.left + 16, jar.right - 16);
    fish.y = clamp(fish.y, jar.waterLine + 8, floorY - 8);
    transitionFishState(FISH_STATE.CRUISING);
  }

  function rebuildLayerCaches() {
    backRockIndices = [];
    midRockIndices = [];
    frontRockIndices = [];
    for (let i = 0; i < rocks.length; i++) {
      const d = rocks[i].depth;
      if (d < 0.48) backRockIndices.push(i);
      else if (d < 0.74) midRockIndices.push(i);
      else frontRockIndices.push(i);
    }

    backGrassIndices = [];
    midGrassIndices = [];
    frontGrassIndices = [];
    for (let i = 0; i < grassStalks.length; i++) {
      const d = grassStalks[i].depth;
      if (d < 0.45) backGrassIndices.push(i);
      else if (d < 0.72) midGrassIndices.push(i);
      else frontGrassIndices.push(i);
    }

    backStemIndices = [];
    midStemIndices = [];
    frontStemIndices = [];
    for (let i = 0; i < stemPlants.length; i++) {
      const d = stemPlants[i].depth;
      if (d < 0.45) backStemIndices.push(i);
      else if (d < 0.72) midStemIndices.push(i);
      else frontStemIndices.push(i);
    }
  }

  function spawnBubble(x, y, radius, depth) {
    if (bubbles.length >= 80) bubbles.shift();
    bubbles.push({
      x,
      y,
      radius,
      depth: clamp(depth, 0.1, 0.98),
      vy: randRange(0.15, 0.34) * (0.75 + radius * 0.22),
      wobblePhase: randRange(0, Math.PI * 2),
      wobbleSpeed: randRange(2.4, 4.4)
    });
  }

  function spawnSurfaceRipple(x, strength) {
    if (surfaceRipples.length >= 10) surfaceRipples.shift();
    surfaceRipples.push({
      x: clamp(x, jar.left + 2, jar.right - 2),
      radius: 1.0,
      maxRadius: clamp(14 + strength * 16, 12, 34),
      alpha: clamp(0.45 + strength * 0.45, 0.35, 0.95)
    });
  }

  function spawnFood(x, y) {
    if (foodPellets.length >= 18) foodPellets.shift();
    const fDepth = randRange(0.28, 0.78);
    foodPellets.push({
      x: clamp(x, jar.left + 6, jar.right - 6),
      y: clamp(y, jar.top + 2, jar.waterLine - 1),
      vx: randRange(-0.08, 0.08),
      vy: randRange(0.22, 0.35),
      inWater: false,
      depth: fDepth,
      phase: randRange(0, Math.PI * 2),
      settledTimer: 0
    });
  }

  function spawnHeartParticles(x, y, depth) {
    const count = 4;
    for (let i = 0; i < count; i++) {
      if (heartParticles.length >= 24) heartParticles.shift();
      heartParticles.push({
        x: x + randRange(-3.5, 3.5),
        y: y - randRange(2.0, 5.0),
        vx: randRange(-0.09, 0.09),
        vy: -randRange(0.14, 0.24),
        phase: randRange(0, Math.PI * 2),
        life: randRange(1.4, 2.1),
        maxLife: 2.1,
        depth: clamp(depth + 0.05, 0.2, 0.96)
      });
    }
  }

  function findNearestFood() {
    let best = null;
    let bestDist = Infinity;
    for (let i = 0; i < foodPellets.length; i++) {
      const f = foodPellets[i];
      if (!f.inWater) continue;
      const dist = Math.hypot(f.x - fish.x, f.y - fish.y);
      if (dist < bestDist) {
        bestDist = dist;
        best = f;
      }
    }
    return best;
  }

  function transitionFishState(newState) {
    const innerLeft = jar.left + 15;
    const innerRight = jar.right - 15;
    const topBound = jar.waterLine + 6;
    const bottomBound = jar.sandTop - 6;

    fish.state = newState;

    if (newState === FISH_STATE.FORAGING) {
      fish.orbitTarget = null;
      fish.stateTimer = 8.0;
    } else if (newState === FISH_STATE.ORBITING) {
      const candidates = grassStalks.filter((s) => s.height >= 14);
      const stalk =
        candidates.length > 0
          ? candidates[Math.floor(Math.random() * candidates.length)]
          : grassStalks[Math.floor(Math.random() * grassStalks.length)];

      if (stalk) {
        const centerY = clamp(
          stalk.baseY - stalk.height * randRange(0.35, 0.72),
          topBound + 2,
          bottomBound - 2
        );
        fish.orbitTarget = { x: stalk.baseX, y: centerY, stalkRef: stalk };
        fish.orbitRadius = randRange(10.0, 17.0);
        fish.orbitAngle = Math.atan2(fish.y - centerY, fish.x - stalk.baseX);
        fish.stateTimer = randRange(3.2, 6.0);
        fish.targetDepth = clamp(stalk.depth + randRange(-0.24, 0.24), 0.16, 0.90);
      } else {
        transitionFishState(FISH_STATE.CRUISING);
      }
    } else if (newState === FISH_STATE.RESTING) {
      fish.orbitTarget = null;
      fish.stateTimer = randRange(2.8, 5.2);
      const restX = clamp(
        fish.x + randRange(-18, 18),
        innerLeft + 4,
        innerRight - 4
      );
      const restY = clamp(
        jar.sandTop - randRange(7, 15),
        topBound + 6,
        bottomBound - 2
      );
      fish.restPos.x = restX;
      fish.restPos.y = restY;
      fish.targetDepth = randRange(0.35, 0.75);
    } else if (newState === FISH_STATE.ALERT) {
      fish.orbitTarget = null;
      fish.stateTimer = randRange(1.1, 1.8);
    } else {
      fish.orbitTarget = null;
      fish.stateTimer = randRange(2.2, 4.5);
      const goalX = randRange(innerLeft, innerRight);
      const goalY = randRange(topBound, bottomBound);
      fish.targetAngle = Math.atan2(goalY - fish.y, goalX - fish.x);
      const r = Math.random();
      if (r < 0.42) fish.targetDepth = randRange(0.16, 0.42);
      else if (r < 0.76) fish.targetDepth = randRange(0.42, 0.66);
      else fish.targetDepth = randRange(0.66, 0.92);
    }
  }

  function chooseNextFishState() {
    const food = findNearestFood();
    if (food) {
      fish.targetFood = food;
      transitionFishState(FISH_STATE.FORAGING);
      return;
    }

    if (fish.energy < 0.34) {
      transitionFishState(FISH_STATE.RESTING);
      return;
    }

    const roll = Math.random();
    if (roll < 0.48) {
      transitionFishState(FISH_STATE.CRUISING);
    } else if (roll < 0.82 && grassStalks.length > 0) {
      transitionFishState(FISH_STATE.ORBITING);
    } else {
      transitionFishState(FISH_STATE.RESTING);
    }
  }

  function updateFish(dt) {
    const innerLeft = jar.left + 14;
    const innerRight = jar.right - 14;
    const topBound = jar.waterLine + 5.5;
    const bottomBound = jar.sandTop - 5.5;

    if (fish.turnCooldown > 0) fish.turnCooldown -= dt;
    if (fish.eatFlutterTimer > 0) fish.eatFlutterTimer -= dt;
    fish.stateTimer -= dt;

    if (fish.state !== FISH_STATE.FORAGING && fish.state !== FISH_STATE.ALERT) {
      const food = findNearestFood();
      if (food) {
        fish.targetFood = food;
        transitionFishState(FISH_STATE.FORAGING);
      }
    }

    if (fish.state === FISH_STATE.RESTING) {
      fish.energy = clamp(fish.energy + dt * 0.14, 0, 1);
    } else if (fish.state === FISH_STATE.ALERT) {
      fish.energy = clamp(fish.energy - dt * 0.12, 0, 1);
    } else if (fish.state === FISH_STATE.FORAGING) {
      fish.energy = clamp(fish.energy - dt * 0.04, 0, 1);
    } else {
      fish.energy = clamp(fish.energy - dt * 0.032, 0, 1);
    }

    let desiredSpeed = fish.baseSpeed;
    let tailRate = 9.0;
    let finRate = 6.2;

    if (fish.state === FISH_STATE.FORAGING) {
      desiredSpeed = fish.baseSpeed * 1.48;
      tailRate = 15.5;
      finRate = 9.5;
    } else if (fish.state === FISH_STATE.ALERT) {
      desiredSpeed = fish.baseSpeed * 1.85;
      tailRate = 21.0;
      finRate = 12.0;
    } else if (fish.state === FISH_STATE.RESTING) {
      desiredSpeed = fish.baseSpeed * 0.24;
      tailRate = 4.2;
      finRate = 3.8;
    } else if (fish.state === FISH_STATE.ORBITING) {
      desiredSpeed = fish.baseSpeed * 0.88;
      tailRate = 8.2;
      finRate = 5.8;
    }

    if (fish.eatFlutterTimer > 0) {
      tailRate = 22.0;
      finRate = 14.0;
    }

    fish.speed = lerp(fish.speed, desiredSpeed, dt * 4.2);
    fish.tailPhase += dt * (tailRate + fish.speed * 18);
    fish.finPhase += dt * finRate;
    fish.gillPhase += dt * (fish.state === FISH_STATE.ALERT ? 11.0 : 5.5);
    fish.depth = lerp(fish.depth, fish.targetDepth, dt * 1.9);

    if (fish.state === FISH_STATE.FORAGING) {
      if (!fish.targetFood || foodPellets.indexOf(fish.targetFood) === -1) {
        fish.targetFood = findNearestFood();
      }

      if (fish.targetFood && fish.targetFood.inWater) {
        const f = fish.targetFood;
        fish.targetDepth = lerp(fish.targetDepth, f.depth, dt * 3.5);
        const dx = f.x - fish.x;
        const dy = f.y - fish.y;
        const dist = Math.hypot(dx, dy);

        if (dist > 0.3) {
          fish.targetAngle = Math.atan2(dy, dx);
        }

        if (dist < 4.8 && Math.abs(fish.depth - f.depth) < 0.28) {
          const idx = foodPellets.indexOf(f);
          if (idx !== -1) foodPellets.splice(idx, 1);
          fish.targetFood = null;
          fish.energy = clamp(fish.energy + 0.24, 0, 1);
          fish.eatFlutterTimer = 0.75;
          spawnHeartParticles(
            fish.x + cylindricalShift(fish.x, fish.depth),
            fish.y - 4.0 * depthScale(fish.depth),
            fish.depth
          );

          const nextFood = findNearestFood();
          if (nextFood) {
            fish.targetFood = nextFood;
          } else {
            transitionFishState(FISH_STATE.CRUISING);
          }
        }
      } else {
        chooseNextFishState();
      }
    } else if (fish.state === FISH_STATE.ORBITING && fish.orbitTarget && fish.stateTimer > 0) {
      const stalk = fish.orbitTarget.stalkRef;
      const swayOffset =
        Math.sin(elapsed * stalk.swaySpeed + stalk.phase) * stalk.swayAmp + stalk.nudgeOffset;
      const cx = fish.orbitTarget.x + swayOffset;
      const cy = fish.orbitTarget.y;

      const angularVel = (fish.speed / Math.max(8.0, fish.orbitRadius)) * 1.15;
      fish.orbitAngle += angularVel * dt * 14;

      const desiredX = clamp(
        cx + Math.cos(fish.orbitAngle) * fish.orbitRadius,
        innerLeft,
        innerRight
      );
      const desiredY = clamp(
        cy + Math.sin(fish.orbitAngle) * (fish.orbitRadius * 0.65),
        topBound,
        bottomBound
      );

      const dx = desiredX - fish.x;
      const dy = desiredY - fish.y;
      if (Math.hypot(dx, dy) > 0.4) {
        fish.targetAngle = Math.atan2(dy, dx);
      }
    } else if (fish.state === FISH_STATE.RESTING && fish.stateTimer > 0) {
      const hoverX = fish.restPos.x + Math.sin(elapsed * 1.1) * 2.2;
      const hoverY = fish.restPos.y + Math.cos(elapsed * 1.5) * 1.1;
      const dx = hoverX - fish.x;
      const dy = hoverY - fish.y;
      if (Math.hypot(dx, dy) > 1.2) {
        fish.targetAngle = Math.atan2(dy, dx);
      } else {
        const gentleDir = Math.cos(fish.angle) >= 0 ? 0 : Math.PI;
        fish.targetAngle = gentleDir + Math.sin(elapsed * 0.9) * 0.14;
      }
    } else if (fish.stateTimer <= 0) {
      chooseNextFishState();
    }

    let avoidX = 0;
    let avoidY = 0;
    const margin = 15.0;

    if (fish.x < innerLeft + margin) {
      avoidX += ((innerLeft + margin - fish.x) / margin) * 1.6;
    }
    if (fish.x > innerRight - margin) {
      avoidX -= ((fish.x - (innerRight - margin)) / margin) * 1.6;
    }
    if (fish.y < topBound + 8.0) {
      avoidY += ((topBound + 8.0 - fish.y) / 8.0) * 1.4;
    }
    if (fish.y > bottomBound - 8.0) {
      avoidY -= ((fish.y - (bottomBound - 8.0)) / 8.0) * 1.4;
    }

    for (let i = 0; i < rocks.length; i++) {
      const r = rocks[i];
      if (Math.abs(r.depth - fish.depth) > 0.35) continue;
      const centerX = r.x + r.w * 0.5;
      const centerY = r.y + r.h * 0.5;
      const dx = fish.x - centerX;
      const dy = fish.y - centerY;
      const dist = Math.hypot(dx, dy);
      const minDist = Math.max(r.w * 0.65, 13.0);

      if (dist > 0.01 && dist < minDist) {
        const push = ((minDist - dist) / minDist) * 1.3;
        avoidX += (dx / dist) * push;
        avoidY += (dy / dist) * push;
      }
    }

    if (Math.abs(avoidX) > 0.01 || Math.abs(avoidY) > 0.01) {
      const desiredDirX = Math.cos(fish.targetAngle) + avoidX;
      const desiredDirY = Math.sin(fish.targetAngle) + avoidY;
      fish.targetAngle = Math.atan2(desiredDirY, desiredDirX);
    }

    const diff = angleDiff(fish.targetAngle, fish.angle);
    const turnRate =
      fish.state === FISH_STATE.ALERT
        ? 5.2
        : fish.state === FISH_STATE.FORAGING
        ? 4.4
        : fish.state === FISH_STATE.RESTING
        ? 2.0
        : 3.2;
    fish.angle += clamp(diff, -turnRate * dt, turnRate * dt);
    fish.angle = Math.atan2(Math.sin(fish.angle), Math.cos(fish.angle));

    fish.vx = Math.cos(fish.angle) * fish.speed;
    fish.vy = Math.sin(fish.angle) * fish.speed * 0.72;

    fish.x = clamp(fish.x + fish.vx * stepScale, innerLeft, innerRight);
    fish.y = clamp(fish.y + fish.vy * stepScale, topBound, bottomBound);

    if (
      (fish.x <= innerLeft + 0.5 || fish.x >= innerRight - 0.5) &&
      fish.turnCooldown <= 0
    ) {
      const centerY = (topBound + bottomBound) * 0.5;
      fish.targetAngle = Math.atan2(centerY - fish.y, jar.centerX - fish.x);
      fish.turnCooldown = 0.6;
    }
  }

  function updateEnvironmentAndParticles(dt) {
    if (pointer.active && pointer.inWater) {
      const moveSpeed = Math.hypot(pointer.x - pointer.prevX, pointer.y - pointer.prevY);
      if (moveSpeed > 0.25) {
        for (let i = 0; i < grassStalks.length; i++) {
          const s = grassStalks[i];
          const topY = s.baseY - s.height;
          if (pointer.y >= topY - 4 && pointer.y <= s.baseY + 2) {
            const dx = s.baseX - pointer.x;
            if (Math.abs(dx) < 12) {
              const push = ((12 - Math.abs(dx)) / 12) * clamp(moveSpeed * 0.16, 0.2, 1.4);
              s.nudgeVel += (dx >= 0 ? 1 : -1) * push;
            }
          }
        }
        for (let i = 0; i < stemPlants.length; i++) {
          const sp = stemPlants[i];
          const topY = sp.baseY - sp.height;
          if (pointer.y >= topY - 4 && pointer.y <= sp.baseY + 2) {
            const dx = sp.baseX - pointer.x;
            if (Math.abs(dx) < 14) {
              const push = ((14 - Math.abs(dx)) / 14) * clamp(moveSpeed * 0.16, 0.2, 1.4);
              sp.nudgeVel += (dx >= 0 ? 1 : -1) * push;
            }
          }
        }
        for (let i = 0; i < motes.length; i++) {
          const m = motes[i];
          const dx = m.x - pointer.x;
          const dy = m.y - pointer.y;
          const dist = Math.hypot(dx, dy);
          if (dist > 0.1 && dist < 14) {
            const force = ((14 - dist) / 14) * 0.04;
            m.vx = clamp(m.vx + (dx / dist) * force, -0.22, 0.22);
            m.vy = clamp(m.vy + (dy / dist) * force, -0.22, 0.22);
          }
        }
      }
      pointer.prevX = pointer.x;
      pointer.prevY = pointer.y;
    }

    for (let i = 0; i < grassStalks.length; i++) {
      const s = grassStalks[i];
      if (Math.abs(s.nudgeOffset) > 0.001 || Math.abs(s.nudgeVel) > 0.001) {
        s.nudgeVel += -s.nudgeOffset * 14 * dt;
        s.nudgeVel *= Math.exp(-5.5 * dt);
        s.nudgeOffset += s.nudgeVel * dt;
      }
    }

    for (let i = 0; i < stemPlants.length; i++) {
      const sp = stemPlants[i];
      if (Math.abs(sp.nudgeOffset) > 0.001 || Math.abs(sp.nudgeVel) > 0.001) {
        sp.nudgeVel += -sp.nudgeOffset * 12 * dt;
        sp.nudgeVel *= Math.exp(-5.0 * dt);
        sp.nudgeOffset += sp.nudgeVel * dt;
      }
    }

    for (let i = 0; i < rocks.length; i++) {
      if (rocks[i].glintTimer > 0) {
        rocks[i].glintTimer = Math.max(0, rocks[i].glintTimer - dt);
      }
    }

    for (let i = surfaceRipples.length - 1; i >= 0; i--) {
      const r = surfaceRipples[i];
      r.radius += 16 * dt;
      r.alpha -= 0.72 * dt;
      if (r.alpha <= 0.02 || r.radius >= r.maxRadius) {
        surfaceRipples.splice(i, 1);
      }
    }

    for (let i = foodPellets.length - 1; i >= 0; i--) {
      const f = foodPellets[i];
      f.phase += dt * 3.2;

      if (!f.inWater) {
        f.vy += 0.36 * dt;
        f.y += f.vy * stepScale;
        f.x += f.vx * stepScale;

        if (f.y >= jar.waterLine) {
          f.inWater = true;
          f.y = jar.waterLine + 0.5;
          f.vy = 0.075;
          spawnSurfaceRipple(f.x, 0.35);
          spawnBubble(f.x, jar.waterLine + 1.5, 0.9, f.depth);
        }
      } else {
        if (f.y < jar.sandTop - 1.5) {
          f.y += f.vy * stepScale;
          f.x += Math.sin(f.phase) * 0.06 * stepScale;
          f.x = clamp(f.x, jar.left + 5, jar.right - 5);
        } else {
          f.y = jar.sandTop - 1.2;
          f.settledTimer += dt;
          if (f.settledTimer > 14.0) {
            foodPellets.splice(i, 1);
          }
        }
      }
    }

    for (let i = heartParticles.length - 1; i >= 0; i--) {
      const h = heartParticles[i];
      h.life -= dt;
      h.phase += dt * 4.2;
      h.y += h.vy * stepScale;
      h.x += (h.vx + Math.sin(h.phase) * 0.08) * stepScale;
      if (h.life <= 0 || h.y <= jar.waterLine + 1.5) {
        heartParticles.splice(i, 1);
      }
    }

    if (Math.random() < dt * 2.8 && rocks.length > 0) {
      const r = rocks[Math.floor(Math.random() * rocks.length)];
      const bDepth = clamp(r.depth + randRange(-0.15, 0.15), 0.12, 0.96);
      spawnBubble(
        r.x + randRange(2, r.w - 2),
        r.y + 1,
        randRange(0.9, 2.0) * depthScale(bDepth),
        bDepth
      );
    }

    for (let i = bubbles.length - 1; i >= 0; i--) {
      const b = bubbles[i];
      b.wobblePhase += b.wobbleSpeed * dt;
      b.y -= b.vy * stepScale;
      b.x += Math.sin(b.wobblePhase) * 0.11 * stepScale;
      b.x = clamp(b.x, jar.left + 4, jar.right - 4);

      if (b.y <= jar.waterLine + 1.0) {
        if (b.radius > 1.6 && Math.random() < 0.35) {
          spawnSurfaceRipple(b.x, 0.15);
        }
        bubbles.splice(i, 1);
      }
    }

    for (let i = 0; i < motes.length; i++) {
      const m = motes[i];
      m.phase += dt * 1.5;
      m.vx *= Math.exp(-0.8 * dt);
      m.vy *= Math.exp(-0.8 * dt);
      m.x += (m.vx + Math.cos(m.phase) * 0.04) * stepScale;
      m.y += (m.vy + Math.sin(m.phase * 0.7) * 0.03) * stepScale;

      if (m.x < jar.left + 4) m.x = jar.right - 4;
      if (m.x > jar.right - 4) m.x = jar.left + 4;
      if (m.y < jar.waterLine + 2) m.y = jar.sandTop - 2;
      if (m.y > jar.sandTop - 2) m.y = jar.waterLine + 2;
    }
  }

  function drawJarAndEnvironment() {
    const glassDeep = hexToUint32("#244354");
    const glassBright = hexToUint32("#78c8e6");
    const waterFar = hexToUint32("#091822");
    const waterDark = hexToUint32("#0d222e");
    const waterMid = hexToUint32("#183b4d");
    const waterLight = hexToUint32("#347896");
    const sandDark = hexToUint32("#695537");
    const sandMid = hexToUint32("#9e8356");
    const sandLight = hexToUint32("#d1b788");

    const invWaterSpan = 1 / Math.max(1, jar.sandTop - jar.waterLine);
    const invSandSpan = 1 / Math.max(1, jar.bottom - jar.sandTop);

    for (let y = jar.waterLine + 1; y < jar.sandTop; y++) {
      const depthRatio = (y - jar.waterLine) * invWaterSpan;
      const yWaveA = elapsed * 1.5 + y * 0.11;
      const yWaveB = -elapsed * 1.15 - y * 0.16;

      for (let x = jar.left + 1; x < jar.right; x++) {
        const cylNorm = clamp((x - jar.centerX) / jar.halfW, -1, 1);
        const cylShade = Math.sqrt(Math.max(0.15, 1 - cylNorm * cylNorm * 0.65));

        const causticA = Math.sin(x * 0.16 + yWaveA) * 0.5 + 0.5;
        const causticB = Math.cos(x * 0.12 + yWaveB) * 0.5 + 0.5;
        const caustic = causticA * causticB * (1.0 - depthRatio * 0.68) * cylShade;
        const baseTone = clamp((0.14 + caustic * 0.48 - depthRatio * 0.1) * cylShade + 0.04, 0.04, 0.72);

        if (ditherPass(baseTone, x, y)) {
          const col = ditherMixUint(waterMid, waterLight, caustic * 0.85, x, y);
          setPixel(x, y, col, false, 0.02);
        } else if (ditherPass(0.28 - depthRatio * 0.15, x, y)) {
          setPixel(x, y, ditherMixUint(waterFar, waterDark, cylShade, x, y), false, 0.01);
        }
      }
    }

    const cornerR = 5;
    for (let y = jar.top; y <= jar.bottom; y++) {
      for (let x = jar.left; x <= jar.right; x++) {
        let inCornerCut = false;
        if (x < jar.left + cornerR && y < jar.top + cornerR) {
          if (Math.hypot(jar.left + cornerR - x, jar.top + cornerR - y) > cornerR + 0.4) inCornerCut = true;
        } else if (x > jar.right - cornerR && y < jar.top + cornerR) {
          if (Math.hypot(x - (jar.right - cornerR), jar.top + cornerR - y) > cornerR + 0.4) inCornerCut = true;
        } else if (x < jar.left + cornerR && y > jar.bottom - cornerR) {
          if (Math.hypot(jar.left + cornerR - x, y - (jar.bottom - cornerR)) > cornerR + 0.4) inCornerCut = true;
        } else if (x > jar.right - cornerR && y > jar.bottom - cornerR) {
          if (Math.hypot(x - (jar.right - cornerR), y - (jar.bottom - cornerR)) > cornerR + 0.4) inCornerCut = true;
        }
        if (inCornerCut) continue;

        const isTop =
          y === jar.top ||
          (y < jar.top + cornerR &&
            (x <= jar.left + cornerR || x >= jar.right - cornerR) &&
            Math.abs(
              Math.hypot(
                x < jar.left + cornerR ? jar.left + cornerR - x : x - (jar.right - cornerR),
                jar.top + cornerR - y
              ) - cornerR
            ) < 0.85);
        const isBottom =
          y === jar.bottom ||
          (y > jar.bottom - cornerR &&
            (x <= jar.left + cornerR || x >= jar.right - cornerR) &&
            Math.abs(
              Math.hypot(
                x < jar.left + cornerR ? jar.left + cornerR - x : x - (jar.right - cornerR),
                y - (jar.bottom - cornerR)
              ) - cornerR
            ) < 0.85);
        const isLeft = x === jar.left && y >= jar.top + cornerR && y <= jar.bottom - cornerR;
        const isRight = x === jar.right && y >= jar.top + cornerR && y <= jar.bottom - cornerR;

        if (isTop || isBottom || isLeft || isRight) {
          const shimmer = 0.45 + 0.45 * Math.sin(x * 0.25 + y * 0.2 - elapsed * 1.2);
          const col = ditherMixUint(glassDeep, glassBright, shimmer, x, y);
          setPixel(x, y, col, shimmer > 0.78, 0.99);
        } else if (x === jar.left + 1 && y > jar.top + 3 && y < jar.bottom - 3) {
          const streak = 0.25 + 0.55 * Math.sin(y * 0.14 - elapsed * 0.9);
          if (ditherPass(streak, x, y)) {
            setPixel(x, y, ditherMixUint(glassDeep, glassBright, streak, x, y), false, 0.98);
          }
        }
      }
    }

    for (let x = jar.left + 1; x < jar.right; x++) {
      let waveOffset = Math.sin(elapsed * 2.0 + x * 0.18) * 0.6;
      let rippleBoost = 0;

      if (pointer.active && Math.abs(pointer.y - jar.waterLine) < 10) {
        const dx = Math.abs(x - pointer.x);
        if (dx < 14) {
          const falloff = (14 - dx) / 14;
          waveOffset += Math.sin(dx * 0.9 - elapsed * 8) * 0.7 * falloff;
          rippleBoost += 0.35 * falloff;
        }
      }

      for (let i = 0; i < surfaceRipples.length; i++) {
        const r = surfaceRipples[i];
        const distFromRing = Math.abs(Math.abs(x - r.x) - r.radius);
        if (distFromRing < 2.2) {
          const ringStrength = (1 - distFromRing / 2.2) * r.alpha;
          waveOffset -= ringStrength * 0.85;
          rippleBoost += ringStrength * 0.55;
        }
      }

      const wave = clamp(Math.sin(elapsed * 2.4 + x * 0.22) * 0.5 + 0.5 + rippleBoost, 0, 1);
      const yOffset = Math.round(waveOffset);
      const col = ditherMixUint(waterLight, glassBright, wave, x, jar.waterLine + yOffset);
      setPixel(x, jar.waterLine + yOffset, col, true, 0.96);
      if (ditherPass(wave * 0.55, x, jar.waterLine + yOffset + 1)) {
        setPixel(x, jar.waterLine + yOffset + 1, waterMid, false, 0.85);
      }
    }

    for (let y = jar.sandTop; y < jar.bottom; y++) {
      const sandDepth = (y - jar.sandTop) * invSandSpan;
      const approxDepth = clamp(0.15 + sandDepth * 0.8, 0.15, 0.95);
      for (let x = jar.left + 1; x < jar.right; x++) {
        if (!isEmptyCell(x, y) && y >= jar.bottom - cornerR) continue;

        const dune = Math.sin(x * 0.1 + sandDepth * 2.2) * 0.14;
        const lightFactor = clamp(0.78 - sandDepth * 0.68 + dune, 0.08, 0.92);
        const col =
          lightFactor > 0.45
            ? ditherMixUint(sandMid, sandLight, (lightFactor - 0.45) * 1.8, x, y)
            : ditherMixUint(sandDark, sandMid, lightFactor * 2.1, x, y);

        setPixel(x, y, col, false, approxDepth);
      }
    }

    for (let i = 0; i < sandPebbles.length; i++) {
      const p = sandPebbles[i];
      const minX = Math.floor(p.x - p.rx);
      const maxX = Math.ceil(p.x + p.rx);
      const minY = Math.floor(p.y - p.ry);
      const maxY = Math.ceil(p.y + p.ry);
      const invRx = 1 / p.rx;
      const invRy = 1 / p.ry;

      for (let py = minY; py <= maxY; py++) {
        for (let px = minX; px <= maxX; px++) {
          const nx = (px - p.x) * invRx;
          const ny = (py - p.y) * invRy;
          if (nx * nx + ny * ny <= 1.0) {
            const shade = clamp(0.75 - ny * 0.35 - nx * 0.2, 0.2, 0.95);
            if (ditherPass(shade, px, py)) {
              setPixel(px, py, p.color, false, p.depth);
            }
          }
        }
      }
    }
  }

  function drawGrassStalk(stalk) {
    const parallaxX = cylindricalShift(stalk.baseX, stalk.depth);
    const depthAtten = lerp(0.68, 1.05, stalk.depth);
    const invHeight = 1 / Math.max(1, stalk.height - 1);

    for (let h = 0; h < stalk.height; h++) {
      const y = stalk.baseY - h;
      if (y <= jar.waterLine || y >= jar.bottom) continue;

      const heightRatio = h * invHeight;
      const bendCurve = Math.pow(heightRatio, 1.35);
      const sway =
        Math.sin(elapsed * stalk.swaySpeed + stalk.phase - h * 0.13) *
          stalk.swayAmp *
          bendCurve +
        stalk.nudgeOffset * bendCurve;

      const centerX = clamp(stalk.baseX + parallaxX + sway, jar.left + 2, jar.right - 2);
      const halfW = stalk.thickness * (1.0 - heightRatio * 0.55) * 0.5;
      const minX = Math.floor(centerX - halfW - 0.5);
      const maxX = Math.ceil(centerX + halfW + 0.5);

      for (let px = minX; px <= maxX; px++) {
        if (px <= jar.left || px >= jar.right) continue;
        const distFromCenter = Math.abs(px - centerX) / Math.max(0.4, halfW + 0.5);
        if (distFromCenter > 1.0) continue;

        const edgeShade = (1.0 - distFromCenter * 0.45) * depthAtten;
        const tipMix = clamp(heightRatio * 0.85 + stalk.depth * 0.22, 0.1, 0.95);

        let col;
        if (h >= stalk.height - 2) {
          col = ditherMixUint(stalk.palette.mid, stalk.palette.tip, clamp(edgeShade, 0, 1), px, y);
        } else {
          col = ditherMixUint(stalk.palette.dark, stalk.palette.mid, clamp(tipMix * edgeShade, 0, 1), px, y);
        }

        if (ditherPass(clamp(edgeShade * 0.92, 0.15, 0.98), px, y)) {
          setPixel(px, y, col, h >= stalk.height - 1 && stalk.depth > 0.55, stalk.depth);
        }
      }
    }
  }

  function drawStemPlant(plant) {
    const parallaxX = cylindricalShift(plant.baseX, plant.depth);
    const depthAtten = lerp(0.7, 1.05, plant.depth);
    const invHeight = 1 / Math.max(1, plant.height - 1);

    for (let h = 0; h < plant.height; h++) {
      const y = plant.baseY - h;
      if (y <= jar.waterLine || y >= jar.bottom) continue;

      const heightRatio = h * invHeight;
      const bendCurve = Math.pow(heightRatio, 1.3);
      const sway =
        Math.sin(elapsed * plant.swaySpeed + plant.phase - h * 0.12) *
          plant.swayAmp *
          bendCurve +
        plant.nudgeOffset * bendCurve;

      const cx = clamp(plant.baseX + parallaxX + sway, jar.left + 2, jar.right - 2);
      const gx = Math.round(cx);
      if (gx > jar.left && gx < jar.right) {
        setPixel(gx, y, plant.palette.stem, false, plant.depth);
      }

      if (h > 3 && h < plant.height - 1 && h % plant.leafStep === 0) {
        const side = ((h / plant.leafStep) & 1) === 0 ? 1 : -1;
        const len = Math.max(2, Math.round(plant.leafLen * (1.05 - heightRatio * 0.45)));
        for (let lx = 1; lx <= len; lx++) {
          const px = gx + side * lx;
          const py = y - Math.floor(lx * 0.45);
          if (px <= jar.left || px >= jar.right || py <= jar.waterLine || py >= jar.bottom) continue;
          const t = (lx / len) * depthAtten;
          const col = ditherMixUint(plant.palette.leafDark, plant.palette.leafLight, clamp(t, 0.1, 0.95), px, py);
          setPixel(px, py, col, lx === len && plant.depth > 0.58, plant.depth);
        }
      }
    }
  }

  function drawRock(rock) {
    const parallaxX = cylindricalShift(rock.x + rock.w * 0.5, rock.depth);
    const cx = rock.x + rock.w * 0.5 + parallaxX;
    const rx = rock.w * 0.5;
    const ry = rock.h;
    const baseY = rock.y + rock.h - 1;
    const depthAtten = lerp(0.72, 1.05, rock.depth);
    const glintBoost = rock.glintTimer > 0 ? Math.sin(rock.glintTimer * Math.PI * 3) * 0.35 : 0;

    for (let py = rock.y; py <= baseY; py++) {
      if (py <= jar.waterLine || py >= jar.bottom) continue;
      const dy = (baseY - py) / Math.max(1, ry);
      const spanX = rx * Math.sqrt(Math.max(0, 1 - dy * dy * 0.72));

      for (let px = Math.floor(cx - spanX); px <= Math.ceil(cx + spanX); px++) {
        if (px <= jar.left || px >= jar.right) continue;
        const nx = (px - cx) / Math.max(1, rx);
        const lightScore = clamp((0.55 + dy * 0.45 - nx * 0.35) * depthAtten + glintBoost, 0.1, 0.98);
        const col =
          glintBoost > 0.12 && lightScore > 0.76
            ? ditherMixUint(rock.light, rock.highlight, (lightScore - 0.76) * 4, px, py)
            : ditherMixUint(rock.dark, rock.light, lightScore, px, py);
        setPixel(px, py, col, glintBoost > 0.15 && lightScore > 0.85, rock.depth);
      }
    }
  }

  function isPixelOccludedForFish(px, py) {
    for (let i = 0; i < grassStalks.length; i++) {
      const s = grassStalks[i];
      if (s.depth <= fish.depth + 0.03) continue;
      if (py > s.baseY || py < s.baseY - s.height + 1) continue;

      const h = s.baseY - py;
      const heightRatio = h / Math.max(1, s.height - 1);
      const bendCurve = Math.pow(heightRatio, 1.35);
      const sway =
        Math.sin(elapsed * s.swaySpeed + s.phase - h * 0.13) *
          s.swayAmp *
          bendCurve +
        s.nudgeOffset * bendCurve;
      const parallaxX = cylindricalShift(s.baseX, s.depth);
      const centerX = s.baseX + parallaxX + sway;
      const halfW = s.thickness * (1.0 - heightRatio * 0.55) * 0.5 + 0.55;

      if (Math.abs(px - centerX) <= halfW && ditherPass(0.88, px, py)) {
        return true;
      }
    }

    for (let i = 0; i < rocks.length; i++) {
      const r = rocks[i];
      if (r.depth <= fish.depth + 0.03) continue;
      const parallaxX = cylindricalShift(r.x + r.w * 0.5, r.depth);
      const cx = r.x + r.w * 0.5 + parallaxX;
      const rx = r.w * 0.5;
      const ry = r.h;
      const baseY = r.y + r.h - 1;

      if (py >= r.y && py <= baseY) {
        const dy = (baseY - py) / Math.max(1, ry);
        const spanX = rx * Math.sqrt(Math.max(0, 1 - dy * dy * 0.72));
        if (Math.abs(px - cx) <= spanX) {
          return true;
        }
      }
    }

    return false;
  }

  function drawFish() {
    const facingLeft = Math.cos(fish.angle) < -0.08;
    const dir = facingLeft ? -1 : 1;
    const pScale = depthScale(fish.depth);
    const fishParallaxX = cylindricalShift(fish.x, fish.depth);
    const fx = fish.x + fishParallaxX;
    const fy = fish.y;

    const tailAmp =
      fish.state === FISH_STATE.RESTING
        ? 1.1
        : fish.state === FISH_STATE.ALERT || fish.eatFlutterTimer > 0
        ? 3.1
        : 2.3;
    const tailWag = Math.sin(fish.tailPhase) * tailAmp * pScale;
    const finFlap = Math.sin(fish.finPhase) * (fish.state === FISH_STATE.RESTING ? 0.6 : 1.2) * pScale;
    const gillPulse = Math.sin(fish.gillPhase) > 0.35;
    const pitch = clamp(fish.vy * 4.5, -2.5, 2.5) * pScale;

    const depthTint = clamp((fish.depth - 0.15) / 0.8, 0, 1);
    const bodyOrange = ditherMixUint(
      hexToUint32("#d96b2b"),
      hexToUint32("#ff8c42"),
      depthTint,
      Math.round(fx),
      Math.round(fy)
    );
    const bodyGold = hexToUint32("#ffd166");
    const bodyDeep = hexToUint32("#b84718");
    const finColor = hexToUint32("#ffaa64");
    const whiteCol = hexToUint32("#ffffff");

    const bodyRx = 5.4 * pScale;
    const bodyRy = 2.7 * pScale;
    const tailLen = 4.2 * pScale;
    const invBodyRxSq = 1 / (bodyRx * bodyRx);
    const invBodyRySq = 1 / (bodyRy * bodyRy);

    const minX = Math.floor(fx - bodyRx - tailLen - 2);
    const maxX = Math.ceil(fx + bodyRx + tailLen + 2);
    const minY = Math.floor(fy - bodyRy - 4 * pScale - 2);
    const maxY = Math.ceil(fy + bodyRy + 4 * pScale + 2);

    for (let py = minY; py <= maxY; py++) {
      for (let px = minX; px <= maxX; px++) {
        if (px <= jar.left || px >= jar.right || py <= jar.waterLine || py >= jar.sandTop) {
          continue;
        }

        if (isPixelOccludedForFish(px, py)) {
          continue;
        }

        const localX = (px - fx) * dir;
        const localY = py - fy - pitch * (1.0 - Math.abs(localX) / (bodyRx + 2 * pScale));

        const normBody = localX * localX * invBodyRxSq + localY * localY * invBodyRySq;
        if (normBody <= 1.0) {
          const isGillSlit =
            gillPulse &&
            localX >= 0.8 * pScale &&
            localX <= 1.5 * pScale &&
            Math.abs(localY) <= bodyRy * 0.55;
          if (isGillSlit) {
            setPixel(px, py, bodyDeep, false, fish.depth);
            continue;
          }
          const stripe = 0.5 + 0.5 * Math.sin((localX / pScale) * 1.15 + elapsed * 2.5);
          const bellyShade = clamp(0.65 - localY / (bodyRy * 2.5), 0.15, 0.95);
          const baseCol = ditherMixUint(bodyDeep, bodyOrange, bellyShade, px, py);
          const finalCol = ditherMixUint(baseCol, bodyGold, stripe * 0.45, px, py);
          setPixel(px, py, finalCol, false, fish.depth);
          continue;
        }

        if (localX < -bodyRx + 0.6 * pScale && localX > -bodyRx - tailLen) {
          const tailT = (-bodyRx + 0.6 * pScale - localX) / (tailLen + 0.6 * pScale);
          const tailCenterY = tailWag * tailT * 1.25;
          const tailHalfSpan = (1.0 + tailT * 2.4) * pScale;
          if (Math.abs(localY - tailCenterY) <= tailHalfSpan) {
            const edgeFade = 1.0 - Math.abs(localY - tailCenterY) / (tailHalfSpan + 0.4);
            if (ditherPass(edgeFade * 0.9 + 0.1, px, py)) {
              setPixel(px, py, ditherMixUint(bodyDeep, finColor, tailT * 0.7, px, py), false, fish.depth);
            }
          }
        }

        if (
          localX >= -2.2 * pScale &&
          localX <= 1.6 * pScale &&
          localY < -bodyRy + 0.4 * pScale &&
          localY >= -bodyRy - 2.0 * pScale + finFlap * 0.4
        ) {
          if (ditherPass(0.75, px, py)) {
            setPixel(px, py, finColor, false, fish.depth);
          }
        }

        if (
          localX >= -1.2 * pScale &&
          localX <= 1.2 * pScale &&
          localY > bodyRy - 0.4 * pScale &&
          localY <= bodyRy + 1.6 * pScale - finFlap * 0.3
        ) {
          if (ditherPass(0.68, px, py)) {
            setPixel(px, py, finColor, false, fish.depth);
          }
        }
      }
    }

    const eyeX = Math.round(fx + dir * 2.8 * pScale);
    const eyeY = Math.round(fy - 0.5 * pScale + pitch * 0.5);
    if (
      eyeX > jar.left &&
      eyeX < jar.right &&
      eyeY > jar.waterLine &&
      eyeY < jar.sandTop &&
      !isPixelOccludedForFish(eyeX, eyeY)
    ) {
      setPixel(eyeX, eyeY, whiteCol, fish.depth > 0.45, fish.depth);
    }
  }

  function drawFoodAndHearts() {
    const foodCore = hexToUint32("#f4a261");
    const foodRim = hexToUint32("#e76f51");

    for (let i = 0; i < foodPellets.length; i++) {
      const f = foodPellets[i];
      const fx = Math.round(f.x + (f.inWater ? cylindricalShift(f.x, f.depth) : 0));
      const fy = Math.round(f.y);
      if (fx <= jar.left || fx >= jar.right || fy <= jar.top || fy >= jar.sandTop) continue;

      setPixel(fx, fy, foodCore, false, f.depth);
      if (ditherPass(0.65, fx + 1, fy)) setPixel(fx + 1, fy, foodRim, false, f.depth);
      if (ditherPass(0.65, fx, fy + 1)) setPixel(fx, fy + 1, foodRim, false, f.depth);
    }

    const heartBright = hexToUint32("#ff5c8a");
    const heartSoft = hexToUint32("#ff8fab");
    const heartOffsets = [
      [-1, -1],
      [1, -1],
      [-2, 0],
      [-1, 0],
      [0, 0],
      [1, 0],
      [2, 0],
      [-1, 1],
      [0, 1],
      [1, 1],
      [0, 2]
    ];

    for (let i = 0; i < heartParticles.length; i++) {
      const h = heartParticles[i];
      const fade = clamp(h.life / h.maxLife, 0, 1);
      const hx = Math.round(h.x);
      const hy = Math.round(h.y);

      for (let k = 0; k < heartOffsets.length; k++) {
        const px = hx + heartOffsets[k][0];
        const py = hy + heartOffsets[k][1];
        if (px <= jar.left || px >= jar.right || py <= jar.waterLine || py >= jar.sandTop) continue;
        if (ditherPass(fade * 0.95, px, py)) {
          const col = heartOffsets[k][1] <= 0 ? heartBright : heartSoft;
          setPixel(px, py, col, fade > 0.55, h.depth);
        }
      }
    }
  }

  function drawParticles() {
    const moteDark = hexToUint32("#264c61");
    const moteLight = hexToUint32("#529bb8");
    const bubbleRim = hexToUint32("#b5ecff");
    const bubbleFill = hexToUint32("#5bb8db");

    for (let i = 0; i < motes.length; i++) {
      const m = motes[i];
      if (m.y > jar.waterLine && m.y < jar.sandTop) {
        const gx = Math.round(m.x + cylindricalShift(m.x, m.depth));
        const gy = Math.round(m.y);
        if (isEmptyCell(gx, gy) && ditherPass(0.35 + m.depth * 0.4, gx, gy)) {
          setPixel(gx, gy, ditherMixUint(moteDark, moteLight, m.depth, gx, gy), false, m.depth);
        }
      }
    }

    for (let i = 0; i < bubbles.length; i++) {
      const b = bubbles[i];
      if (b.y <= jar.waterLine || b.y >= jar.sandTop) continue;

      const bx = b.x + cylindricalShift(b.x, b.depth);
      const by = b.y;
      const minX = Math.floor(bx - b.radius);
      const maxX = Math.ceil(bx + b.radius);
      const minY = Math.floor(by - b.radius);
      const maxY = Math.ceil(by + b.radius);

      for (let py = minY; py <= maxY; py++) {
        for (let px = minX; px <= maxX; px++) {
          if (px <= jar.left || px >= jar.right || py <= jar.waterLine || py >= jar.sandTop) {
            continue;
          }
          const dist = Math.hypot(px - bx, py - by);
          if (dist <= b.radius) {
            const rim = dist >= b.radius - 0.75;
            const col = rim ? bubbleRim : bubbleFill;
            if (rim || ditherPass(0.55, px, py)) {
              setPixel(px, py, col, rim && b.depth > 0.5, b.depth);
            }
          }
        }
      }
    }
  }

  function renderGridToCanvas() {
    imgBuf32.set(gridPixels);
    ctx.putImageData(imgData, 0, 0);
  }

  function tick(timestamp) {
    if (!lastTime) lastTime = timestamp;
    const rawDt = (timestamp - lastTime) * 0.001;
    lastTime = timestamp;
    const dt = clamp(rawDt, 0.001, 0.05);
    stepScale = dt * 60;
    elapsed += dt;

    updateFish(dt);
    updateEnvironmentAndParticles(dt);

    clearGrid();
    drawJarAndEnvironment();

    for (let i = 0; i < backRockIndices.length; i++) drawRock(rocks[backRockIndices[i]]);
    for (let i = 0; i < backStemIndices.length; i++) drawStemPlant(stemPlants[backStemIndices[i]]);
    for (let i = 0; i < backGrassIndices.length; i++) drawGrassStalk(grassStalks[backGrassIndices[i]]);

    for (let i = 0; i < midRockIndices.length; i++) drawRock(rocks[midRockIndices[i]]);
    for (let i = 0; i < midStemIndices.length; i++) drawStemPlant(stemPlants[midStemIndices[i]]);
    for (let i = 0; i < midGrassIndices.length; i++) drawGrassStalk(grassStalks[midGrassIndices[i]]);

    drawFish();
    drawFoodAndHearts();

    for (let i = 0; i < frontRockIndices.length; i++) drawRock(rocks[frontRockIndices[i]]);
    for (let i = 0; i < frontStemIndices.length; i++) drawStemPlant(stemPlants[frontStemIndices[i]]);
    for (let i = 0; i < frontGrassIndices.length; i++) drawGrassStalk(grassStalks[frontGrassIndices[i]]);

    drawParticles();
    renderGridToCanvas();

    requestAnimationFrame(tick);
  }

  function handlePointerMove(clientX, clientY) {
    const gx = clientX / cellSize;
    const gy = clientY / cellSize;
    pointer.prevX = pointer.active ? pointer.x : gx;
    pointer.prevY = pointer.active ? pointer.y : gy;
    pointer.x = gx;
    pointer.y = gy;
    pointer.active = true;
    pointer.inWater =
      gx > jar.left && gx < jar.right && gy >= jar.waterLine - 3 && gy < jar.sandTop;
  }

  function handlePointerInteract(clientX, clientY) {
    const gx = clientX / cellSize;
    const gy = clientY / cellSize;

    if (gx > jar.left + 2 && gx < jar.right - 2 && gy < jar.waterLine) {
      spawnFood(gx, gy);
      return;
    }

    if (gx >= jar.left && gx <= jar.right && gy >= jar.waterLine && gy <= jar.bottom) {
      const clampedY = clamp(gy, jar.waterLine + 2, jar.sandTop - 2);
      const clickDepth = randRange(0.25, 0.9);
      for (let i = 0; i < 6; i++) {
        const bDepth = clamp(clickDepth + randRange(-0.15, 0.15), 0.12, 0.96);
        spawnBubble(
          gx + randRange(-3.5, 3.5),
          clampedY + randRange(-1.5, 2.0),
          randRange(0.9, 2.0) * depthScale(bDepth),
          bDepth
        );
      }

      spawnSurfaceRipple(gx, 0.55);

      for (let i = 0; i < rocks.length; i++) {
        const r = rocks[i];
        if (gx >= r.x - 1 && gx <= r.x + r.w + 1 && gy >= r.y - 1 && gy <= r.y + r.h + 1) {
          r.glintTimer = 0.65;
        }
      }

      const distToFish = Math.hypot(gx - fish.x, clampedY - fish.y);
      if (distToFish < 18) {
        fish.targetAngle = Math.atan2(fish.y - clampedY, fish.x - gx);
        transitionFishState(FISH_STATE.ALERT);
      } else if (fish.state !== FISH_STATE.FORAGING) {
        fish.targetAngle = Math.atan2(clampedY - fish.y, gx - fish.x);
        if (fish.state === FISH_STATE.RESTING) {
          transitionFishState(FISH_STATE.CRUISING);
        } else {
          fish.stateTimer = randRange(1.4, 2.6);
        }
      }
    }
  }

  canvas.addEventListener("pointermove", (e) => {
    handlePointerMove(e.clientX, e.clientY);
  });

  canvas.addEventListener("pointerleave", () => {
    pointer.active = false;
    pointer.inWater = false;
  });

  canvas.addEventListener("pointerdown", (e) => {
    handlePointerMove(e.clientX, e.clientY);
    handlePointerInteract(e.clientX, e.clientY);
  });

  window.addEventListener("resize", () => {
    resizeWorld();
  });

  window.addEventListener("load", () => {
    resizeWorld();
    requestAnimationFrame(tick);
  });
})();
