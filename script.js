import { initializeApp } from "https://www.gstatic.com/firebasejs/13.4.0/firebase-app.js";
import { getAuth, signInAnonymously } from "https://www.gstatic.com/firebasejs/13.4.0/firebase-auth.js";
import { getDatabase, ref, set, onValue } from "https://www.gstatic.com/firebasejs/13.4.0/firebase-database.js";

(function () {
  "use strict";

  const canvas = document.getElementById("world");
  const ctx = canvas.getContext("2d", { alpha: false });

  const firebaseConfig = {
    apiKey: "AIzaSyAL5nMn3cz41ejuzdIf9rQYUsp2q_YHLG4",
    authDomain: "fihtank.firebaseapp.com",
    databaseURL: "https://fihtank-default-rtdb.asia-southeast1.firebasedatabase.app",
    projectId: "fihtank",
    storageBucket: "fihtank.firebasestorage.app",
    messagingSenderId: "408782023308",
    appId: "1:408782023308:web:fbb94ab17a659e2280a9a9"
  };

  let db = null;
  let auth = null;
  let currentUser = null;
  let syncDbRef = null;
  let syncReady = false;
  let isLeader = false;
  let leaderId = "";
  let lastHeartbeat = 0;
  let lastBroadcast = 0;
  let lastRemoteUpdate = 0;

  const clientId =
    typeof crypto !== "undefined" && typeof crypto.randomUUID === "function"
      ? crypto.randomUUID()
      : "client_" + Math.random().toString(36).slice(2) + "_" + Date.now();

  const remoteFish = {
    x: 190,
    y: 105,
    vx: 0.45,
    vy: 0,
    angle: 0,
    targetAngle: 0,
    pitchAngle: 0,
    speed: 0.48,
    state: 0,
    depth: 0.5,
    targetDepth: 0.5,
    sandDashDir: 1,
    sandDashEndX: 190,
    hasSnapshot: false
  };

  let cellSize = 2;
  let cols = 380;
  let rows = 214;

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
    left: 28,
    right: 352,
    top: 14,
    bottom: 200,
    sandTop: 168,
    waterLine: 44,
    centerX: 190,
    halfW: 162
  };

  let grassStalks = [];
  let stemPlants = [];
  let kelpRibbons = [];
  let fernFronds = [];
  let mossCushions = [];
  let floatingPads = [];

  let rocks = [];
  let bubbles = [];
  let motes = [];
  let sandPebbles = [];
  let sandGrains = [];
  let splashDroplets = [];
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
  let backKelpIndices = [];
  let midKelpIndices = [];
  let frontKelpIndices = [];
  let backFernIndices = [];
  let midFernIndices = [];
  let frontFernIndices = [];

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
    FORAGING: 4,
    JUMP_PREP: 5,
    AIRBORNE: 6,
    SAND_DASH: 7
  };

  const fish = {
    x: 190,
    y: 105,
    vx: 0.45,
    vy: 0.0,
    angle: 0,
    targetAngle: 0,
    pitchAngle: 0,
    rollWobble: 0,
    speed: 0.48,
    baseSpeed: 0.48,
    tailPhase: 0,
    finPhase: 0,
    gillPhase: 0,
    bodyWavePhase: 0,
    state: FISH_STATE.CRUISING,
    stateTimer: 2.0,
    energy: 0.90,
    orbitTarget: null,
    orbitAngle: 0,
    orbitRadius: 20,
    restPos: { x: 190, y: 140 },
    targetFood: null,
    eatFlutterTimer: 0,
    depth: 0.5,
    targetDepth: 0.5,
    turnCooldown: 0,
    jumpCooldown: 3.0,
    sandDashCooldown: 3.5,
    jumpStartX: 0,
    jumpPeakHeight: 0,
    sandDashDir: 1,
    sandDashEndX: 0,
    sandTrailTimer: 0
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

  function normXRatio(x) {
    const span = Math.max(1, jar.right - jar.left);
    return clamp((x - jar.left) / span, 0.04, 0.96);
  }

  function denormXRatio(rx) {
    const span = Math.max(1, jar.right - jar.left);
    return jar.left + clamp(rx, 0.04, 0.96) * span;
  }

  function normYRatio(y) {
    const span = Math.max(1, jar.sandTop - jar.top);
    return clamp((y - jar.top) / span, 0.02, 0.98);
  }

  function denormYRatio(ry) {
    const span = Math.max(1, jar.sandTop - jar.top);
    return jar.top + clamp(ry, 0.02, 0.98) * span;
  }

  const seenEventIds = new Set();
  let pendingEvents = [];

  function applyRemoteFishSnapshot(data) {
    if (!data || !currentUser || data.senderId === clientId) return;

    const nowMs = Date.now();
    const ageSec = Math.max(0, (nowMs - (data.updatedAtMs || nowMs)) * 0.001);
    if (ageSec > 12) return;

    const baseX = denormXRatio(typeof data.rx === "number" ? data.rx : 0.5);
    const baseY = denormYRatio(typeof data.ry === "number" ? data.ry : 0.5);
    const rvx = typeof data.rvx === "number" ? data.rvx : 0;
    const rvy = typeof data.rvy === "number" ? data.rvy : 0;
    const rState = typeof data.state === "number" ? data.state : FISH_STATE.CRUISING;

    let projX = baseX + rvx * ageSec * 60 * 0.45;
    let projY = baseY + rvy * ageSec * 60 * 0.45;
    if (rState === FISH_STATE.AIRBORNE) {
      const g = 0.058 * (fish.baseSpeed / 0.48);
      projY += 0.5 * g * Math.pow(ageSec * 60, 2) * 0.25;
    }

    remoteFish.x = clamp(projX, jar.left + 12, jar.right - 12);
    remoteFish.y = clamp(projY, jar.top + 4, jar.sandTop - 5);
    remoteFish.vx = rvx;
    remoteFish.vy = rvy;
    remoteFish.angle = typeof data.angle === "number" ? data.angle : 0;
    remoteFish.targetAngle = typeof data.targetAngle === "number" ? data.targetAngle : remoteFish.angle;
    remoteFish.pitchAngle = typeof data.pitchAngle === "number" ? data.pitchAngle : 0;
    remoteFish.speed = typeof data.speed === "number" ? data.speed : fish.baseSpeed;
    remoteFish.state = rState;
    remoteFish.depth = typeof data.depth === "number" ? data.depth : 0.5;
    remoteFish.targetDepth = typeof data.targetDepth === "number" ? data.targetDepth : remoteFish.depth;
    remoteFish.sandDashDir = data.sandDashDir === -1 ? -1 : 1;
    remoteFish.sandDashEndX = denormXRatio(typeof data.rDashEndX === "number" ? data.rDashEndX : 0.5);
    remoteFish.hasSnapshot = true;
    lastRemoteUpdate = performance.now();

    if (Array.isArray(data.events)) {
      for (let i = 0; i < data.events.length; i++) {
        const ev = data.events[i];
        if (!ev || !ev.id || ev.ts < nowMs - 8000) continue;
        if (seenEventIds.has(ev.id)) continue;
        seenEventIds.add(ev.id);
        if (seenEventIds.size > 120) {
          const firstKey = seenEventIds.values().next().value;
          seenEventIds.delete(firstKey);
        }

        const ex = denormXRatio(ev.rx);
        const ey = denormYRatio(ev.ry);
        if (ev.type === "food") {
          spawnFood(ex, clamp(ey, jar.top + 2, jar.waterLine - 1));
        } else if (ev.type === "jump") {
          spawnSurfaceRipple(ex, 0.75);
          fish.x = clamp(ex, jar.left + 16, jar.right - 16);
          fish.y = Math.min(fish.y, jar.waterLine + 3);
          triggerWaterJump(ev.dir === -1 ? -1 : 1);
        } else if (ev.type === "dash") {
          const d = ev.dir === -1 ? -1 : 1;
          spawnSandPlume(ex, jar.sandTop - 0.5, d, fish.depth, 14);
          fish.x = clamp(ex, jar.left + 16, jar.right - 16);
          fish.y = jar.sandTop - 2.6 * depthScale(fish.depth);
          triggerSandDash(d);
        } else if (ev.type === "bubble") {
          for (let b = 0; b < 6; b++) {
            spawnBubble(
              ex + randRange(-4, 4),
              clamp(ey, jar.waterLine + 3, jar.sandTop - 3),
              randRange(1.0, 2.2),
              fish.depth
            );
          }
          spawnSurfaceRipple(ex, 0.45);
        }
      }
    }
  }

  function queueGlobalEvent(type, x, y, dir) {
    if (!syncReady || !currentUser) return;
    const evId = clientId + "_" + Date.now() + "_" + Math.random().toString(36).slice(2, 7);
    seenEventIds.add(evId);
    pendingEvents.push({
      id: evId,
      type,
      rx: normXRatio(x),
      ry: normYRatio(y),
      dir: dir || 1,
      ts: Date.now()
    });
    if (pendingEvents.length > 10) pendingEvents.shift();
    pushGlobalState(true);
  }

  async function pushGlobalState(force) {
    if (!syncReady || !currentUser || !syncDbRef) return;
    const now = performance.now();
    if (!force && now - lastBroadcast < 85) return;
    lastBroadcast = now;

    const eventsToSend = pendingEvents.slice();
    pendingEvents = [];

    try {
      await set(syncDbRef, {
        senderId: clientId,
        userId: currentUser.uid,
        leaderId: isLeader ? clientId : leaderId,
        heartbeatMs: Date.now(),
        updatedAtMs: Date.now(),
        rx: normXRatio(fish.x),
        ry: normYRatio(fish.y),
        rvx: fish.vx,
        rvy: fish.vy,
        angle: fish.angle,
        targetAngle: fish.targetAngle,
        pitchAngle: fish.pitchAngle,
        speed: fish.speed,
        state: fish.state,
        depth: fish.depth,
        targetDepth: fish.targetDepth,
        sandDashDir: fish.sandDashDir,
        rDashEndX: normXRatio(fish.sandDashEndX),
        events: eventsToSend
      });
    } catch (_) {}
  }

  async function initGlobalSync() {
    try {
      const app = initializeApp(firebaseConfig);
      auth = getAuth(app);
      db = getDatabase(app);

      await signInAnonymously(auth);
      currentUser = auth.currentUser;
      if (!currentUser) return;

      syncDbRef = ref(db, "aquarium_sync/main_tank");
      syncReady = true;

      onValue(
        syncDbRef,
        (snap) => {
          if (!snap.exists()) {
            isLeader = true;
            leaderId = clientId;
            pushGlobalState(true);
            return;
          }
          const data = snap.val();
          const nowMs = Date.now();
          const hbAge = nowMs - (data.heartbeatMs || 0);
          if (!data.leaderId || hbAge > 3500) {
            isLeader = true;
            leaderId = clientId;
          } else {
            leaderId = data.leaderId;
            isLeader = leaderId === clientId;
          }
          if (!isLeader) {
            applyRemoteFishSnapshot(data);
          }
        },
        () => {}
      );

      setTimeout(() => {
        if (!remoteFish.hasSnapshot) {
          isLeader = true;
          leaderId = clientId;
          pushGlobalState(true);
        }
      }, 650);
    } catch (_) {}
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

    cellSize = clamp(Math.round(Math.min(width, height) / 360), 1, 2);

    cols = Math.max(150, Math.floor(width / cellSize));
    rows = Math.max(110, Math.floor(height / cellSize));

    canvas.width = cols;
    canvas.height = rows;

    const padX = Math.max(10, Math.floor(cols * 0.075));
    const padY = Math.max(8, Math.floor(rows * 0.065));
    jar.left = padX;
    jar.right = Math.max(jar.left + 70, cols - 1 - padX);
    jar.top = padY;
    jar.bottom = Math.max(jar.top + 60, rows - 1 - padY);

    jar.waterLine = clamp(
      jar.top + Math.floor((jar.bottom - jar.top) * 0.21),
      jar.top + 14,
      jar.bottom - 32
    );
    jar.sandTop = clamp(
      jar.bottom - Math.max(14, Math.floor((jar.bottom - jar.top) * 0.16)),
      jar.waterLine + 26,
      jar.bottom - 9
    );
    jar.centerX = (jar.left + jar.right) * 0.5;
    jar.halfW = Math.max(1, (jar.right - jar.left) * 0.5);

    fish.baseSpeed = clamp((jar.right - jar.left) * 0.00175, 0.36, 0.95);

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
    return normX * normX * normX * (depth - 0.5) * 6.5;
  }

  function populateEcosystem() {
    const innerLeft = jar.left + 12;
    const innerRight = jar.right - 12;
    const innerWidth = Math.max(60, innerRight - innerLeft);
    const floorY = jar.sandTop;
    const maxPlantHeight = Math.max(24, floorY - jar.waterLine - 8);

    rocks = [];
    const rockCount = innerWidth > 220 ? 6 : 5;
    const rockDefs = [
      { rxFrac: 0.14, width: 32, height: 15, depth: 0.22, light: "#75899e", dark: "#2b3540" },
      { rxFrac: 0.44, width: 44, height: 20, depth: 0.54, light: "#8fa4b8", dark: "#343e4a" },
      { rxFrac: 0.80, width: 35, height: 17, depth: 0.28, light: "#798da3", dark: "#2d3742" },
      { rxFrac: 0.29, width: 28, height: 13, depth: 0.84, light: "#a8bdd1", dark: "#3f4b59" },
      { rxFrac: 0.65, width: 33, height: 15, depth: 0.90, light: "#b2c7db", dark: "#43505e" },
      { rxFrac: 0.90, width: 24, height: 12, depth: 0.62, light: "#8fa4b8", dark: "#343e4a" }
    ];

    for (let i = 0; i < rockCount; i++) {
      const def = rockDefs[i % rockDefs.length];
      const scale = depthScale(def.depth);
      const w = clamp(Math.round(def.width * scale), 16, Math.floor(innerWidth * 0.22));
      const h = clamp(Math.round(def.height * scale), 9, Math.floor((floorY - jar.waterLine) * 0.22));
      const cx = Math.round(innerLeft + def.rxFrac * innerWidth + randRange(-5, 5));
      const x0 = clamp(Math.round(cx - w * 0.5), jar.left + 6, jar.right - w - 5);
      const yBaseShift = Math.round((def.depth - 0.5) * 4.0);
      const y0 = clamp(floorY - h + 1 + yBaseShift, jar.waterLine + 10, jar.bottom - h);

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
    const stalkCount = clamp(Math.floor(innerWidth / 3.4), 48, 120);
    const grassPalettes = [
      { dark: hexToUint32("#0e3d29"), mid: hexToUint32("#1c734b"), tip: hexToUint32("#4ad18c") },
      { dark: hexToUint32("#124b33"), mid: hexToUint32("#248f5d"), tip: hexToUint32("#63e6a1") },
      { dark: hexToUint32("#0b3322"), mid: hexToUint32("#176340"), tip: hexToUint32("#3ec27e") },
      { dark: hexToUint32("#184d32"), mid: hexToUint32("#2e8a57"), tip: hexToUint32("#76e89e") }
    ];

    for (let i = 0; i < stalkCount; i++) {
      const t = stalkCount === 1 ? 0.5 : i / (stalkCount - 1);
      const clusterOffset = Math.sin(t * Math.PI * 7 + i * 0.65) * 7.0;
      const baseX = clamp(
        Math.round(innerLeft + t * innerWidth + clusterOffset),
        jar.left + 6,
        jar.right - 6
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
        Math.round(randRange(maxPlantHeight * 0.30, maxPlantHeight * 0.90) * lerp(0.82, 1.12, depth)),
        16,
        maxPlantHeight
      );

      grassStalks.push({
        baseX,
        baseY: clamp(floorY + Math.round((depth - 0.5) * 4.2), jar.sandTop - 1, jar.bottom - 4),
        height,
        thickness: clamp(randRange(1.6, 3.2) * pScale, 1.4, 4.6),
        depth,
        phase: randRange(0, Math.PI * 2),
        swaySpeed: randRange(1.05, 1.95),
        swayAmp: randRange(3.2, 7.4) * lerp(0.75, 1.2, depth),
        nudgeVel: 0,
        nudgeOffset: 0,
        palette: grassPalettes[i % grassPalettes.length]
      });
    }

    stemPlants = [];
    const stemCount = clamp(Math.floor(innerWidth / 28), 6, 14);
    const stemPalettes = [
      { stem: hexToUint32("#18593c"), leafDark: hexToUint32("#1d7a50"), leafLight: hexToUint32("#54d996") },
      { stem: hexToUint32("#1b5246"), leafDark: hexToUint32("#237866"), leafLight: hexToUint32("#5ce0c5") },
      { stem: hexToUint32("#5c2434"), leafDark: hexToUint32("#8f344d"), leafLight: hexToUint32("#e06c88") }
    ];

    for (let i = 0; i < stemCount; i++) {
      const frac = (i + 0.5) / stemCount;
      const baseX = clamp(
        Math.round(innerLeft + frac * innerWidth + randRange(-8, 8)),
        jar.left + 9,
        jar.right - 9
      );
      const depth = i % 2 === 0 ? randRange(0.22, 0.46) : randRange(0.58, 0.88);
      const height = clamp(
        Math.round(randRange(maxPlantHeight * 0.42, maxPlantHeight * 0.84)),
        20,
        maxPlantHeight - 3
      );

      stemPlants.push({
        baseX,
        baseY: clamp(floorY + Math.round((depth - 0.5) * 3.8), jar.sandTop - 1, jar.bottom - 4),
        height,
        depth,
        phase: randRange(0, Math.PI * 2),
        swaySpeed: randRange(0.95, 1.65),
        swayAmp: randRange(3.5, 6.8),
        nudgeVel: 0,
        nudgeOffset: 0,
        leafStep: Math.max(5, Math.round(7 * depthScale(depth))),
        leafLen: Math.max(4, Math.round(6.5 * depthScale(depth))),
        palette: stemPalettes[i % stemPalettes.length]
      });
    }

    kelpRibbons = [];
    const kelpCount = clamp(Math.floor(innerWidth / 48), 4, 8);
    const kelpPalettes = [
      { dark: hexToUint32("#164a38"), mid: hexToUint32("#268060"), light: hexToUint32("#65d4ab"), pod: hexToUint32("#9cf5d2") },
      { dark: hexToUint32("#2d4a1e"), mid: hexToUint32("#4d7d33"), light: hexToUint32("#8ec969"), pod: hexToUint32("#c5f29b") }
    ];
    for (let i = 0; i < kelpCount; i++) {
      const frac = (i + 0.35 + randRange(-0.12, 0.12)) / kelpCount;
      const baseX = clamp(Math.round(innerLeft + frac * innerWidth), jar.left + 10, jar.right - 10);
      const depth = i % 2 === 0 ? randRange(0.18, 0.42) : randRange(0.62, 0.86);
      const height = clamp(Math.round(randRange(maxPlantHeight * 0.58, maxPlantHeight * 0.95)), 28, maxPlantHeight);
      kelpRibbons.push({
        baseX,
        baseY: clamp(floorY + Math.round((depth - 0.5) * 3.5), jar.sandTop - 1, jar.bottom - 4),
        height,
        depth,
        width: clamp(3.4 * depthScale(depth), 2.2, 5.2),
        twistFreq: randRange(0.16, 0.24),
        phase: randRange(0, Math.PI * 2),
        swaySpeed: randRange(0.9, 1.45),
        swayAmp: randRange(4.5, 8.5),
        nudgeVel: 0,
        nudgeOffset: 0,
        palette: kelpPalettes[i % kelpPalettes.length]
      });
    }

    fernFronds = [];
    const fernCount = clamp(Math.floor(innerWidth / 55), 3, 7);
    for (let i = 0; i < fernCount; i++) {
      const frac = (i + 0.65) / fernCount;
      const baseX = clamp(Math.round(innerLeft + frac * innerWidth + randRange(-10, 10)), jar.left + 12, jar.right - 12);
      const depth = randRange(0.30, 0.85);
      const frondCount = Math.floor(randRange(5, 8));
      const fronds = [];
      for (let f = 0; f < frondCount; f++) {
        const t = frondCount === 1 ? 0 : (f / (frondCount - 1)) * 2 - 1;
        fronds.push({
          leanAngle: t * randRange(0.55, 0.85),
          length: clamp(Math.round(randRange(16, 30) * depthScale(depth)), 12, Math.floor(maxPlantHeight * 0.55)),
          phase: randRange(0, Math.PI * 2)
        });
      }
      fernFronds.push({
        baseX,
        baseY: clamp(floorY + Math.round((depth - 0.5) * 3.5), jar.sandTop - 1, jar.bottom - 4),
        depth,
        fronds,
        nudgeVel: 0,
        nudgeOffset: 0,
        dark: hexToUint32("#103b25"),
        mid: hexToUint32("#1f6e43"),
        light: hexToUint32("#4ec47d")
      });
    }

    mossCushions = [];
    const mossCount = clamp(Math.floor(innerWidth / 42), 4, 10);
    for (let i = 0; i < mossCount; i++) {
      const mDepth = randRange(0.24, 0.92);
      const pScale = depthScale(mDepth);
      const rx = clamp(Math.round(randRange(4.5, 8.5) * pScale), 4, 12);
      const ry = clamp(Math.round(rx * randRange(0.58, 0.78)), 3, 9);
      mossCushions.push({
        x: randRange(innerLeft + 4, innerRight - 4),
        y: clamp(floorY + Math.round((mDepth - 0.5) * 3.2), jar.sandTop - 1, jar.bottom - 3),
        rx,
        ry,
        depth: mDepth,
        dark: hexToUint32("#0c381d"),
        mid: hexToUint32("#1c6b38"),
        light: hexToUint32("#45b869")
      });
    }

    floatingPads = [];
    const padCount = clamp(Math.floor(innerWidth / 26), 6, 15);
    for (let i = 0; i < padCount; i++) {
      const pDepth = randRange(0.20, 0.88);
      floatingPads.push({
        x: randRange(jar.left + 10, jar.right - 10),
        rx: clamp(randRange(2.5, 4.8) * depthScale(pDepth), 2.0, 6.5),
        rootLen: clamp(Math.round(randRange(6, 16) * depthScale(pDepth)), 5, 20),
        depth: pDepth,
        phase: randRange(0, Math.PI * 2),
        driftSpeed: randRange(0.15, 0.35),
        dark: hexToUint32("#17592c"),
        light: hexToUint32("#4fd172"),
        rootCol: hexToUint32("#528a68")
      });
    }

    sandPebbles = [];
    const pebbleColors = [hexToUint32("#c4aa79"), hexToUint32("#786340"), hexToUint32("#9c8357")];
    const pebbleCount = Math.floor(innerWidth / 4.2);
    for (let i = 0; i < pebbleCount; i++) {
      const pDepth = randRange(0.15, 0.95);
      const pScale = depthScale(pDepth);
      sandPebbles.push({
        x: randRange(jar.left + 6, jar.right - 6),
        y: randRange(floorY + 1.5, jar.bottom - 2),
        rx: randRange(1.6, 3.4) * pScale,
        ry: randRange(1.0, 2.0) * pScale,
        depth: pDepth,
        color: pDepth > 0.6 ? pebbleColors[0] : pDepth > 0.35 ? pebbleColors[2] : pebbleColors[1]
      });
    }
    sandPebbles.sort((a, b) => a.depth - b.depth);

    motes = [];
    const moteCount = clamp(Math.floor(innerWidth / 4.5), 30, 80);
    for (let i = 0; i < moteCount; i++) {
      const mDepth = randRange(0.12, 0.95);
      motes.push({
        x: randRange(jar.left + 6, jar.right - 6),
        y: randRange(jar.waterLine + 4, floorY - 4),
        vx: randRange(-0.08, 0.08) * depthScale(mDepth),
        vy: randRange(-0.06, 0.04),
        depth: mDepth,
        phase: randRange(0, Math.PI * 2)
      });
    }

    bubbles = [];
    sandGrains = [];
    splashDroplets = [];
    surfaceRipples = [];
    foodPellets = [];
    heartParticles = [];

    for (let i = 0; i < 18; i++) {
      const bDepth = randRange(0.15, 0.95);
      spawnBubble(
        randRange(jar.left + 12, jar.right - 12),
        randRange(jar.waterLine + 6, floorY - 4),
        randRange(1.2, 2.8) * depthScale(bDepth),
        bDepth
      );
    }

    rebuildLayerCaches();

    fish.x = clamp(fish.x, jar.left + 22, jar.right - 22);
    fish.y = clamp(fish.y, jar.waterLine + 14, floorY - 14);
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

    backKelpIndices = [];
    midKelpIndices = [];
    frontKelpIndices = [];
    for (let i = 0; i < kelpRibbons.length; i++) {
      const d = kelpRibbons[i].depth;
      if (d < 0.45) backKelpIndices.push(i);
      else if (d < 0.72) midKelpIndices.push(i);
      else frontKelpIndices.push(i);
    }

    backFernIndices = [];
    midFernIndices = [];
    frontFernIndices = [];
    for (let i = 0; i < fernFronds.length; i++) {
      const d = fernFronds[i].depth;
      if (d < 0.45) backFernIndices.push(i);
      else if (d < 0.72) midFernIndices.push(i);
      else frontFernIndices.push(i);
    }
  }

  function spawnBubble(x, y, radius, depth) {
    if (bubbles.length >= 110) bubbles.shift();
    bubbles.push({
      x,
      y,
      radius,
      depth: clamp(depth, 0.1, 0.98),
      vy: randRange(0.22, 0.46) * (0.75 + radius * 0.2),
      wobblePhase: randRange(0, Math.PI * 2),
      wobbleSpeed: randRange(2.4, 4.4)
    });
  }

  function spawnSandPlume(x, y, dirX, depth, count) {
    for (let i = 0; i < count; i++) {
      if (sandGrains.length >= 240) sandGrains.shift();
      const spread = randRange(-0.45, 0.45);
      const ejectSpeed = randRange(0.45, 1.45);
      sandGrains.push({
        x: x + randRange(-2.5, 2.5),
        y: y - randRange(0.3, 1.8),
        vx: -dirX * ejectSpeed * randRange(0.45, 1.15) + spread,
        vy: -randRange(0.55, 1.55),
        settled: false,
        settleTimer: 0,
        bounceCount: 0,
        life: randRange(2.6, 4.2),
        maxLife: 4.2,
        depth: clamp(depth + randRange(-0.12, 0.12), 0.15, 0.96),
        bright: Math.random() > 0.42
      });
    }
  }

  function spawnWaterSplash(x, vxInherit, intensity) {
    const count = Math.round(8 + intensity * 12);
    for (let i = 0; i < count; i++) {
      if (splashDroplets.length >= 90) splashDroplets.shift();
      splashDroplets.push({
        x: x + randRange(-3.5, 3.5),
        y: jar.waterLine - randRange(0.5, 2.5),
        vx: vxInherit * randRange(0.2, 0.7) + randRange(-0.75, 0.75),
        vy: -randRange(0.85, 2.15) * intensity,
        life: randRange(0.45, 0.95),
        bright: Math.random() > 0.35
      });
    }
    spawnSurfaceRipple(x, clamp(0.65 * intensity, 0.3, 1.1));
    for (let i = 0; i < 6; i++) {
      spawnBubble(
        x + randRange(-5, 5),
        jar.waterLine + randRange(2, 7),
        randRange(1.0, 2.2),
        fish.depth
      );
    }
  }

  function spawnSurfaceRipple(x, strength) {
    if (surfaceRipples.length >= 16) surfaceRipples.shift();
    surfaceRipples.push({
      x: clamp(x, jar.left + 3, jar.right - 3),
      radius: 1.2,
      maxRadius: clamp(18 + strength * 24, 16, 48),
      alpha: clamp(0.45 + strength * 0.45, 0.35, 0.95)
    });
  }

  function spawnFood(x, y) {
    const grainCount = Math.floor(randRange(3, 5));
    for (let i = 0; i < grainCount; i++) {
      if (foodPellets.length >= 32) foodPellets.shift();
      const fDepth = randRange(0.26, 0.80);
      const offsetX = i === 0 ? 0 : randRange(-7.5, 7.5);
      const offsetY = i === 0 ? 0 : randRange(-4.5, 2.5);
      foodPellets.push({
        x: clamp(x + offsetX, jar.left + 8, jar.right - 8),
        y: clamp(y + offsetY, jar.top + 2, jar.waterLine - 1),
        vx: randRange(-0.14, 0.14),
        vy: randRange(0.24, 0.46),
        inWater: false,
        depth: fDepth,
        phase: randRange(0, Math.PI * 2),
        settledTimer: 0
      });
    }
  }

  function spawnHeartParticles(x, y, depth) {
    const count = 5;
    for (let i = 0; i < count; i++) {
      if (heartParticles.length >= 30) heartParticles.shift();
      heartParticles.push({
        x: x + randRange(-4.5, 4.5),
        y: y - randRange(3.0, 7.0),
        vx: randRange(-0.12, 0.12),
        vy: -randRange(0.18, 0.32),
        phase: randRange(0, Math.PI * 2),
        life: randRange(1.4, 2.2),
        maxLife: 2.2,
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

  function triggerWaterJump(preferredDir) {
    const innerLeft = jar.left + 26;
    const innerRight = jar.right - 26;
    if (innerRight - innerLeft < 40) return false;

    let dir = preferredDir;
    if (!dir) {
      if (fish.x < jar.centerX - 18) dir = 1;
      else if (fish.x > jar.centerX + 18) dir = -1;
      else dir = Math.cos(fish.angle) >= 0 ? 1 : -1;
    }

    if (dir > 0 && fish.x > innerRight - 36) dir = -1;
    if (dir < 0 && fish.x < innerLeft + 36) dir = 1;

    fish.state = FISH_STATE.JUMP_PREP;
    fish.orbitTarget = null;
    fish.stateTimer = 1.4;
    fish.jumpCooldown = randRange(7.5, 13.0);
    fish.targetDepth = clamp(fish.depth, 0.35, 0.75);

    const launchAngle = dir > 0 ? -Math.PI * 0.33 : -Math.PI * 0.67;
    fish.targetAngle = launchAngle;
    return true;
  }

  function triggerSandDash(preferredDir) {
    const innerLeft = jar.left + 20;
    const innerRight = jar.right - 20;
    if (innerRight - innerLeft < 45) return false;

    let dir = preferredDir;
    if (!dir) {
      if (fish.x < jar.centerX) dir = 1;
      else dir = -1;
    }
    if (dir > 0 && fish.x > innerRight - 30) dir = -1;
    if (dir < 0 && fish.x < innerLeft + 30) dir = 1;

    const dashSpan = clamp((innerRight - innerLeft) * randRange(0.45, 0.72), 38, 140);
    fish.sandDashDir = dir;
    fish.sandDashEndX = clamp(fish.x + dir * dashSpan, innerLeft, innerRight);
    fish.state = FISH_STATE.SAND_DASH;
    fish.orbitTarget = null;
    fish.stateTimer = 3.4;
    fish.sandDashCooldown = randRange(7.5, 13.5);
    fish.targetDepth = randRange(0.42, 0.78);
    return true;
  }

  function transitionFishState(newState) {
    const innerLeft = jar.left + 18;
    const innerRight = jar.right - 18;
    const topBound = jar.waterLine + 9;
    const bottomBound = jar.sandTop - 8;

    fish.state = newState;

    if (newState === FISH_STATE.FORAGING) {
      fish.orbitTarget = null;
      fish.stateTimer = 8.0;
    } else if (newState === FISH_STATE.ORBITING) {
      const candidates = grassStalks.filter((s) => s.height >= 20);
      const stalk =
        candidates.length > 0
          ? candidates[Math.floor(Math.random() * candidates.length)]
          : grassStalks[Math.floor(Math.random() * grassStalks.length)];

      if (stalk) {
        const centerY = clamp(
          stalk.baseY - stalk.height * randRange(0.35, 0.72),
          topBound + 4,
          bottomBound - 4
        );
        fish.orbitTarget = { x: stalk.baseX, y: centerY, stalkRef: stalk };
        fish.orbitRadius = randRange(14.0, 24.0);
        fish.orbitAngle = Math.atan2(fish.y - centerY, fish.x - stalk.baseX);
        fish.stateTimer = randRange(3.2, 5.8);
        fish.targetDepth = clamp(stalk.depth + randRange(-0.22, 0.22), 0.16, 0.90);
      } else {
        transitionFishState(FISH_STATE.CRUISING);
      }
    } else if (newState === FISH_STATE.RESTING) {
      fish.orbitTarget = null;
      fish.stateTimer = randRange(2.4, 4.4);
      const restX = clamp(
        fish.x + randRange(-26, 26),
        innerLeft + 6,
        innerRight - 6
      );
      const restY = clamp(
        jar.sandTop - randRange(10, 22),
        topBound + 8,
        bottomBound - 3
      );
      fish.restPos.x = restX;
      fish.restPos.y = restY;
      fish.targetDepth = randRange(0.35, 0.75);
    } else if (newState === FISH_STATE.ALERT) {
      fish.orbitTarget = null;
      fish.stateTimer = randRange(1.0, 1.6);
    } else {
      fish.orbitTarget = null;
      fish.stateTimer = randRange(2.0, 4.0);
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

    if (fish.energy < 0.30) {
      transitionFishState(FISH_STATE.RESTING);
      return;
    }

    const roll = Math.random();
    if (roll < 0.18 && fish.jumpCooldown <= 0 && fish.energy > 0.48) {
      if (triggerWaterJump(0)) return;
    }
    if (roll >= 0.18 && roll < 0.38 && fish.sandDashCooldown <= 0 && fish.energy > 0.45) {
      if (triggerSandDash(0)) return;
    }

    if (roll < 0.68) {
      transitionFishState(FISH_STATE.CRUISING);
    } else if (roll < 0.88 && grassStalks.length > 0) {
      transitionFishState(FISH_STATE.ORBITING);
    } else {
      transitionFishState(FISH_STATE.RESTING);
    }
  }

  function updateFish(dt) {
    const innerLeft = jar.left + 16;
    const innerRight = jar.right - 16;
    const topBound = jar.waterLine + 7.5;
    const bottomBound = jar.sandTop - 6.5;

    if (syncReady && currentUser && !isLeader && remoteFish.hasSnapshot) {
      const wasAirborne = fish.state === FISH_STATE.AIRBORNE;
      const blend = 1 - Math.exp(-14 * dt);

      fish.x = lerp(fish.x, remoteFish.x, blend);
      fish.y = lerp(fish.y, remoteFish.y, blend);
      fish.vx = lerp(fish.vx, remoteFish.vx, blend);
      fish.vy = lerp(fish.vy, remoteFish.vy, blend);
      fish.angle += angleDiff(remoteFish.angle, fish.angle) * blend;
      fish.targetAngle = remoteFish.targetAngle;
      fish.pitchAngle = lerp(fish.pitchAngle, remoteFish.pitchAngle, blend);
      fish.speed = lerp(fish.speed, remoteFish.speed, blend);
      fish.state = remoteFish.state;
      fish.depth = lerp(fish.depth, remoteFish.depth, blend * 0.75);
      fish.targetDepth = remoteFish.targetDepth;
      fish.sandDashDir = remoteFish.sandDashDir;
      fish.sandDashEndX = remoteFish.sandDashEndX;

      if (!wasAirborne && fish.state === FISH_STATE.AIRBORNE) {
        spawnWaterSplash(fish.x, fish.vx, 1.0);
      } else if (wasAirborne && fish.state !== FISH_STATE.AIRBORNE && fish.y >= jar.waterLine) {
        spawnWaterSplash(fish.x, fish.vx, 0.9);
      }

      if (fish.state === FISH_STATE.SAND_DASH && Math.abs(fish.y - (jar.sandTop - 2.6 * depthScale(fish.depth))) < 4.0) {
        fish.sandTrailTimer += dt;
        if (fish.sandTrailTimer >= 0.035) {
          fish.sandTrailTimer = 0;
          const tailX = fish.x - fish.sandDashDir * 6.5 * depthScale(fish.depth);
          spawnSandPlume(tailX, jar.sandTop - 0.4, fish.sandDashDir, fish.depth, 4);
        }
      }

      const swimActivity = Math.max(0.35, fish.speed / Math.max(0.1, fish.baseSpeed));
      fish.tailPhase += dt * (11.0 * swimActivity + fish.speed * 14);
      fish.bodyWavePhase += dt * (9.5 * swimActivity + fish.speed * 11);
      fish.finPhase += dt * (6.8 * swimActivity);
      fish.gillPhase += dt * 5.8;

      if (performance.now() - lastRemoteUpdate > 4000) {
        isLeader = true;
        leaderId = clientId;
      }
      return;
    }

    if (fish.turnCooldown > 0) fish.turnCooldown -= dt;
    if (fish.eatFlutterTimer > 0) fish.eatFlutterTimer -= dt;
    if (fish.jumpCooldown > 0) fish.jumpCooldown -= dt;
    if (fish.sandDashCooldown > 0) fish.sandDashCooldown -= dt;
    fish.stateTimer -= dt;

    if (fish.state === FISH_STATE.AIRBORNE) {
      const airGravity = 0.058 * (fish.baseSpeed / 0.48);
      fish.vy += airGravity * stepScale;
      fish.x += fish.vx * stepScale;
      fish.y += fish.vy * stepScale;

      if (fish.x < innerLeft + 4) {
        fish.x = innerLeft + 4;
        fish.vx = Math.abs(fish.vx) * 0.7;
      } else if (fish.x > innerRight - 4) {
        fish.x = innerRight - 4;
        fish.vx = -Math.abs(fish.vx) * 0.7;
      }

      fish.angle = Math.atan2(fish.vy, fish.vx);
      fish.pitchAngle = clamp(fish.vy * 0.95, -0.95, 0.95);
      fish.tailPhase += dt * 16.0;
      fish.bodyWavePhase += dt * 12.0;
      fish.finPhase += dt * 10.0;

      if (fish.vy > 0 && fish.y >= jar.waterLine + 1.5) {
        spawnWaterSplash(fish.x, fish.vx, 0.95);
        fish.vy *= 0.58;
        fish.vx *= 0.82;
        fish.targetAngle = Math.atan2(fish.vy, fish.vx);
        transitionFishState(FISH_STATE.CRUISING);
        fish.stateTimer = 1.6;
      }
      return;
    }

    if (fish.state === FISH_STATE.JUMP_PREP) {
      fish.energy = clamp(fish.energy - dt * 0.08, 0, 1);
      const launchSpeed = fish.baseSpeed * 2.55;
      fish.speed = lerp(fish.speed, launchSpeed, dt * 6.5);
      fish.tailPhase += dt * 28.0;
      fish.bodyWavePhase += dt * 22.0;
      fish.finPhase += dt * 15.0;

      const diff = angleDiff(fish.targetAngle, fish.angle);
      fish.angle += clamp(diff, -6.5 * dt, 6.5 * dt);

      fish.vx = Math.cos(fish.angle) * fish.speed;
      fish.vy = Math.sin(fish.angle) * fish.speed * 1.15;

      fish.x = clamp(fish.x + fish.vx * stepScale, innerLeft, innerRight);
      fish.y += fish.vy * stepScale;
      fish.pitchAngle = lerp(fish.pitchAngle, clamp(fish.vy * 0.85, -0.9, 0.9), dt * 8.0);

      if (fish.y <= jar.waterLine) {
        fish.state = FISH_STATE.AIRBORNE;
        const headroom = Math.max(18, jar.waterLine - (jar.top + 4));
        const desiredApexVy = -Math.sqrt(2 * 0.058 * (fish.baseSpeed / 0.48) * headroom * 0.78);
        fish.vy = Math.min(fish.vy * 1.18, desiredApexVy);
        fish.vx = (fish.vx >= 0 ? 1 : -1) * clamp(Math.abs(fish.vx) * 1.05, fish.baseSpeed * 1.35, fish.baseSpeed * 2.2);
        spawnWaterSplash(fish.x, fish.vx, 1.05);
      } else if (fish.stateTimer <= 0) {
        transitionFishState(FISH_STATE.CRUISING);
      }
      return;
    }

    if (fish.state === FISH_STATE.SAND_DASH) {
      fish.energy = clamp(fish.energy - dt * 0.075, 0, 1);
      const skimY = jar.sandTop - 2.6 * depthScale(fish.depth);
      const distToEnd = (fish.sandDashEndX - fish.x) * fish.sandDashDir;

      const dyToSand = skimY - fish.y;
      const isOnSand = Math.abs(dyToSand) < 3.5;

      const dashSpeed = isOnSand ? fish.baseSpeed * 2.35 : fish.baseSpeed * 1.65;
      fish.speed = lerp(fish.speed, dashSpeed, dt * 6.0);
      fish.tailPhase += dt * 30.0;
      fish.bodyWavePhase += dt * 24.0;
      fish.finPhase += dt * 16.0;
      fish.depth = lerp(fish.depth, fish.targetDepth, dt * 3.0);

      const desiredVx = fish.sandDashDir * fish.speed;
      const desiredVy = clamp(dyToSand * 0.14, -fish.speed * 0.75, fish.speed * 0.75);
      fish.vx = lerp(fish.vx, desiredVx, dt * 7.5);
      fish.vy = lerp(fish.vy, desiredVy, dt * 7.5);

      fish.angle = Math.atan2(fish.vy, fish.vx);
      fish.pitchAngle = lerp(fish.pitchAngle, clamp(fish.vy * 0.65, -0.5, 0.5), dt * 8.0);

      fish.x = clamp(fish.x + fish.vx * stepScale, innerLeft, innerRight);
      fish.y = clamp(fish.y + fish.vy * stepScale, topBound, skimY + 0.4);

      if (isOnSand) {
        fish.sandTrailTimer += dt;
        if (fish.sandTrailTimer >= 0.025) {
          fish.sandTrailTimer = 0;
          const tailX = fish.x - fish.sandDashDir * 6.5 * depthScale(fish.depth);
          spawnSandPlume(tailX, jar.sandTop - 0.4, fish.sandDashDir, fish.depth, 5);
          if (Math.random() < 0.45) {
            spawnBubble(tailX, jar.sandTop - 1.5, randRange(0.8, 1.5), fish.depth);
          }
        }
      }

      if (distToEnd <= 2.0 || fish.stateTimer <= 0 || fish.x <= innerLeft + 1 || fish.x >= innerRight - 1) {
        fish.targetAngle = fish.sandDashDir > 0 ? -0.38 : Math.PI + 0.38;
        transitionFishState(FISH_STATE.CRUISING);
        fish.stateTimer = 1.8;
      }
      return;
    }

    if (fish.state !== FISH_STATE.FORAGING && fish.state !== FISH_STATE.ALERT) {
      const food = findNearestFood();
      if (food) {
        fish.targetFood = food;
        transitionFishState(FISH_STATE.FORAGING);
      }
    }

    if (fish.state === FISH_STATE.RESTING) {
      fish.energy = clamp(fish.energy + dt * 0.15, 0, 1);
    } else if (fish.state === FISH_STATE.ALERT) {
      fish.energy = clamp(fish.energy - dt * 0.11, 0, 1);
    } else if (fish.state === FISH_STATE.FORAGING) {
      fish.energy = clamp(fish.energy - dt * 0.04, 0, 1);
    } else {
      fish.energy = clamp(fish.energy - dt * 0.03, 0, 1);
    }

    const glideCycle = 0.86 + 0.18 * Math.sin(elapsed * 2.4 + fish.tailPhase * 0.08);
    let desiredSpeed = fish.baseSpeed * glideCycle;
    let tailRate = 10.5;
    let finRate = 6.8;

    if (fish.state === FISH_STATE.FORAGING) {
      desiredSpeed = fish.baseSpeed * 1.52;
      tailRate = 16.5;
      finRate = 10.5;
    } else if (fish.state === FISH_STATE.ALERT) {
      desiredSpeed = fish.baseSpeed * 1.95;
      tailRate = 23.0;
      finRate = 13.0;
    } else if (fish.state === FISH_STATE.RESTING) {
      desiredSpeed = fish.baseSpeed * 0.22;
      tailRate = 4.6;
      finRate = 4.2;
    } else if (fish.state === FISH_STATE.ORBITING) {
      desiredSpeed = fish.baseSpeed * 0.90;
      tailRate = 9.2;
      finRate = 6.2;
    }

    if (fish.eatFlutterTimer > 0) {
      tailRate = 24.0;
      finRate = 15.0;
    }

    fish.speed = lerp(fish.speed, desiredSpeed, dt * 4.5);
    fish.tailPhase += dt * (tailRate + fish.speed * 14);
    fish.bodyWavePhase += dt * (tailRate * 0.85 + fish.speed * 11);
    fish.finPhase += dt * finRate;
    fish.gillPhase += dt * (fish.state === FISH_STATE.ALERT ? 11.5 : 5.8);
    fish.depth = lerp(fish.depth, fish.targetDepth, dt * 1.9);

    if (fish.state === FISH_STATE.FORAGING) {
      if (!fish.targetFood || foodPellets.indexOf(fish.targetFood) === -1) {
        fish.targetFood = findNearestFood();
      }

      if (fish.targetFood && fish.targetFood.inWater) {
        const f = fish.targetFood;
        fish.targetDepth = lerp(fish.targetDepth, f.depth, dt * 3.8);
        const dx = f.x - fish.x;
        const dy = f.y - fish.y;
        const dist = Math.hypot(dx, dy);

        if (dist > 0.3) {
          fish.targetAngle = Math.atan2(dy, dx);
        }

        if (dist < 6.5 && Math.abs(fish.depth - f.depth) < 0.28) {
          const idx = foodPellets.indexOf(f);
          if (idx !== -1) foodPellets.splice(idx, 1);
          fish.targetFood = null;
          fish.energy = clamp(fish.energy + 0.24, 0, 1);
          fish.eatFlutterTimer = 0.75;
          spawnHeartParticles(
            fish.x + cylindricalShift(fish.x, fish.depth),
            fish.y - 6.0 * depthScale(fish.depth),
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

      const angularVel = (fish.speed / Math.max(12.0, fish.orbitRadius)) * 1.15;
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
      if (Math.hypot(dx, dy) > 0.5) {
        fish.targetAngle = Math.atan2(dy, dx);
      }
    } else if (fish.state === FISH_STATE.RESTING && fish.stateTimer > 0) {
      const hoverX = fish.restPos.x + Math.sin(elapsed * 1.1) * 3.2;
      const hoverY = fish.restPos.y + Math.cos(elapsed * 1.5) * 1.6;
      const dx = hoverX - fish.x;
      const dy = hoverY - fish.y;
      if (Math.hypot(dx, dy) > 1.6) {
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
    const margin = 22.0;

    if (fish.x < innerLeft + margin) {
      avoidX += ((innerLeft + margin - fish.x) / margin) * 1.7;
    }
    if (fish.x > innerRight - margin) {
      avoidX -= ((fish.x - (innerRight - margin)) / margin) * 1.7;
    }
    if (fish.y < topBound + 11.0) {
      avoidY += ((topBound + 11.0 - fish.y) / 11.0) * 1.5;
    }
    if (fish.y > bottomBound - 11.0) {
      avoidY -= ((fish.y - (bottomBound - 11.0)) / 11.0) * 1.5;
    }

    for (let i = 0; i < rocks.length; i++) {
      const r = rocks[i];
      if (Math.abs(r.depth - fish.depth) > 0.35) continue;
      const centerX = r.x + r.w * 0.5;
      const centerY = r.y + r.h * 0.5;
      const dx = fish.x - centerX;
      const dy = fish.y - centerY;
      const dist = Math.hypot(dx, dy);
      const minDist = Math.max(r.w * 0.65, 18.0);

      if (dist > 0.01 && dist < minDist) {
        const push = ((minDist - dist) / minDist) * 1.35;
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
        ? 5.4
        : fish.state === FISH_STATE.FORAGING
        ? 4.6
        : fish.state === FISH_STATE.RESTING
        ? 2.1
        : 3.3;
    const appliedTurn = clamp(diff, -turnRate * dt, turnRate * dt);
    fish.angle += appliedTurn;
    fish.angle = Math.atan2(Math.sin(fish.angle), Math.cos(fish.angle));

    fish.rollWobble = lerp(fish.rollWobble, clamp(appliedTurn * 18, -0.32, 0.32), dt * 6.0);

    fish.vx = Math.cos(fish.angle) * fish.speed;
    fish.vy = Math.sin(fish.angle) * fish.speed * 0.78;
    fish.pitchAngle = lerp(fish.pitchAngle, clamp(Math.atan2(fish.vy, Math.abs(fish.vx) + 0.15) * 0.55, -0.45, 0.45), dt * 6.0);

    fish.x = clamp(fish.x + fish.vx * stepScale, innerLeft, innerRight);
    fish.y = clamp(fish.y + fish.vy * stepScale, topBound, bottomBound);

    if (Math.random() < 0.35) {
      for (let i = 0; i < grassStalks.length; i++) {
        const s = grassStalks[i];
        if (Math.abs(s.depth - fish.depth) < 0.22 && Math.abs(s.baseX - fish.x) < 7 && fish.y > s.baseY - s.height) {
          s.nudgeVel += fish.vx * 0.28;
        }
      }
    }

    if (
      (fish.x <= innerLeft + 0.8 || fish.x >= innerRight - 0.8) &&
      fish.turnCooldown <= 0
    ) {
      const centerY = (topBound + bottomBound) * 0.5;
      fish.targetAngle = Math.atan2(centerY - fish.y, jar.centerX - fish.x);
      fish.turnCooldown = 0.6;
    }

    if (syncReady && currentUser && isLeader) {
      const nowMs = Date.now();
      const forceSend = pendingEvents.length > 0 || nowMs - lastHeartbeat > 1200;
      if (forceSend) lastHeartbeat = nowMs;
      pushGlobalState(forceSend);
    }
  }

  function updateEnvironmentAndParticles(dt) {
    if (pointer.active && pointer.inWater) {
      const moveSpeed = Math.hypot(pointer.x - pointer.prevX, pointer.y - pointer.prevY);
      if (moveSpeed > 0.3) {
        for (let i = 0; i < grassStalks.length; i++) {
          const s = grassStalks[i];
          const topY = s.baseY - s.height;
          if (pointer.y >= topY - 6 && pointer.y <= s.baseY + 3) {
            const dx = s.baseX - pointer.x;
            if (Math.abs(dx) < 16) {
              const push = ((16 - Math.abs(dx)) / 16) * clamp(moveSpeed * 0.16, 0.25, 1.8);
              s.nudgeVel += (dx >= 0 ? 1 : -1) * push;
            }
          }
        }
        for (let i = 0; i < stemPlants.length; i++) {
          const sp = stemPlants[i];
          const topY = sp.baseY - sp.height;
          if (pointer.y >= topY - 6 && pointer.y <= sp.baseY + 3) {
            const dx = sp.baseX - pointer.x;
            if (Math.abs(dx) < 18) {
              const push = ((18 - Math.abs(dx)) / 18) * clamp(moveSpeed * 0.16, 0.25, 1.8);
              sp.nudgeVel += (dx >= 0 ? 1 : -1) * push;
            }
          }
        }
        for (let i = 0; i < kelpRibbons.length; i++) {
          const k = kelpRibbons[i];
          if (pointer.y >= k.baseY - k.height - 6 && pointer.y <= k.baseY + 3) {
            const dx = k.baseX - pointer.x;
            if (Math.abs(dx) < 18) {
              const push = ((18 - Math.abs(dx)) / 18) * clamp(moveSpeed * 0.16, 0.25, 1.8);
              k.nudgeVel += (dx >= 0 ? 1 : -1) * push;
            }
          }
        }
        for (let i = 0; i < fernFronds.length; i++) {
          const fn = fernFronds[i];
          if (pointer.y >= fn.baseY - 32 && pointer.y <= fn.baseY + 3) {
            const dx = fn.baseX - pointer.x;
            if (Math.abs(dx) < 18) {
              const push = ((18 - Math.abs(dx)) / 18) * clamp(moveSpeed * 0.16, 0.25, 1.8);
              fn.nudgeVel += (dx >= 0 ? 1 : -1) * push;
            }
          }
        }
        for (let i = 0; i < motes.length; i++) {
          const m = motes[i];
          const dx = m.x - pointer.x;
          const dy = m.y - pointer.y;
          const dist = Math.hypot(dx, dy);
          if (dist > 0.1 && dist < 20) {
            const force = ((20 - dist) / 20) * 0.05;
            m.vx = clamp(m.vx + (dx / dist) * force, -0.32, 0.32);
            m.vy = clamp(m.vy + (dy / dist) * force, -0.32, 0.32);
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
    for (let i = 0; i < kelpRibbons.length; i++) {
      const k = kelpRibbons[i];
      if (Math.abs(k.nudgeOffset) > 0.001 || Math.abs(k.nudgeVel) > 0.001) {
        k.nudgeVel += -k.nudgeOffset * 10 * dt;
        k.nudgeVel *= Math.exp(-4.5 * dt);
        k.nudgeOffset += k.nudgeVel * dt;
      }
    }
    for (let i = 0; i < fernFronds.length; i++) {
      const fn = fernFronds[i];
      if (Math.abs(fn.nudgeOffset) > 0.001 || Math.abs(fn.nudgeVel) > 0.001) {
        fn.nudgeVel += -fn.nudgeOffset * 13 * dt;
        fn.nudgeVel *= Math.exp(-5.2 * dt);
        fn.nudgeOffset += fn.nudgeVel * dt;
      }
    }

    for (let i = 0; i < floatingPads.length; i++) {
      const pad = floatingPads[i];
      pad.x += Math.sin(elapsed * pad.driftSpeed + pad.phase) * 0.025 * stepScale;
      pad.x = clamp(pad.x, jar.left + 8, jar.right - 8);
    }

    for (let i = 0; i < rocks.length; i++) {
      if (rocks[i].glintTimer > 0) {
        rocks[i].glintTimer = Math.max(0, rocks[i].glintTimer - dt);
      }
    }

    for (let i = surfaceRipples.length - 1; i >= 0; i--) {
      const r = surfaceRipples[i];
      r.radius += 22 * dt;
      r.alpha -= 0.72 * dt;
      if (r.alpha <= 0.02 || r.radius >= r.maxRadius) {
        surfaceRipples.splice(i, 1);
      }
    }

    for (let i = sandGrains.length - 1; i >= 0; i--) {
      const g = sandGrains[i];
      const bedY = jar.sandTop + (g.depth - 0.5) * 3.2;

      if (!g.settled) {
        g.vy += 0.062 * stepScale;
        g.vx *= Math.exp(-2.4 * dt);
        g.x += g.vx * stepScale;
        g.y += g.vy * stepScale;
        g.x = clamp(g.x, jar.left + 4, jar.right - 4);

        if (g.y >= bedY && g.vy > 0) {
          g.y = bedY;
          if (g.bounceCount < 2 && Math.abs(g.vy) > 0.25) {
            g.vy = -g.vy * 0.34;
            g.vx *= 0.55;
            g.bounceCount++;
          } else {
            g.vx = 0;
            g.vy = 0;
            g.settled = true;
            g.settleTimer = randRange(1.4, 2.8);
          }
        }
      } else {
        g.settleTimer -= dt;
        if (g.settleTimer <= 0) {
          sandGrains.splice(i, 1);
        }
      }
    }

    for (let i = splashDroplets.length - 1; i >= 0; i--) {
      const d = splashDroplets[i];
      d.life -= dt;
      d.vy += 0.085 * stepScale;
      d.x += d.vx * stepScale;
      d.y += d.vy * stepScale;
      if (d.life <= 0 || (d.vy > 0 && d.y >= jar.waterLine + 1)) {
        splashDroplets.splice(i, 1);
      }
    }

    for (let i = foodPellets.length - 1; i >= 0; i--) {
      const f = foodPellets[i];
      f.phase += dt * 3.2;

      if (!f.inWater) {
        f.vy += 0.45 * dt;
        f.y += f.vy * stepScale;
        f.x += f.vx * stepScale;

        if (f.y >= jar.waterLine) {
          f.inWater = true;
          f.y = jar.waterLine + 0.5;
          f.vy = 0.095;
          spawnSurfaceRipple(f.x, 0.35);
          spawnBubble(f.x, jar.waterLine + 2.0, 1.1, f.depth);
        }
      } else {
        if (f.y < jar.sandTop - 2.0) {
          f.y += f.vy * stepScale;
          f.x += Math.sin(f.phase) * 0.08 * stepScale;
          f.x = clamp(f.x, jar.left + 6, jar.right - 6);
        } else {
          f.y = jar.sandTop - 1.5;
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
      h.x += (h.vx + Math.sin(h.phase) * 0.1) * stepScale;
      if (h.life <= 0 || h.y <= jar.waterLine + 2.0) {
        heartParticles.splice(i, 1);
      }
    }

    if (Math.random() < dt * 3.5 && rocks.length > 0) {
      const r = rocks[Math.floor(Math.random() * rocks.length)];
      const bDepth = clamp(r.depth + randRange(-0.15, 0.15), 0.12, 0.96);
      spawnBubble(
        r.x + randRange(3, r.w - 3),
        r.y + 1,
        randRange(1.1, 2.5) * depthScale(bDepth),
        bDepth
      );
    }

    for (let i = bubbles.length - 1; i >= 0; i--) {
      const b = bubbles[i];
      b.wobblePhase += b.wobbleSpeed * dt;
      b.y -= b.vy * stepScale;
      b.x += Math.sin(b.wobblePhase) * 0.14 * stepScale;
      b.x = clamp(b.x, jar.left + 5, jar.right - 5);

      if (b.y <= jar.waterLine + 1.0) {
        if (b.radius > 1.8 && Math.random() < 0.35) {
          spawnSurfaceRipple(b.x, 0.18);
        }
        bubbles.splice(i, 1);
      }
    }

    for (let i = 0; i < motes.length; i++) {
      const m = motes[i];
      m.phase += dt * 1.5;
      m.vx *= Math.exp(-0.8 * dt);
      m.vy *= Math.exp(-0.8 * dt);
      m.x += (m.vx + Math.cos(m.phase) * 0.05) * stepScale;
      m.y += (m.vy + Math.sin(m.phase * 0.7) * 0.04) * stepScale;

      if (m.x < jar.left + 5) m.x = jar.right - 5;
      if (m.x > jar.right - 5) m.x = jar.left + 5;
      if (m.y < jar.waterLine + 3) m.y = jar.sandTop - 3;
      if (m.y > jar.sandTop - 3) m.y = jar.waterLine + 3;
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
      const yWaveA = elapsed * 1.5 + y * 0.08;
      const yWaveB = -elapsed * 1.15 - y * 0.11;

      for (let x = jar.left + 1; x < jar.right; x++) {
        const cylNorm = clamp((x - jar.centerX) / jar.halfW, -1, 1);
        const cylShade = Math.sqrt(Math.max(0.15, 1 - cylNorm * cylNorm * 0.65));

        const causticA = Math.sin(x * 0.11 + yWaveA) * 0.5 + 0.5;
        const causticB = Math.cos(x * 0.085 + yWaveB) * 0.5 + 0.5;
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

    const cornerR = 8;
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
            ) < 0.9);
        const isBottom =
          y === jar.bottom ||
          (y > jar.bottom - cornerR &&
            (x <= jar.left + cornerR || x >= jar.right - cornerR) &&
            Math.abs(
              Math.hypot(
                x < jar.left + cornerR ? jar.left + cornerR - x : x - (jar.right - cornerR),
                y - (jar.bottom - cornerR)
              ) - cornerR
            ) < 0.9);
        const isLeft = x === jar.left && y >= jar.top + cornerR && y <= jar.bottom - cornerR;
        const isRight = x === jar.right && y >= jar.top + cornerR && y <= jar.bottom - cornerR;

        if (isTop || isBottom || isLeft || isRight) {
          const shimmer = 0.45 + 0.45 * Math.sin(x * 0.18 + y * 0.15 - elapsed * 1.2);
          const col = ditherMixUint(glassDeep, glassBright, shimmer, x, y);
          setPixel(x, y, col, shimmer > 0.78, 0.99);
        } else if ((x === jar.left + 1 || x === jar.left + 2) && y > jar.top + 5 && y < jar.bottom - 5) {
          const streak = 0.25 + 0.55 * Math.sin(y * 0.10 - elapsed * 0.9);
          if (ditherPass(streak, x, y)) {
            setPixel(x, y, ditherMixUint(glassDeep, glassBright, streak, x, y), false, 0.98);
          }
        }
      }
    }

    for (let x = jar.left + 1; x < jar.right; x++) {
      let waveOffset = Math.sin(elapsed * 2.0 + x * 0.12) * 0.75;
      let rippleBoost = 0;

      if (pointer.active && Math.abs(pointer.y - jar.waterLine) < 14) {
        const dx = Math.abs(x - pointer.x);
        if (dx < 20) {
          const falloff = (20 - dx) / 20;
          waveOffset += Math.sin(dx * 0.65 - elapsed * 8) * 0.9 * falloff;
          rippleBoost += 0.35 * falloff;
        }
      }

      for (let i = 0; i < surfaceRipples.length; i++) {
        const r = surfaceRipples[i];
        const distFromRing = Math.abs(Math.abs(x - r.x) - r.radius);
        if (distFromRing < 3.0) {
          const ringStrength = (1 - distFromRing / 3.0) * r.alpha;
          waveOffset -= ringStrength * 1.15;
          rippleBoost += ringStrength * 0.55;
        }
      }

      const wave = clamp(Math.sin(elapsed * 2.4 + x * 0.15) * 0.5 + 0.5 + rippleBoost, 0, 1);
      const yOffset = Math.round(waveOffset);
      const col = ditherMixUint(waterLight, glassBright, wave, x, jar.waterLine + yOffset);
      setPixel(x, jar.waterLine + yOffset, col, true, 0.96);
      if (ditherPass(wave * 0.65, x, jar.waterLine + yOffset + 1)) {
        setPixel(x, jar.waterLine + yOffset + 1, waterMid, false, 0.85);
      }
    }

    for (let i = 0; i < floatingPads.length; i++) {
      const pad = floatingPads[i];
      const pxCenter = pad.x + cylindricalShift(pad.x, pad.depth);
      const waveY = jar.waterLine + Math.round(Math.sin(elapsed * 2.0 + pad.x * 0.12) * 0.65);
      const rx = pad.rx;
      for (let dx = -Math.ceil(rx); dx <= Math.ceil(rx); dx++) {
        const gx = Math.round(pxCenter + dx);
        if (gx <= jar.left || gx >= jar.right) continue;
        const norm = Math.abs(dx) / Math.max(1, rx);
        if (norm <= 1.0) {
          const col = ditherMixUint(pad.dark, pad.light, 1.0 - norm * 0.65, gx, waveY);
          setPixel(gx, waveY, col, false, pad.depth);
          if (norm < 0.7) {
            setPixel(gx, waveY - 1, pad.light, false, pad.depth);
          }
        }
      }
      for (let ry = 1; ry <= pad.rootLen; ry++) {
        const sway = Math.sin(elapsed * 1.4 + pad.phase - ry * 0.25) * (ry * 0.12);
        const rxPos = Math.round(pxCenter + sway);
        const ryPos = waveY + ry;
        if (rxPos > jar.left && rxPos < jar.right && ryPos < jar.sandTop) {
          if (ditherPass(1.0 - (ry / (pad.rootLen + 2)) * 0.55, rxPos, ryPos)) {
            setPixel(rxPos, ryPos, pad.rootCol, false, pad.depth * 0.95);
          }
        }
      }
    }

    for (let y = jar.sandTop; y < jar.bottom; y++) {
      const sandDepth = (y - jar.sandTop) * invSandSpan;
      const approxDepth = clamp(0.15 + sandDepth * 0.8, 0.15, 0.95);
      for (let x = jar.left + 1; x < jar.right; x++) {
        if (!isEmptyCell(x, y) && y >= jar.bottom - cornerR) continue;

        const dune = Math.sin(x * 0.07 + sandDepth * 2.2) * 0.14;
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

    for (let i = 0; i < mossCushions.length; i++) {
      const m = mossCushions[i];
      const cx = m.x + cylindricalShift(m.x, m.depth);
      const minX = Math.floor(cx - m.rx);
      const maxX = Math.ceil(cx + m.rx);
      const minY = Math.floor(m.y - m.ry);
      const maxY = Math.ceil(m.y + 1);
      for (let py = minY; py <= maxY; py++) {
        for (let px = minX; px <= maxX; px++) {
          if (px <= jar.left || px >= jar.right || py <= jar.waterLine || py >= jar.bottom) continue;
          const nx = (px - cx) / m.rx;
          const ny = (py - m.y) / m.ry;
          if (nx * nx + ny * ny <= 1.0) {
            const fuzzy = 0.65 - ny * 0.45 - nx * 0.25;
            if (ditherPass(clamp(fuzzy + 0.25, 0.2, 0.98), px, py)) {
              const col = fuzzy > 0.55
                ? ditherMixUint(m.mid, m.light, (fuzzy - 0.55) * 2.2, px, py)
                : ditherMixUint(m.dark, m.mid, fuzzy * 1.8, px, py);
              setPixel(px, py, col, false, m.depth);
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
        Math.sin(elapsed * stalk.swaySpeed + stalk.phase - h * 0.09) *
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
        if (h >= stalk.height - 3) {
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
        Math.sin(elapsed * plant.swaySpeed + plant.phase - h * 0.085) *
          plant.swayAmp *
          bendCurve +
        plant.nudgeOffset * bendCurve;

      const cx = clamp(plant.baseX + parallaxX + sway, jar.left + 2, jar.right - 2);
      const gx = Math.round(cx);
      if (gx > jar.left && gx < jar.right) {
        setPixel(gx, y, plant.palette.stem, false, plant.depth);
      }

      if (h > 4 && h < plant.height - 2 && h % plant.leafStep === 0) {
        const side = ((h / plant.leafStep) & 1) === 0 ? 1 : -1;
        const len = Math.max(3, Math.round(plant.leafLen * (1.05 - heightRatio * 0.42)));
        for (let lx = 1; lx <= len; lx++) {
          const px = gx + side * lx;
          const py = y - Math.floor(lx * 0.42);
          if (px <= jar.left || px >= jar.right || py <= jar.waterLine || py >= jar.bottom) continue;
          const t = (lx / len) * depthAtten;
          const col = ditherMixUint(plant.palette.leafDark, plant.palette.leafLight, clamp(t, 0.1, 0.95), px, py);
          setPixel(px, py, col, lx === len && plant.depth > 0.58, plant.depth);
          if (lx > 1 && lx < len && py - 1 > jar.waterLine) {
            setPixel(px, py - 1, plant.palette.leafLight, false, plant.depth);
          }
        }
      }
    }
  }

  function drawKelpRibbon(kelp) {
    const parallaxX = cylindricalShift(kelp.baseX, kelp.depth);
    const invHeight = 1 / Math.max(1, kelp.height - 1);

    for (let h = 0; h < kelp.height; h++) {
      const y = kelp.baseY - h;
      if (y <= jar.waterLine + 1 || y >= jar.bottom) continue;

      const heightRatio = h * invHeight;
      const bendCurve = Math.pow(heightRatio, 1.25);
      const sway =
        Math.sin(elapsed * kelp.swaySpeed + kelp.phase - h * 0.07) *
          kelp.swayAmp *
          bendCurve +
        kelp.nudgeOffset * bendCurve;

      const twist = Math.sin(h * kelp.twistFreq + elapsed * 1.6 + kelp.phase);
      const ribbonHalfW = Math.max(0.8, kelp.width * (0.35 + 0.65 * Math.abs(twist)) * (1.0 - heightRatio * 0.35));
      const centerX = clamp(kelp.baseX + parallaxX + sway + twist * 1.4, jar.left + 3, jar.right - 3);

      const minX = Math.floor(centerX - ribbonHalfW);
      const maxX = Math.ceil(centerX + ribbonHalfW);
      for (let px = minX; px <= maxX; px++) {
        if (px <= jar.left || px >= jar.right) continue;
        const shade = clamp(0.45 + twist * 0.35 + heightRatio * 0.25, 0.1, 0.95);
        const col = twist > 0
          ? ditherMixUint(kelp.palette.mid, kelp.palette.light, shade, px, y)
          : ditherMixUint(kelp.palette.dark, kelp.palette.mid, shade, px, y);
        setPixel(px, y, col, false, kelp.depth);
      }

      if (h > 8 && h < kelp.height - 4 && h % 14 === 0) {
        const side = twist >= 0 ? 1 : -1;
        const podX = Math.round(centerX + side * (ribbonHalfW + 1.4));
        if (podX > jar.left + 1 && podX < jar.right - 1) {
          setPixel(podX, y, kelp.palette.pod, kelp.depth > 0.55, kelp.depth);
          setPixel(podX, y - 1, kelp.palette.light, false, kelp.depth);
        }
      }
    }
  }

  function drawFernRosette(fern) {
    const parallaxX = cylindricalShift(fern.baseX, fern.depth);
    const rootX = fern.baseX + parallaxX;

    for (let f = 0; f < fern.fronds.length; f++) {
      const frond = fern.fronds[f];
      for (let step = 0; step < frond.length; step++) {
        const t = step / Math.max(1, frond.length - 1);
        const sway =
          Math.sin(elapsed * 1.3 + frond.phase - step * 0.11) * (2.6 * t * t) +
          fern.nudgeOffset * (t * t);

        const dx = Math.sin(frond.leanAngle) * step * 0.85 + sway;
        const dy = -Math.cos(frond.leanAngle * 0.65) * step * 0.92 + t * t * 3.2;

        const cx = Math.round(rootX + dx);
        const cy = Math.round(fern.baseY + dy);
        if (cx <= jar.left || cx >= jar.right || cy <= jar.waterLine || cy >= jar.bottom) continue;

        const leafSpan = Math.round(Math.sin(t * Math.PI) * 2.4 * depthScale(fern.depth));
        for (let w = -leafSpan; w <= leafSpan; w++) {
          const px = cx + w;
          if (px <= jar.left || px >= jar.right) continue;
          const col = w === 0
            ? fern.dark
            : ditherMixUint(fern.mid, fern.light, clamp(t * 0.85 + 0.15, 0.1, 0.95), px, cy);
          setPixel(px, cy, col, false, fern.depth);
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
    if (py <= jar.waterLine) return false;

    for (let i = 0; i < grassStalks.length; i++) {
      const s = grassStalks[i];
      if (s.depth <= fish.depth + 0.03) continue;
      if (py > s.baseY || py < s.baseY - s.height + 1) continue;

      const h = s.baseY - py;
      const heightRatio = h / Math.max(1, s.height - 1);
      const bendCurve = Math.pow(heightRatio, 1.35);
      const sway =
        Math.sin(elapsed * s.swaySpeed + s.phase - h * 0.09) *
          s.swayAmp *
          bendCurve +
        s.nudgeOffset * bendCurve;
      const parallaxX = cylindricalShift(s.baseX, s.depth);
      const centerX = s.baseX + parallaxX + sway;
      const halfW = s.thickness * (1.0 - heightRatio * 0.55) * 0.5 + 0.65;

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
    const isAirborne = fish.state === FISH_STATE.AIRBORNE || fish.y <= jar.waterLine;
    const facingLeft = fish.vx < -0.02 || (Math.abs(fish.vx) <= 0.02 && Math.cos(fish.angle) < -0.08);
    const dir = facingLeft ? -1 : 1;
    const pScale = depthScale(fish.depth);
    const fishParallaxX = cylindricalShift(fish.x, fish.depth);
    const fx = fish.x + fishParallaxX;
    const fy = fish.y;

    const bodyRx = 8.4 * pScale;
    const bodyRy = 4.1 * pScale;
    const tailLen = 6.6 * pScale;

    const tailAmp =
      fish.state === FISH_STATE.RESTING
        ? 1.4
        : fish.state === FISH_STATE.ALERT ||
          fish.state === FISH_STATE.SAND_DASH ||
          fish.state === FISH_STATE.AIRBORNE ||
          fish.eatFlutterTimer > 0
        ? 3.8
        : 2.7;

    const finFlap = Math.sin(fish.finPhase) * (fish.state === FISH_STATE.RESTING ? 0.8 : 1.7) * pScale;
    const gillPulse = Math.sin(fish.gillPhase) > 0.35;

    const signedPitch = clamp(fish.pitchAngle, -0.92, 0.92);
    const cosP = Math.cos(signedPitch);
    const sinP = Math.sin(signedPitch);

    const depthTint = clamp((fish.depth - 0.15) / 0.8, 0, 1);
    const bodyOrange = ditherMixUint(
      hexToUint32("#d96b2b"),
      hexToUint32("#ff8c42"),
      depthTint,
      Math.round(fx),
      Math.round(fy)
    );
    const bodyGold = hexToUint32("#ffd166");
    const bodyBelly = hexToUint32("#ffe8a3");
    const bodyDeep = hexToUint32("#b84718");
    const finColor = hexToUint32("#ffaa64");
    const finTip = hexToUint32("#ffd6a5");
    const whiteCol = hexToUint32("#ffffff");
    const pupilCol = hexToUint32("#12161f");

    const invBodyRxSq = 1 / (bodyRx * bodyRx);
    const invBodyRySq = 1 / (bodyRy * bodyRy);

    const boundR = Math.ceil(bodyRx + tailLen + 6 * pScale);
    const minX = Math.floor(fx - boundR);
    const maxX = Math.ceil(fx + boundR);
    const minY = Math.floor(fy - boundR);
    const maxY = Math.ceil(fy + boundR);

    const renderDepth = isAirborne ? 0.995 : fish.depth;

    for (let py = minY; py <= maxY; py++) {
      for (let px = minX; px <= maxX; px++) {
        if (px <= jar.left || px >= jar.right || py <= jar.top || py >= jar.sandTop) {
          continue;
        }

        if (!isAirborne && isPixelOccludedForFish(px, py)) {
          continue;
        }

        const dx = (px - fx) * dir;
        const dy = py - fy;
        const localX = dx * cosP + dy * sinP;
        const rawLocalY = -dx * sinP + dy * cosP;

        const headToTailT = clamp((bodyRx - localX) / (bodyRx * 2 + tailLen), 0, 1.3);
        const spineWave =
          Math.sin(fish.bodyWavePhase - headToTailT * 4.2) *
          (headToTailT * headToTailT) *
          tailAmp *
          0.72 *
          pScale;
        const localY = rawLocalY - spineWave;

        const normBody = localX * localX * invBodyRxSq + localY * localY * invBodyRySq;
        if (normBody <= 1.0) {
          const isGillSlit =
            gillPulse &&
            localX >= 1.5 * pScale &&
            localX <= 2.4 * pScale &&
            Math.abs(localY) <= bodyRy * 0.56;
          if (isGillSlit) {
            setPixel(px, py, bodyDeep, false, renderDepth);
            continue;
          }
          const stripe = 0.5 + 0.5 * Math.sin((localX / pScale) * 0.85 + elapsed * 2.5);
          const verticalRatio = localY / bodyRy;
          let baseCol;
          if (verticalRatio > 0.35) {
            baseCol = ditherMixUint(bodyGold, bodyBelly, (verticalRatio - 0.35) * 1.5, px, py);
          } else {
            const dorsalShade = clamp(0.62 - verticalRatio * 0.45, 0.15, 0.95);
            baseCol = ditherMixUint(bodyDeep, bodyOrange, dorsalShade, px, py);
          }
          const finalCol = ditherMixUint(baseCol, bodyGold, stripe * 0.42, px, py);
          setPixel(px, py, finalCol, isAirborne && verticalRatio < -0.55, renderDepth);
          continue;
        }

        if (localX < -bodyRx + 1.0 * pScale && localX > -bodyRx - tailLen) {
          const tailT = (-bodyRx + 1.0 * pScale - localX) / (tailLen + 1.0 * pScale);
          const tailHalfSpan = (1.3 + tailT * 3.8) * pScale;
          const forkNotch = tailT > 0.55 ? (tailT - 0.55) * 2.6 * pScale : 0;
          const absY = Math.abs(localY);

          if (absY <= tailHalfSpan && absY >= forkNotch) {
            const edgeFade = 1.0 - absY / (tailHalfSpan + 0.5);
            if (ditherPass(edgeFade * 0.92 + 0.08, px, py)) {
              const col =
                tailT > 0.72
                  ? ditherMixUint(finColor, finTip, (tailT - 0.72) * 3.5, px, py)
                  : ditherMixUint(bodyDeep, finColor, tailT * 1.1, px, py);
              setPixel(px, py, col, false, renderDepth);
            }
          }
        }

        if (
          localX >= -3.6 * pScale &&
          localX <= 2.2 * pScale &&
          localY < -bodyRy + 0.6 * pScale &&
          localY >= -bodyRy - 3.1 * pScale + finFlap * 0.45
        ) {
          const dorsalSlope = (2.2 * pScale - localX) / (5.8 * pScale);
          const maxDorsalH = (1.2 + dorsalSlope * 2.1) * pScale;
          if (-localY - bodyRy <= maxDorsalH && ditherPass(0.78, px, py)) {
            setPixel(px, py, finColor, false, renderDepth);
          }
        }

        if (
          localX >= -2.0 * pScale &&
          localX <= 1.8 * pScale &&
          localY > bodyRy - 0.6 * pScale &&
          localY <= bodyRy + 2.4 * pScale - finFlap * 0.35
        ) {
          if (ditherPass(0.72, px, py)) {
            setPixel(px, py, finColor, false, renderDepth);
          }
        }
      }
    }

    const eyeLocalX = 4.5 * pScale;
    const eyeLocalY = -0.85 * pScale;
    const eyeWorldX = Math.round(fx + dir * (eyeLocalX * cosP - eyeLocalY * sinP));
    const eyeWorldY = Math.round(fy + (eyeLocalX * sinP + eyeLocalY * cosP));

    if (
      eyeWorldX > jar.left &&
      eyeWorldX < jar.right &&
      eyeWorldY > jar.top &&
      eyeWorldY < jar.sandTop &&
      (isAirborne || !isPixelOccludedForFish(eyeWorldX, eyeWorldY))
    ) {
      setPixel(eyeWorldX, eyeWorldY, whiteCol, true, renderDepth);
      if (pScale >= 0.85) {
        setPixel(eyeWorldX + dir, eyeWorldY, pupilCol, false, renderDepth);
      }
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
      if (ditherPass(0.55, fx, fy + 1)) setPixel(fx, fy + 1, foodRim, false, f.depth);
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
    const sandGrainLight = hexToUint32("#e6cfa1");
    const sandGrainDark = hexToUint32("#9c8052");
    const dropBright = hexToUint32("#b8f0ff");
    const dropSoft = hexToUint32("#5ab6db");

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

    for (let i = 0; i < sandGrains.length; i++) {
      const g = sandGrains[i];
      const gx = Math.round(g.x + cylindricalShift(g.x, g.depth));
      const gy = Math.round(g.y);
      if (gx > jar.left && gx < jar.right && gy > jar.waterLine && gy <= jar.bottom) {
        const alpha = g.settled ? clamp(g.settleTimer / 1.2, 0.2, 1) : 1;
        if (ditherPass(alpha, gx, gy)) {
          setPixel(gx, gy, g.bright ? sandGrainLight : sandGrainDark, false, g.depth + 0.04);
        }
      }
    }

    for (let i = 0; i < splashDroplets.length; i++) {
      const d = splashDroplets[i];
      const gx = Math.round(d.x);
      const gy = Math.round(d.y);
      if (gx > jar.left && gx < jar.right && gy > jar.top && gy <= jar.waterLine + 1) {
        setPixel(gx, gy, d.bright ? dropBright : dropSoft, d.bright, 0.99);
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
            const rim = dist >= b.radius - 0.85;
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
    for (let i = 0; i < backKelpIndices.length; i++) drawKelpRibbon(kelpRibbons[backKelpIndices[i]]);
    for (let i = 0; i < backStemIndices.length; i++) drawStemPlant(stemPlants[backStemIndices[i]]);
    for (let i = 0; i < backFernIndices.length; i++) drawFernRosette(fernFronds[backFernIndices[i]]);
    for (let i = 0; i < backGrassIndices.length; i++) drawGrassStalk(grassStalks[backGrassIndices[i]]);

    for (let i = 0; i < midRockIndices.length; i++) drawRock(rocks[midRockIndices[i]]);
    for (let i = 0; i < midKelpIndices.length; i++) drawKelpRibbon(kelpRibbons[midKelpIndices[i]]);
    for (let i = 0; i < midStemIndices.length; i++) drawStemPlant(stemPlants[midStemIndices[i]]);
    for (let i = 0; i < midFernIndices.length; i++) drawFernRosette(fernFronds[midFernIndices[i]]);
    for (let i = 0; i < midGrassIndices.length; i++) drawGrassStalk(grassStalks[midGrassIndices[i]]);

    drawFish();
    drawFoodAndHearts();

    for (let i = 0; i < frontRockIndices.length; i++) drawRock(rocks[frontRockIndices[i]]);
    for (let i = 0; i < frontKelpIndices.length; i++) drawKelpRibbon(kelpRibbons[frontKelpIndices[i]]);
    for (let i = 0; i < frontStemIndices.length; i++) drawStemPlant(stemPlants[frontStemIndices[i]]);
    for (let i = 0; i < frontFernIndices.length; i++) drawFernRosette(fernFronds[frontFernIndices[i]]);
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
      gx > jar.left && gx < jar.right && gy >= jar.waterLine - 4 && gy < jar.sandTop;
  }

  function handlePointerInteract(clientX, clientY) {
    const gx = clientX / cellSize;
    const gy = clientY / cellSize;

    if (gx > jar.left + 3 && gx < jar.right - 3 && gy < jar.waterLine) {
      spawnFood(gx, gy);
      queueGlobalEvent("food", gx, gy, 1);
      return;
    }

    if (
      gx > jar.left + 6 &&
      gx < jar.right - 6 &&
      gy >= jar.sandTop - 2 &&
      gy <= jar.bottom &&
      fish.state !== FISH_STATE.AIRBORNE &&
      fish.state !== FISH_STATE.JUMP_PREP
    ) {
      const dir = gx >= fish.x ? 1 : -1;
      spawnSandPlume(gx, jar.sandTop - 0.5, dir, fish.depth, 14);
      triggerSandDash(dir);
      queueGlobalEvent("dash", gx, gy, dir);
      return;
    }

    if (
      gx > jar.left + 10 &&
      gx < jar.right - 10 &&
      gy >= jar.waterLine &&
      gy <= jar.waterLine + 14 &&
      fish.state !== FISH_STATE.AIRBORNE &&
      fish.state !== FISH_STATE.JUMP_PREP
    ) {
      const dir = gx >= fish.x ? 1 : -1;
      spawnSurfaceRipple(gx, 0.75);
      triggerWaterJump(dir);
      queueGlobalEvent("jump", gx, gy, dir);
      return;
    }

    if (gx >= jar.left && gx <= jar.right && gy >= jar.waterLine && gy <= jar.bottom) {
      const clampedY = clamp(gy, jar.waterLine + 3, jar.sandTop - 3);
      const clickDepth = randRange(0.25, 0.9);
      for (let i = 0; i < 8; i++) {
        const bDepth = clamp(clickDepth + randRange(-0.15, 0.15), 0.12, 0.96);
        spawnBubble(
          gx + randRange(-5.0, 5.0),
          clampedY + randRange(-2.5, 3.0),
          randRange(1.1, 2.5) * depthScale(bDepth),
          bDepth
        );
      }

      spawnSurfaceRipple(gx, 0.55);
      queueGlobalEvent("bubble", gx, clampedY, 1);

      for (let i = 0; i < rocks.length; i++) {
        const r = rocks[i];
        if (gx >= r.x - 2 && gx <= r.x + r.w + 2 && gy >= r.y - 2 && gy <= r.y + r.h + 2) {
          r.glintTimer = 0.65;
        }
      }

      if (fish.state === FISH_STATE.AIRBORNE || fish.state === FISH_STATE.JUMP_PREP) return;

      const distToFish = Math.hypot(gx - fish.x, clampedY - fish.y);
      if (distToFish < 24) {
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
      if (isLeader) pushGlobalState(true);
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
    initGlobalSync();
    requestAnimationFrame(tick);
  });
})();
