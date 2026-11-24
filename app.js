/*
 * Arbol de Navidad 3D en ASCII (version web de arbol_navidad_v3.py)
 *
 * Motor: nube de puntos 3D -> animacion desde ancla -> rotacion -> perspectiva
 * -> z-buffer por celda -> iluminacion Phong -> caracter ASCII + color -> bloom.
 *
 * Controles: doble clic / doble toque o ESPACIO: girar/detener arbol
 *            arrastrar o FLECHAS izq/der: rotar camara | B bloom | R repetir
 */
"use strict";

// ------------------------------------------------------------------ config
let CW = 6, CH = 9, FONT_PX = 10;   // tamano de celda (se ajusta en pantallas chicas)
const RAMP = ".:-=+*#%@@";
const BG = "#020308";
const CAM_DIST = 8.4, CAM_Y = 2.75, PITCH0 = 0.2;
const GROUND_Y = 0.0;
const LIGHT = normalize3([-0.5, 0.75, -0.6]);

let W, H, COLS, ROWS, FOCAL, CY;   // CY: centro vertical de proyeccion

// ------------------------------------------------------------------ utilidades
const TAU = Math.PI * 2;
const rand = Math.random;
const uni = (a, b) => a + (b - a) * rand();
const clamp = (v, a, b) => (v < a ? a : v > b ? b : v);
function gauss() {
  let u = 0, v = 0;
  while (u === 0) u = rand();
  while (v === 0) v = rand();
  return Math.sqrt(-2 * Math.log(u)) * Math.cos(TAU * v);
}
function normalize3(v) {
  const l = Math.hypot(v[0], v[1], v[2]) || 1;
  return [v[0] / l, v[1] / l, v[2] / l];
}
function randDir() {
  return normalize3([gauss(), gauss(), gauss()]);
}

// ------------------------------------------------------------------ nube de puntos
// kind: 0 = aparece en su lugar, 1 = crece desde el ancla, 2 = pop elastico desde el ancla
class Cloud {
  constructor() {
    this.P = []; this.N = []; this.C = []; this.A = [];
    this.t0 = []; this.dur = []; this.kind = [];
    this.kd = []; this.ks = []; this.shin = []; this.ao = [];
    this.emis = []; this.rim = []; this.spin = [];
  }

  // pts / nrm: arreglos planos [x,y,z,...]; col: [r,g,b] o plano; t0 y ao: numero o arreglo
  add(pts, nrm, col, t0, o = {}) {
    const n = pts.length / 3;
    const opt = Object.assign({ dur: 0.6, anchor: null, kind: 0, kd: 0.95, ks: 0.2, shin: 12,
      ao: 1, emis: 0, rim: 0.3, spin: true }, o);
    let A = opt.anchor;
    if (!A) {
      A = [0, 0, 0];
      for (let i = 0; i < n; i++) { A[0] += pts[3 * i]; A[1] += pts[3 * i + 1]; A[2] += pts[3 * i + 2]; }
      A = A.map((v) => v / n);
    }
    const perCol = col.length === n * 3 && n > 1;
    for (let i = 0; i < n; i++) {
      this.P.push(pts[3 * i], pts[3 * i + 1], pts[3 * i + 2]);
      const nv = normalize3([nrm[3 * i], nrm[3 * i + 1], nrm[3 * i + 2]]);
      this.N.push(nv[0], nv[1], nv[2]);
      if (perCol) this.C.push(col[3 * i], col[3 * i + 1], col[3 * i + 2]);
      else this.C.push(col[0], col[1], col[2]);
      this.A.push(A[0], A[1], A[2]);
      this.t0.push(typeof t0 === "number" ? t0 : t0[i]);
      this.ao.push(typeof opt.ao === "number" ? opt.ao : opt.ao[i]);
      this.dur.push(opt.dur); this.kind.push(opt.kind); this.kd.push(opt.kd);
      this.ks.push(opt.ks); this.shin.push(opt.shin); this.emis.push(opt.emis);
      this.rim.push(opt.rim); this.spin.push(opt.spin ? 1 : 0);
    }
  }

  build() {
    const S = {};
    for (const k of ["P", "N", "C", "A", "t0", "dur", "kind", "kd", "ks", "shin", "ao", "emis", "rim"])
      S[k] = Float32Array.from(this[k]);
    S.spin = Uint8Array.from(this.spin);
    S.n = this.t0.length;
    let end = 0;
    for (let i = 0; i < S.n; i++) end = Math.max(end, S.t0[i] + S.dur[i]);
    S.end = end;
    return S;
  }
}

// ------------------------------------------------------------------ primitivas
function fibSphere(n, c, rad) {
  const P = [], N = [];
  for (let k = 0; k < n; k++) {
    const i = k + 0.5;
    const phi = Math.acos(1 - (2 * i) / n);
    const th = Math.PI * (1 + Math.sqrt(5)) * i;
    const d = [Math.cos(th) * Math.sin(phi), Math.cos(phi), Math.sin(th) * Math.sin(phi)];
    P.push(c[0] + d[0] * rad, c[1] + d[1] * rad, c[2] + d[2] * rad);
    N.push(d[0], d[1], d[2]);
  }
  return [P, N];
}

// caras de una caja (sin fondo) muestreadas en rejilla regular
function boxFaces(size, step) {
  const [sx, sy, sz] = size;
  const faces = [
    [[-sx / 2, sy, -sz / 2], [sx, 0, 0], [0, 0, sz], [0, 1, 0]],
    [[-sx / 2, 0, sz / 2], [sx, 0, 0], [0, sy, 0], [0, 0, 1]],
    [[-sx / 2, 0, -sz / 2], [sx, 0, 0], [0, sy, 0], [0, 0, -1]],
    [[sx / 2, 0, -sz / 2], [0, 0, sz], [0, sy, 0], [1, 0, 0]],
    [[-sx / 2, 0, -sz / 2], [0, 0, sz], [0, sy, 0], [-1, 0, 0]],
  ];
  const P = [], N = [];
  for (const [o, ua, ub, nn] of faces) {
    const na = Math.floor(Math.hypot(...ua) / step) + 1;
    const nb = Math.floor(Math.hypot(...ub) / step) + 1;
    for (let b = 0; b < nb; b++) {
      for (let a = 0; a < na; a++) {
        const s = na > 1 ? a / (na - 1) : 0, v = nb > 1 ? b / (nb - 1) : 0;
        P.push(o[0] + s * ua[0] + v * ub[0], o[1] + s * ua[1] + v * ub[1], o[2] + s * ua[2] + v * ub[2]);
        N.push(nn[0], nn[1], nn[2]);
      }
    }
  }
  return [P, N];
}

function rotYFlat(P, a, off = [0, 0, 0]) {
  const c = Math.cos(a), s = Math.sin(a), out = new Array(P.length);
  for (let i = 0; i < P.length; i += 3) {
    const x = P[i], y = P[i + 1], z = P[i + 2];
    out[i] = x * c + z * s + off[0];
    out[i + 1] = y + off[1];
    out[i + 2] = -x * s + z * c + off[2];
  }
  return out;
}

function inPoly(x, y, poly) {
  let inside = false;
  for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
    const [xi, yi] = poly[i], [xj, yj] = poly[j];
    if ((yi > y) !== (yj > y) && x < ((xj - xi) * (y - yi)) / (yj - yi + 1e-12) + xi) inside = !inside;
  }
  return inside;
}

// ------------------------------------------------------------------ arbol
const TIERS = [ // [y_base, altura, radio_base] de abajo hacia arriba
  [0.50, 1.15, 1.70], [1.05, 1.05, 1.45], [1.55, 0.98, 1.20],
  [2.02, 0.92, 0.97], [2.45, 0.86, 0.76], [2.85, 0.80, 0.56],
  [3.22, 0.75, 0.37],
];
const TOP_Y = 3.97;

function envelope(y) {
  let r = 0;
  for (const [yb, h, rb] of TIERS) {
    const s = (y - yb) / h;
    if (s >= -0.05 && s <= 1) r = Math.max(r, rb * (1 - clamp(s, 0, 1)));
  }
  return r;
}

// guirnalda: espiral de arriba hacia abajo, termina abajo y al frente
const G_TOP = 3.75, G_SPAN = 3.2, G_TURNS = 4.75;
const garlandRadius = (y) => envelope(y) * 1.13 + 0.07;   // por fuera de las ramas

function garlandGap(y, th) {
  let best = 1e9, bestY = null;
  const thm = ((th % TAU) + TAU) % TAU;
  for (let k = -1; k <= Math.floor(G_TURNS) + 1; k++) {
    const u = (thm + TAU * k) / (G_TURNS * TAU);
    if (u >= 0 && u <= 1) {
      const yg = G_TOP - u * G_SPAN;
      if (Math.abs(y - yg) < best) { best = Math.abs(y - yg); bestY = yg; }
    }
  }
  return [best, bestY];
}

function buildScene() {
  const cl = new Cloud();

  // --- tronco
  {
    const P = [], N = [];
    for (let i = 0; i < 3500; i++) {
      const th = uni(0, TAU), y = uni(GROUND_Y, 0.75);
      P.push(0.2 * Math.cos(th), y, 0.2 * Math.sin(th));
      N.push(Math.cos(th), 0, Math.sin(th));
    }
    cl.add(P, N, [0.42, 0.24, 0.10], 0.2, { dur: 0.5, anchor: [0, 0, 0], kind: 1, ks: 0.05 });
  }

  // --- niveles del arbol, de abajo hacia arriba, cada uno crece desde su base
  let tTier = 0.6;
  TIERS.forEach(([yb, h, rb], i) => {
    const n = Math.floor(17000 * rb);
    const P = [], N = [], C = [], T0 = [], AO = [];
    for (let k = 0; k < n; k++) {
      const s = 1 - Math.sqrt(rand());
      const th = uni(0, TAU);
      const clump = 1 + 0.09 * Math.sin(th * (7 + i) + i * 2.1) + 0.05 * Math.sin(th * 17 + i);
      const depth = 1 - 0.16 * rand() ** 2;
      const r = rb * (1 - s) * clump * depth;
      const droop = 0.14 * (1 - s) ** 2.2;
      const y = yb + s * h - droop;
      P.push(r * Math.cos(th), y, r * Math.sin(th));
      N.push(Math.cos(th) + gauss() * 0.4, (rb / h) * 0.75 + gauss() * 0.4, Math.sin(th) + gauss() * 0.4);
      const env = envelope(y);
      const ao = clamp(r / Math.max(env, 1e-3), 0, 1) ** 2.2;
      AO.push(0.32 + 0.68 * ao);
      const g = rand();
      C.push(0.06 + 0.10 * g, 0.42 + 0.26 * g, 0.10 + 0.10 * g);
      T0.push(tTier + rand() * 0.15);
    }
    cl.add(P, N, C, T0, { dur: 0.75, anchor: [0, yb, 0], kind: 1, ks: 0.25, shin: 10, ao: AO, rim: 0.3, kd: 0.85 });
    tTier += 0.32;
  });

  // --- tapete (no gira)
  {
    const P = [], N = [], C = [];
    for (let x = -2.6; x < 2.6; x += 0.05) {
      for (let z = -2.6; z < 2.6; z += 0.05) {
        const rr = Math.hypot(x, z / 0.95);
        if (rr >= 2.55) continue;
        const lip = rr > 2.3;
        const y = GROUND_Y + (lip ? 0.1 * Math.sqrt(clamp(1 - ((rr - 2.3) / 0.25) ** 2, 0, 1)) : 0.1);
        const th = Math.atan2(z, x);
        P.push(x, y, z);
        const nb = lip ? [Math.cos(th) * 0.6, 1, Math.sin(th) * 0.6] : [0, 1, 0];
        N.push(nb[0] + gauss() * 0.06, nb[1] + gauss() * 0.06, nb[2] + gauss() * 0.06);
        const f = 0.85 + 0.15 * rand();
        C.push(0.80 * f, 0.84 * f, 0.96 * f);
      }
    }
    cl.add(P, N, C, 2.9, { dur: 0.8, anchor: [0, GROUND_Y + 0.1, 0], kind: 1, ks: 0.05, rim: 0, kd: 0.5, spin: false });
  }

  // --- estrella 3D (pop)
  {
    const poly = [];
    for (let i = 0; i < 10; i++) {
      const a = Math.PI / 2 + (i * Math.PI) / 5, r = i % 2 === 0 ? 0.33 : 0.15;
      poly.push([r * Math.cos(a), r * Math.sin(a)]);
    }
    const P = [], N = [];
    for (let qx = -0.33; qx < 0.33; qx += 0.008) {
      for (let qy = -0.33; qy < 0.33; qy += 0.008) {
        if (!inPoly(qx, qy, poly)) continue;
        const dist = Math.hypot(qx, qy) / 0.33;
        for (const side of [-1, 1]) {
          P.push(qx, qy + TOP_Y + 0.18, side * (0.1 * (1 - dist) + 0.015));
          N.push(qx * 2.4, qy * 2.4, side);
        }
      }
    }
    cl.add(P, N, [1.0, 0.74, 0.12], 3.7, { dur: 0.6, anchor: [0, TOP_Y + 0.18, 0], kind: 2, ks: 1.0, shin: 18, emis: 0.25 });
  }

  // --- guirnalda: se dibuja de arriba hacia abajo por la espiral
  {
    const P = [], N = [], T0 = [];
    for (let i = 0; i < 24000; i++) {
      const u = rand();
      const y = G_TOP - u * G_SPAN;
      const th = u * G_TURNS * TAU;
      const R = garlandRadius(y);
      const d = randDir();
      P.push(R * Math.cos(th) + d[0] * 0.07, y + d[1] * 0.07, R * Math.sin(th) + d[2] * 0.07);
      N.push(d[0], d[1], d[2]);
      T0.push(4.3 + u * 1.8);
    }
    cl.add(P, N, [0.90, 0.10, 0.10], T0, { dur: 0.15, kind: 0, ks: 0.9, shin: 22 });
  }

  // --- regalos (pop uno por uno, no giran)
  const GIFTS = [ // [angulo, radio, tamano, giro, color, liston]
    [192, 1.95, [0.45, 0.62, 0.42], 0.30, [0.48, 0.24, 0.80], [0.98, 0.78, 0.15]],
    [232, 1.85, [0.62, 0.58, 0.55], -0.15, [0.15, 0.55, 0.22], [0.95, 0.78, 0.15]],
    [305, 1.85, [0.52, 0.50, 0.50], 0.45, [0.15, 0.36, 0.90], [0.98, 0.78, 0.15]],
    [345, 1.95, [0.60, 0.50, 0.55], 0.15, [0.88, 0.16, 0.10], [0.98, 0.78, 0.15]],
    [268, 2.10, [0.45, 0.32, 0.42], 0.70, [0.90, 0.15, 0.12], [0.98, 0.78, 0.15]],
    [150, 1.55, [0.50, 0.45, 0.50], 0.5, [0.92, 0.30, 0.50], [1.0, 1.0, 1.0]],
    [30, 1.55, [0.50, 0.52, 0.50], -0.4, [0.98, 0.65, 0.10], [0.90, 0.12, 0.12]],
  ];
  let tg = 6.4;
  for (const [deg, rad, size, yaw, col, rib] of GIFTS) {
    const a = (deg * Math.PI) / 180;
    const at = [rad * Math.cos(a), GROUND_Y + 0.1, rad * Math.sin(a)];
    const anchor = [at[0], at[1] + size[1] / 2, at[2]];
    const [p, nrm] = boxFaces(size, 0.014);
    const C = [];
    for (let i = 0; i < p.length; i += 3) {
      const ribm = Math.abs(p[i]) < size[0] * 0.09 || Math.abs(p[i + 2]) < size[2] * 0.09;
      C.push(...(ribm ? rib : col));
    }
    cl.add(rotYFlat(p, yaw, at), rotYFlat(nrm, yaw), C, tg,
      { dur: 0.6, anchor, kind: 2, ks: 0.35, shin: 14, rim: 0.2, spin: false });
    const bp = [], bn = [];
    for (const s of [-1, 1]) {
      const [P, N] = fibSphere(260, [s * 0.06, size[1] + 0.04, 0], 0.055);
      bp.push(...P); bn.push(...N);
    }
    cl.add(rotYFlat(bp, yaw, at), rotYFlat(bn, yaw), rib, tg + 0.1,
      { dur: 0.6, anchor, kind: 2, ks: 0.8, shin: 20, spin: false });
    tg += 0.28;
  }

  // --- esferas: repartidas parejo, sin tapar la guirnalda, pop de arriba hacia abajo
  const palette = [[0.92, 0.10, 0.08], [0.92, 0.10, 0.08], [1.0, 0.62, 0.08],
    [0.98, 0.78, 0.15], [0.15, 0.38, 0.95], [0.98, 0.45, 0.62],
    [0.90, 0.90, 0.95], [1.0, 0.40, 0.06]];
  const orns = [];
  let b = 0;
  for (let y0 = 3.55; y0 > 0.75; y0 -= 0.34, b++) {
    const env0 = envelope(y0);
    const count = Math.max(1, Math.round((TAU * env0) / 0.7));
    const start = b * 2.39996;
    for (let j = 0; j < count; j++) {
      const th = start + (TAU * (j + uni(-0.15, 0.15))) / count;
      let y = y0 + uni(-0.05, 0.05);
      const rad = uni(0.15, 0.19) * (0.85 + 0.15 * (1 - y / 4));
      const [gap, yg] = garlandGap(y, th);
      if (yg !== null && gap < rad + 0.12) y = yg + (y >= yg ? 1 : -1) * (rad + 0.12);
      const R = envelope(y) * 0.98 + rad * 0.45;
      orns.push([[R * Math.cos(th), y, R * Math.sin(th)], rad]);
    }
  }
  orns.forEach(([c, rad], k) => {
    const t0 = 8.6 + k * 0.045;
    const [P, N] = fibSphere(Math.floor(2600 * rad), c, rad);
    const col = palette[Math.floor(rand() * palette.length)];
    cl.add(P, N, col, t0, { dur: 0.5, anchor: c, kind: 2, ks: 1.3, shin: 38, kd: 1.0, rim: 0.75 });
    const Pc = [], Nc = [];
    for (let i = 0; i < 90; i++) {                       // tapita dorada
      const a = uni(0, TAU), hh = uni(0, 0.045);
      Pc.push(c[0] + 0.32 * rad * Math.cos(a), c[1] + rad * 0.92 + hh, c[2] + 0.32 * rad * Math.sin(a));
      Nc.push(Math.cos(a), 0.3, Math.sin(a));
    }
    cl.add(Pc, Nc, [0.95, 0.75, 0.30], t0, { dur: 0.5, anchor: c, kind: 2, ks: 1.0, shin: 10 });
  });

  return cl.build();
}

// ------------------------------------------------------------------ nieve
class Snow {
  constructor(n = 1100) {
    this.n = n;
    this.P = new Float32Array(n * 3);
    this.v = new Float32Array(n);
    this.ph = new Float32Array(n);
    for (let i = 0; i < n; i++) {
      this.P[3 * i] = uni(-8, 8); this.P[3 * i + 1] = uni(-4, 15); this.P[3 * i + 2] = uni(-6, 9);
      this.v[i] = uni(0.3, 0.8); this.ph[i] = uni(0, 6.3);
    }
  }
  update(dt, t) {
    for (let i = 0; i < this.n; i++) {
      this.P[3 * i + 1] -= this.v[i] * dt;
      this.P[3 * i] += Math.sin(t * 0.7 + this.ph[i]) * 0.25 * dt;
      if (this.P[3 * i + 1] < -4) { this.P[3 * i + 1] = 15; this.P[3 * i] = uni(-8, 8); }
    }
  }
}

// ------------------------------------------------------------------ render
// matriz 3x3 = rotX(-pitch) * rotY(yaw)   (fila mayor)
function viewMatrix(yaw, pitch) {
  const cy = Math.cos(yaw), sy = Math.sin(yaw);
  const cp = Math.cos(-pitch), sp = Math.sin(-pitch);
  // rotY = [[cy,0,sy],[0,1,0],[-sy,0,cy]] ; rotX = [[1,0,0],[0,cp,-sp],[0,sp,cp]]
  return [
    cy, 0, sy,
    sp * sy, cp, -sp * cy,
    -cp * sy, sp, cp * cy,
  ];
}

let zbuf, win, wx, wy, wz, wnx, wny, wnz;

function allocBuffers() {
  const cells = COLS * ROWS;
  zbuf = new Float32Array(cells);
  win = new Int32Array(cells);
  wx = new Float32Array(cells); wy = new Float32Array(cells); wz = new Float32Array(cells);
  wnx = new Float32Array(cells); wny = new Float32Array(cells); wnz = new Float32Array(cells);
}

const colorCache = new Map();
function colorStr(r, g, b) {
  r = (r >> 3) << 3; g = (g >> 3) << 3; b = (b >> 3) << 3;
  const key = (r << 16) | (g << 8) | b;
  let s = colorCache.get(key);
  if (!s) { s = `rgb(${r},${g},${b})`; colorCache.set(key, s); }
  return s;
}

function renderFrame(ctx, S, snow, t, yaw, pitch, treeYaw) {
  const Ms = viewMatrix(yaw, pitch);              // base y regalos (quietos)
  const Mt = viewMatrix(yaw + treeYaw, pitch);    // arbol (gira)
  const cp = Math.cos(-pitch), sp = Math.sin(-pitch);
  // camara (0, CAM_Y, -CAM_DIST) pasada por rotX(-pitch)
  const camX = 0, camY = cp * CAM_Y + sp * CAM_DIST, camZ = sp * CAM_Y - cp * CAM_DIST;
  const L = [LIGHT[0], cp * LIGHT[1] - sp * LIGHT[2], sp * LIGHT[1] + cp * LIGHT[2]];

  zbuf.fill(Infinity);
  win.fill(-1);
  const halfW = W / 2, halfH = CY;
  const animating = t < S.end;
  const { P, N, A, t0, dur, kind, spin } = S;

  // 1) proyectar y z-buffer (gana el punto mas cercano de cada celda)
  for (let i = 0; i < S.n; i++) {
    if (t < t0[i]) continue;
    let x = P[3 * i], y = P[3 * i + 1], z = P[3 * i + 2];
    if (animating) {
      const p = clamp((t - t0[i]) / dur[i], 0, 1);
      if (p <= 0) continue;
      const k = kind[i];
      let s = 1;
      if (k === 1) s = 1 - (1 - p) ** 3;
      else if (k === 2) { const q = p - 1; s = 1 + 2.9 * q * q * q + 1.9 * q * q; }
      if (s !== 1) {
        const ax = A[3 * i], ay = A[3 * i + 1], az = A[3 * i + 2];
        x = ax + (x - ax) * s; y = ay + (y - ay) * s; z = az + (z - az) * s;
      }
    }
    const M = spin[i] ? Mt : Ms;
    const X = M[0] * x + M[1] * y + M[2] * z - camX;
    const Y = M[3] * x + M[4] * y + M[5] * z - camY;
    const Z = M[6] * x + M[7] * y + M[8] * z - camZ;
    if (Z <= 0.5) continue;
    const nx0 = N[3 * i], ny0 = N[3 * i + 1], nz0 = N[3 * i + 2];
    const nx = M[0] * nx0 + M[1] * ny0 + M[2] * nz0;
    const ny = M[3] * nx0 + M[4] * ny0 + M[5] * nz0;
    const nz = M[6] * nx0 + M[7] * ny0 + M[8] * nz0;
    if (nx * X + ny * Y + nz * Z >= 0.08 * Z) continue;      // mira hacia atras
    const c = Math.floor((halfW + (FOCAL * X) / Z) / CW);
    const r = Math.floor((halfH - (FOCAL * Y) / Z) / CH);
    if (c < 0 || c >= COLS || r < 0 || r >= ROWS) continue;
    const cell = r * COLS + c;
    if (Z < zbuf[cell]) {
      zbuf[cell] = Z; win[cell] = i;
      wx[cell] = X; wy[cell] = Y; wz[cell] = Z; wnx[cell] = nx; wny[cell] = ny; wnz[cell] = nz;
    }
  }
  // nieve (no gira con el arbol)
  const sP = snow.P;
  for (let j = 0; j < snow.n; j++) {
    const x = sP[3 * j], y = sP[3 * j + 1], z = sP[3 * j + 2];
    const X = x - camX;
    const Y = cp * y - sp * z - camY;
    const Z = sp * y + cp * z - camZ;
    if (Z <= 0.5) continue;
    const c = Math.floor((halfW + (FOCAL * X) / Z) / CW);
    const r = Math.floor((halfH - (FOCAL * Y) / Z) / CH);
    if (c < 0 || c >= COLS || r < 0 || r >= ROWS) continue;
    const cell = r * COLS + c;
    if (Z < zbuf[cell]) { zbuf[cell] = Z; win[cell] = -2 - j; }
  }

  // 2) iluminacion Phong solo para las celdas ganadoras y dibujo
  ctx.fillStyle = BG;
  ctx.fillRect(0, 0, W, H);
  const { C, kd, ks, shin, ao, emis, rim } = S;
  const last = RAMP.length - 1;
  for (let cell = 0; cell < win.length; cell++) {
    const w = win[cell];
    if (w === -1) continue;
    const c = cell % COLS, r = (cell / COLS) | 0;
    if (w <= -2) {
      const bb = clamp(1.25 - zbuf[cell] / 18, 0.25, 1.0);
      ctx.fillStyle = colorStr(bb * 217 | 0, bb * 230 | 0, bb * 255 | 0);
      ctx.fillText(bb > 0.8 ? "*" : ".", c * CW, r * CH);
      continue;
    }
    const i = w;
    let nx = wnx[cell], ny = wny[cell], nz = wnz[cell];
    const nl = Math.hypot(nx, ny, nz) || 1;
    nx /= nl; ny /= nl; nz /= nl;
    const X = wx[cell], Y = wy[cell], Z = wz[cell];
    const pl = Math.hypot(X, Y, Z);
    const vx = -X / pl, vy = -Y / pl, vz = -Z / pl;
    const diff = Math.max(0, nx * L[0] + ny * L[1] + nz * L[2]);
    let hx = vx + L[0], hy = vy + L[1], hz = vz + L[2];
    const hl = Math.hypot(hx, hy, hz) || 1;
    hx /= hl; hy /= hl; hz /= hl;
    const spec = Math.max(1e-6, nx * hx + ny * hy + nz * hz) ** shin[i];
    const rimv = clamp(nx * vx + ny * vy + nz * vz, 0, 1);
    const rk = rim[i], k_s = ks[i];
    let lum = (0.2 + kd[i] * diff * 0.95) * ao[i] * (1 - rk + rk * rimv) + k_s * spec;
    lum += emis[i] * 0.35;
    const f = 0.25 + 1.05 * lum, add = k_s * spec * 0.6;
    const R = clamp(C[3 * i] * f + add, 0, 1) * 255 | 0;
    const G = clamp(C[3 * i + 1] * f + add, 0, 1) * 255 | 0;
    const Bc = clamp(C[3 * i + 2] * f + add, 0, 1) * 255 | 0;
    const ci = clamp(lum * 1.15 * last, 0, last) | 0;
    ctx.fillStyle = colorStr(R, G, Bc);
    ctx.fillText(RAMP[ci], c * CW, r * CH);
  }
}

// ------------------------------------------------------------------ app
function fitToScreen(canvas, ctx, bloomCanvas) {
  // el canvas ocupa TODA la pantalla (la nieve llena de arriba a abajo)
  W = window.innerWidth; H = window.innerHeight;
  // caracteres mas finos en pantallas chicas (celular)
  const small = Math.min(W, H) < 700;
  CW = small ? 4 : 6; CH = small ? 6 : 9; FONT_PX = small ? 6.5 : 10;
  // el arbol cabe completo: limitado por alto o por ancho, lo que sea menor
  FOCAL = Math.min(H * 0.98, W * 1.45);
  CY = H / 2 + 0.093 * FOCAL;          // centra verticalmente el arbol
  COLS = Math.ceil(W / CW); ROWS = Math.ceil(H / CH);
  const dpr = window.devicePixelRatio || 1;
  canvas.width = W * dpr; canvas.height = H * dpr;
  canvas.style.width = W + "px"; canvas.style.height = H + "px";
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.font = `bold ${FONT_PX}px Consolas, "Courier New", monospace`;
  ctx.textBaseline = "top";
  bloomCanvas.width = Math.max(1, Math.floor(W / 5));
  bloomCanvas.height = Math.max(1, Math.floor(H / 5));
  allocBuffers();
}

function main() {
  const canvas = document.getElementById("scene");
  const ctx = canvas.getContext("2d", { alpha: false });
  const bloomCanvas = document.createElement("canvas");
  const bctx = bloomCanvas.getContext("2d");
  fitToScreen(canvas, ctx, bloomCanvas);
  window.addEventListener("resize", () => fitToScreen(canvas, ctx, bloomCanvas));

  let S = buildScene();
  const snow = new Snow();
  let sceneT = 0, t = 0, yawUser = 0, treeYaw = 0;
  const pitch = PITCH0;                 // fijo: no se puede mover de arriba a abajo
  let spin = true, bloom = true;
  const keys = new Set();

  window.addEventListener("keydown", (e) => {
    if (e.code === "Space") { spin = !spin; e.preventDefault(); }
    else if (e.code === "KeyB") bloom = !bloom;
    else if (e.code === "KeyR") { S = buildScene(); sceneT = 0; }
    if (e.code.startsWith("Arrow")) e.preventDefault();
    keys.add(e.code);
  });
  window.addEventListener("keyup", (e) => keys.delete(e.code));

  // arrastrar (solo horizontal) rota la camara; doble toque / doble clic gira o detiene el arbol
  let drag = null, moved = 0, lastTap = 0;
  canvas.addEventListener("pointerdown", (e) => {
    drag = e.clientX; moved = 0; canvas.setPointerCapture(e.pointerId);
  });
  canvas.addEventListener("pointermove", (e) => {
    if (drag === null) return;
    yawUser += (e.clientX - drag) * 0.008;
    moved += Math.abs(e.clientX - drag);
    drag = e.clientX;
  });
  canvas.addEventListener("pointerup", () => {
    drag = null;
    if (moved > 10) return;              // fue arrastre, no toque
    const now = performance.now();
    if (now - lastTap < 350) { spin = !spin; lastTap = 0; }
    else lastTap = now;
  });
  canvas.addEventListener("dblclick", (e) => e.preventDefault());

  setTimeout(() => document.getElementById("hint").classList.add("hidden"), 6000);

  let prev = performance.now();
  function frame(now) {
    const dt = Math.min((now - prev) / 1000, 0.05);
    prev = now;
    t += dt; sceneT += dt;
    if (keys.has("ArrowLeft")) yawUser -= 1.5 * dt;
    if (keys.has("ArrowRight")) yawUser += 1.5 * dt;
    if (spin) treeYaw += 0.4 * dt;
    const yaw = yawUser + 0.06 * Math.sin(t * 0.5);   // leve vaiven

    snow.update(dt, t);
    renderFrame(ctx, S, snow, sceneT, yaw, pitch, treeYaw);

    if (bloom) {                                        // resplandor suave
      bctx.imageSmoothingEnabled = true;
      bctx.drawImage(canvas, 0, 0, bloomCanvas.width, bloomCanvas.height);
      ctx.save();
      ctx.globalCompositeOperation = "lighter";
      ctx.globalAlpha = 0.35;
      ctx.imageSmoothingEnabled = true;
      ctx.drawImage(bloomCanvas, 0, 0, W, H);
      ctx.restore();
    }
    requestAnimationFrame(frame);
  }
  requestAnimationFrame(frame);
}

if (typeof window !== "undefined") window.addEventListener("load", main);
if (typeof module !== "undefined") module.exports = { buildScene, renderFrame, Snow, viewMatrix, allocBuffers,
  setSize: (w, h) => { W = w; H = h; const small = Math.min(w, h) < 700; CW = small ? 4 : 6; CH = small ? 6 : 9;
    FOCAL = Math.min(h * 0.98, w * 1.45); CY = h / 2 + 0.093 * FOCAL;
    COLS = Math.ceil(w / CW); ROWS = Math.ceil(h / CH); allocBuffers(); },
  getCell: () => [CW, CH] };
