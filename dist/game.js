// src/sim/model.ts
var pairKey = (a, b) => a < b ? `${a}|${b}` : `${b}|${a}`;
var armySize = (a) => Object.values(a.c).reduce((x, y) => x + (y || 0), 0);
function mulberry(seed) {
  let t = seed >>> 0;
  return () => {
    t = t + 1831565813 >>> 0;
    let r = Math.imul(t ^ t >>> 15, 1 | t);
    r = r + Math.imul(r ^ r >>> 7, 61 | r) ^ r;
    return ((r ^ r >>> 14) >>> 0) / 4294967296;
  };
}
function makeRng(g) {
  return mulberry(g.seed + g.turn * 7919 >>> 0);
}
var webReader = (p) => fetch(p).then((r) => {
  if (!r.ok) throw new Error(`${p}: ${r.status}`);
  return r.json();
});
async function loadScenario(id, read = webReader) {
  const scenario = await read(`data/scenarios/${id}.json`);
  const map = await read(`data/maps/${scenario.map}.json`);
  return { scenario, map };
}
function newGame(scenario, map, player, seed = 20250919) {
  const regions = map.regions.map((r) => ({ owner: r.s, native: r.s, stab: 70, occ: 0 }));
  const states = {};
  for (const k of Object.keys(scenario.states)) {
    const s = scenario.states[k];
    states[k] = { ...s, id: k, alive: true };
  }
  const armies = scenario.armies.map((a) => ({ ...a, c: { ...a.c }, gen: null }));
  const persons = scenario.persons.map((p) => ({ ...p, alive: scenario.year >= p.born && (p.died == null || p.died > scenario.year) }));
  for (const a of armies) {
    const best = persons.filter((p) => p.alive && p.o === a.o && (p.role === "gen" || p.role === "ruler") && !p.army).sort((x, y) => y.tong - x.tong)[0];
    if (best) {
      best.army = a.id;
      a.gen = best.id;
    }
  }
  return {
    scenario,
    map,
    turn: 0,
    year: scenario.year,
    player,
    regions,
    armies,
    states,
    persons,
    wars: [],
    grudges: {},
    fired: {},
    chain: {},
    pending: [],
    log: [{ turn: 0, text: `\u524D${-scenario.year}\u5E74\uFF0C${map.regions.length}\u90E1 ${Object.keys(scenario.states).length}\u56FD\u5E76\u7ACB\u3002`, kind: "eco" }],
    winner: null,
    seed,
    unlocked: []
  };
}
var isAtWar = (g, a, b) => g.wars.includes(pairKey(a, b));
var livingStates = (g) => Object.values(g.states).filter((s) => s.alive);
var civilLiving = (g) => livingStates(g).filter((s) => !s.tribal);
var regionsOf = (g, sid) => g.regions.map((r, i) => r.owner === sid ? i : -1).filter((i) => i >= 0);
var personById = (g, id) => id ? g.persons.find((p) => p.id === id && p.alive) : void 0;
var stateName = (g, sid) => g.states[sid]?.name || sid;
var borderRegions = (g, sid) => {
  const out = [];
  for (let i = 0; i < g.regions.length; i++) {
    if (g.regions[i].owner !== sid) continue;
    if (g.map.regions[i].adj.some((j) => g.regions[j].owner !== sid && !g.states[g.regions[j].owner].tribal)) out.push(i);
  }
  return out;
};

// src/sim/rules.ts
var COST = { foodPerK: 0.5, goldPerK: 0.08 };
var clamp = (v, a, b) => Math.max(a, Math.min(b, v));
var fmtYear = (y) => y < 0 ? `\u524D${-y}\u5E74` : `\u540E${y}\u5E74`;
var personsOf = (g, sid) => g.persons.filter((p) => p.alive && p.o === sid);
var moved = (a) => a.moved || 0;
var setMoved = (a, v) => {
  a.moved = v;
};
function stateIncome(g, sid) {
  const s = g.states[sid];
  let gold = 0, food = 0, mpCap = 0;
  for (const ri of regionsOf(g, sid)) {
    const r = g.regions[ri], m = g.map.regions[ri];
    const st = (0.5 + r.stab / 200) * (r.occ > 0 ? 0.6 : 1);
    food += (m.farm * (1 + m.irr * 0.25) * 2 + m.pop * 0.05) * st;
    gold += (m.farm * 1.5 + (m.k ? 8 : 0) + (m.t === "w" ? 2 : 0) + (m.pass ? 1 : 0) + m.pop * 0.06) * st;
    mpCap += m.pop * 6;
  }
  const able = personsOf(g, sid).filter((p) => p.role === "min" && p.zheng > 60).length;
  const mul = (1 + s.reform / 120) * (1 + able * 0.06);
  return { gold: gold * mul, food: food * mul, mp: mpCap };
}
function mainUnit(a) {
  let best = "tu", bn = -1;
  for (const [u, n] of Object.entries(a.c)) if ((n || 0) > bn) {
    bn = n || 0;
    best = u;
  }
  return best;
}
function armyPower(g, a, asDef, foe, terrain, regionDef) {
  const s = g.states[a.o];
  const train = 0.6 + a.train / 160;
  const q = 1 + (s ? s.reform : 0) / 300;
  const foeMain = foe ? mainUnit(foe) : null;
  let sum2 = 0;
  for (const [u, nRaw] of Object.entries(a.c)) {
    const n = nRaw || 0;
    if (!n) continue;
    const un = g.scenario.units[u];
    if (!un) continue;
    let p = un.pow * (un.terr[terrain] ?? 1);
    if (foeMain) p *= g.scenario.counters[u]?.[foeMain] ?? 1;
    if (asDef && u === "nu") p *= 1.2;
    sum2 += n * p;
  }
  const gen = personById(g, a.gen);
  const lead = gen ? asDef ? (gen.tong + gen.wu) / 2 : gen.tong : 28;
  const genMul = 0.7 + lead * 0.012;
  const morMul = 0.6 + a.mor / 150;
  const defMul = asDef ? 1 + regionDef * 0.07 : 1;
  return Math.max(0.1, sum2 * train * q * genMul * morMul * defMul);
}
var defOf = (g, ri) => g.map.regions[ri].def + (g.regions[ri].occ > 0 ? -2 : 0) + Math.floor(g.regions[ri].stab / 40);
function applyLoss(a, rate) {
  let lost = 0;
  for (const k of Object.keys(a.c)) {
    const n = a.c[k] || 0;
    const l = Math.min(n, Math.round(n * rate));
    a.c[k] = n - l;
    lost += l;
  }
  return lost;
}
function cleanup(g) {
  const dead = g.armies.filter((a) => armySize(a) <= 0);
  if (!dead.length) return;
  const ids = new Set(dead.map((a) => a.id));
  for (const p of g.persons) if (p.army && ids.has(p.army)) p.army = null;
  g.armies = g.armies.filter((a) => !ids.has(a.id));
}
function battle(g, atk, ri, rng) {
  const m = g.map.regions[ri];
  const keepers = g.armies.filter((d) => d.id !== atk.id && d.r === ri && d.o === g.regions[ri].owner);
  const foeOwner = g.regions[ri].owner;
  const rd = defOf(g, ri);
  const luck = 0.92 + rng() * 0.16;
  const atkP = armyPower(g, atk, false, keepers[0] || null, m.t, 0) * luck;
  const defP = keepers.length ? keepers.reduce((s, d) => s + armyPower(g, d, true, atk, m.t, rd), 0) : 0.4 * (1 + rd * 0.1);
  const x = atkP / (atkP + defP);
  const win = x > 0.5;
  const atkLoss = applyLoss(atk, clamp(0.1 + 0.5 * (1 - x), 0.04, 0.7));
  let defLoss = 0;
  for (const d of keepers) defLoss += applyLoss(d, clamp(0.1 + 0.5 * x, 0.04, 0.75));
  atk.mor = clamp(atk.mor + (win ? -6 : -30), 0, 100);
  for (const d of keepers) d.mor = clamp(d.mor + (win ? -26 : 5), 0, 100);
  cleanup(g);
  const taken = win && g.regions[ri].owner !== atk.o;
  if (taken) occupy(g, ri, atk.o);
  return { win, atkLoss, defLoss, taken, msg: `${m.n}\uFF1A${stateName(g, atk.o)}${win ? "\u514B" : "\u653B\u4E0D\u514B"}${stateName(g, keepers[0]?.o || foeOwner)}\uFF0C\u6211\u635F${atkLoss}\u5343\u4EBA\uFF0C\u5F7C\u635F${defLoss}\u5343\u4EBA` };
}
function occupy(g, ri, by) {
  const r = g.regions[ri], m = g.map.regions[ri], from = r.owner;
  r.owner = by;
  r.stab = 26;
  r.occ = 3;
  for (const a of g.armies.filter((x) => x.r === ri && x.o === from)) {
    const back = g.map.regions[ri].adj.find((j) => g.regions[j].owner === from);
    if (back == null) {
      const p = personById(g, a.gen);
      if (p) p.army = null;
      a.c = {};
    } else a.r = back;
  }
  cleanup(g);
  g.states[by].prestige += m.k ? 6 : 1;
  g.states[from].prestige = clamp(g.states[from].prestige - 2, 0, 200);
  for (const j of m.adj) {
    const o = g.regions[j].owner;
    if (o === by || !g.states[o]) continue;
    const k = pairKey(by, o);
    g.grudges[k] = (g.grudges[k] || 0) + (g.map.regions[j].k ? 8 : 3);
  }
  if (!regionsOf(g, from).length) destroyState(g, from);
}
function destroyState(g, sid) {
  const s = g.states[sid];
  if (!s || !s.alive) return;
  s.alive = false;
  for (const a of g.armies.filter((x) => x.o === sid)) {
    const p = personById(g, a.gen);
    if (p) p.army = null;
  }
  g.armies = g.armies.filter((x) => x.o !== sid);
  for (const p of g.persons) {
    if (!p.alive || p.o !== sid) continue;
    if (p.role === "ruler") p.alive = false;
    else if (p.role !== "hermit") {
      p.army = null;
      p.o = "refugee";
    }
  }
  g.wars = g.wars.filter((w) => w.split("|").indexOf(sid) < 0);
  pushLog(g, `${s.name}\u4EA1\uFF0C\u5176\u5730\u5C3D\u5165\u4E8E\u654C\u3002`, "war");
}
function declareWar(g, a, b) {
  if (a === b || isAtWar(g, a, b)) return false;
  g.wars.push(pairKey(a, b));
  g.grudges[pairKey(a, b)] = (g.grudges[pairKey(a, b)] || 0) + 20;
  for (const s of livingStates(g)) {
    if (s.tribal || s.id === a || s.id === b) continue;
    const k = pairKey(a, s.id);
    const fear = regionsOf(g, a).length / 6;
    g.grudges[k] = (g.grudges[k] || 0) + fear;
  }
  for (const ar of g.armies.filter((x) => x.o === b)) ar.mor = clamp(ar.mor + 12, 0, 100);
  pushLog(g, `${stateName(g, a)}\u5BA3\u6218${stateName(g, b)}\u3002`, "war");
  return true;
}
function makePeace(g, a, b) {
  const k = pairKey(a, b);
  if (!g.wars.includes(k)) return false;
  g.wars = g.wars.filter((w) => w !== k);
  g.grudges[k] = Math.max(0, (g.grudges[k] || 0) - 25);
  pushLog(g, `${stateName(g, a)}\u4E0E${stateName(g, b)}\u606F\u5175\u3002`, "war");
  return true;
}
function pushLog(g, text, kind = "eco") {
  g.log.push({ turn: g.turn, text, kind });
  if (g.log.length > 500) g.log.shift();
}
function check(g, sid, cmd, gold = 0, mp = 0) {
  const s = g.states[sid];
  if (!s || !s.alive) return { ok: false, msg: "\u56FD\u5DF2\u4EA1" };
  if (s.cmd < cmd) return { ok: false, msg: "\u653F\u4EE4\u5DF2\u5C3D" };
  if (s.gold < gold) return { ok: false, msg: "\u91D1\u4E0D\u8DB3" };
  if (s.mp < mp) return { ok: false, msg: "\u6C11\u529B\u4E0D\u8DB3" };
  return null;
}
var pay = (g, sid, cmd, gold = 0, mp = 0) => {
  const s = g.states[sid];
  s.cmd -= cmd;
  s.gold -= gold;
  s.mp -= mp;
};
var seq = 0;
function cmdRecruit(g, sid, ri, u, k, count = 5) {
  const un = g.scenario.units[u];
  const bad = check(g, sid, 1, un.cost.gold * k, un.cost.mp * k);
  if (bad) return bad;
  if (g.regions[ri].owner !== sid) return { ok: false, msg: "\u6B64\u5730\u4E0D\u5C5E\u6211" };
  if (un.needs && g.unlocked.indexOf(un.needs) < 0) return { ok: false, msg: `\u987B\u5148\u6709${un.name}\u4E4B\u6CD5` };
  let a = g.armies.find((x) => x.r === ri && x.o === sid);
  if (!a) {
    a = { id: `a${++seq}`, o: sid, r: ri, c: {}, train: 35, mor: 65, gen: null };
    g.armies.push(a);
  }
  a.c[u] = (a.c[u] || 0) + k;
  pay(g, sid, 1, un.cost.gold * k, un.cost.mp * k);
  const msg = `${g.map.regions[ri].n}\u52DF${un.name} ${k}\u5343\u4EBA\uFF08\u5171${count}\u6B21\uFF09`;
  return { ok: true, msg };
}
function cmdMove(g, sid, armyId, ri) {
  const a = g.armies.find((x) => x.id === armyId);
  if (!a || a.o !== sid) return { ok: false, msg: "\u6B64\u519B\u975E\u5C5E\u4F60" };
  if (g.map.regions[a.r].adj.indexOf(ri) < 0) return { ok: false, msg: "\u4E24\u5730\u4E0D\u63A5\u58E4" };
  if (g.regions[ri].owner !== sid) return { ok: false, msg: "\u8BE5\u5730\u4E0D\u5C5E\u6211\uFF0C\u987B\u653B\u51FB" };
  const un = g.scenario.units[mainUnit(a)];
  if (moved(a) >= Math.max(1, Math.round(un.spd / 2))) return { ok: false, msg: "\u672C\u56DE\u5408\u5DF2\u673A\u52A8" };
  const bad = check(g, sid, 1);
  if (bad) return bad;
  setMoved(a, moved(a) + 1);
  a.r = ri;
  pay(g, sid, 1);
  return { ok: true, msg: "" };
}
function cmdAttack(g, sid, armyId, ri, rng = Math.random) {
  const a = g.armies.find((x) => x.id === armyId);
  if (!a || a.o !== sid) return { ok: false, msg: "\u6B64\u519B\u975E\u5C5E\u4F60" };
  const foe = g.regions[ri].owner;
  if (foe === sid) return { ok: false, msg: "\u4E0D\u53EF\u653B\u51FB\u5DF1\u65B9" };
  if (g.map.regions[a.r].adj.indexOf(ri) < 0) return { ok: false, msg: "\u4E24\u5730\u4E0D\u63A5\u58E4" };
  if (!isAtWar(g, sid, foe)) return { ok: false, msg: `\u987B\u5148\u5BF9${stateName(g, foe)}\u5BA3\u6218` };
  const bad = check(g, sid, 1);
  if (bad) return bad;
  pay(g, sid, 1);
  setMoved(a, moved(a) + 1);
  const r = battle(g, a, ri, rng);
  pushLog(g, r.msg, "war");
  if (r.win && g.regions[ri].owner === sid) {
    a.r = ri;
    const mate = g.armies.find((x) => x.id !== a.id && x.r === ri && x.o === sid);
    if (mate) mergeInto(g, a, mate);
  } else if (!r.win) {
    const back = g.map.regions[a.r].adj.find((j) => g.regions[j].owner === sid);
    if (back == null) {
      const sz = armySize(a);
      a.c = {};
      cleanup(g);
      if (sz) pushLog(g, `\u519B\u65E0\u5F52\u8DEF\uFF0C${sz}\u5343\u4EBA\u6CA1\u4E8E\u654C\u5883\u3002`, "war");
    } else a.r = back;
  }
  return { ok: true, msg: r.msg };
}
function mergeInto(g, a, b) {
  for (const k of Object.keys(b.c)) a.c[k] = (a.c[k] || 0) + (b.c[k] || 0);
  a.train = (a.train + b.train) / 2;
  a.mor = Math.max(a.mor, b.mor);
  if (!a.gen && b.gen) {
    a.gen = b.gen;
    const p = personById(g, b.gen);
    if (p) p.army = a.id;
  } else {
    const p = personById(g, b.gen);
    if (p) p.army = null;
  }
  g.armies = g.armies.filter((x) => x.id !== b.id);
}
function cmdBuild(g, sid, ri, kind) {
  const m = g.map.regions[ri], r = g.regions[ri];
  if (r.owner !== sid) return { ok: false, msg: "\u6B64\u5730\u4E0D\u5C5E\u6211" };
  const cost = kind === "irr" ? 30 : kind === "stab" ? 14 : 18;
  const bad = check(g, sid, 1, cost);
  if (bad) return bad;
  if (kind === "irr") {
    if (m.irr >= 3) return { ok: false, msg: "\u6C34\u5229\u5DF2\u5C3D" };
    m.irr++;
  }
  if (kind === "stab") r.stab = clamp(r.stab + 12, 0, 100);
  if (kind === "train") {
    const armies = g.armies.filter((a) => a.r === ri && a.o === sid);
    if (!armies.length) return { ok: false, msg: "\u6B64\u5730\u65E0\u519B" };
    for (const a of armies) a.train = clamp(a.train + 6, 0, 100);
  }
  pay(g, sid, 1, cost);
  return { ok: true, msg: kind === "irr" ? `\u6CBB\u6E20\u4E8E${m.n}` : kind === "stab" ? `\u5B89\u8F91${m.n}` : `\u7EC3\u5175\u4E8E${m.n}` };
}
function cmdReform(g, sid) {
  const s = g.states[sid];
  const cost = 20 + Math.round(s.reform * 0.8);
  const bad = check(g, sid, 1, cost);
  if (bad) return bad;
  const best = personsOf(g, sid).filter((p) => p.role !== "hermit").sort((a, b) => b.zheng - a.zheng)[0];
  const gain = 4 + Math.round((best ? best.zheng : 30) / 16);
  s.reform = clamp(s.reform + gain, 0, 100);
  s.worthy = clamp(s.worthy + (best && best.de > 70 ? 2 : 0), 0, 100);
  pay(g, sid, 1, cost);
  const resist = s.reform > 45 ? 7 : 3;
  for (const ri of regionsOf(g, sid)) g.regions[ri].stab = clamp(g.regions[ri].stab - resist, 0, 100);
  pushLog(g, `${s.name}\u884C\u53D8\u6CD5\uFF0C\u6CD5\u5EA6\u81F3${s.reform}\uFF08${best ? best.name : "\u65E0\u4EBA\u4E3B\u4E4B"}\uFF09\uFF0C\u4E16\u65CF\u4E0D\u5B89\u3002`, "eco");
  return { ok: true, msg: `\u53D8\u6CD5\u5EA6 +${gain}` };
}
function cmdSeekPerson(g, sid, rng = Math.random) {
  const s = g.states[sid];
  const bad = check(g, sid, 1, 28);
  if (bad) return bad;
  const inShi = g.persons.filter((p) => p.alive && (p.role === "hermit" || p.o === "refugee") && g.year - p.born >= 14 && (p.died == null || g.year <= p.died));
  const chance = 0.3 + s.worthy / 130;
  if (!inShi.length || rng() > chance) {
    pay(g, sid, 1, 28);
    const abroad = g.persons.filter((p) => p.alive && p.o !== sid && p.o !== "refugee" && p.role !== "ruler" && p.role !== "hermit" && g.year - p.born >= 16 && (p.died == null || g.year <= p.died) && p.de < 72);
    const target = abroad.length && rng() < 0.25 + s.worthy / 220 ? abroad.sort((a, b) => b.zheng + b.mou + b.tong - (a.zheng + a.mou + a.tong) || b.de - a.de)[Math.floor(rng() * 3)] : null;
    if (!target) return { ok: false, msg: `\u793C\u8D24\u672A\u6210\uFF08${s.worthy}\u8D24\u540D\uFF09\uFF0C\u7A7A\u8FD4` };
    const fromId = target.o;
    if (target.army) {
      const ar = g.armies.find((x) => x.id === target.army);
      if (ar) ar.gen = null;
      target.army = null;
    }
    target.o = sid;
    s.worthy = clamp(s.worthy - 3, 0, 100);
    if (g.states[fromId]) g.states[fromId].worthy = clamp(g.states[fromId].worthy - 5, 0, 100);
    pushLog(g, `${target.name}\u81EA${stateName(g, fromId)}\u6765\u5954\uFF0C\u539A\u5E01\u4E3A\u4E4B\u4E5F\u3002`, "evt");
    return { ok: true, msg: `\u5F97\u5BA2\u537F${target.name}` };
  }
  const score2 = (p) => (p.zheng + p.mou + p.tong) * (0.4 + s.worthy / 90) * (p.o === "refugee" ? 1.7 : 1) * (0.6 + rng() * 0.8);
  const hit = inShi.sort((a, b) => score2(b) - score2(a))[0];
  hit.o = sid;
  if (hit.role === "hermit") hit.role = hit.tong > hit.zheng ? "gen" : "min";
  s.worthy = clamp(s.worthy + 4, 0, 100);
  pay(g, sid, 1, 28);
  pushLog(g, `${hit.name}\u6765\u5954\uFF08${hit.note}\uFF09\u3002`, "evt");
  return { ok: true, msg: `\u5F97${hit.name}` };
}
function cmdAssign(g, sid, pid, armyId) {
  const p = g.persons.find((x) => x.id === pid && x.alive);
  if (!p || p.o !== sid) return { ok: false, msg: "\u975E\u6211\u4E4B\u81E3" };
  if (p.army) {
    const old = g.armies.find((a2) => a2.id === p.army);
    if (old) old.gen = null;
    p.army = null;
  }
  if (!armyId) return { ok: true, msg: "" };
  const a = g.armies.find((x) => x.id === armyId);
  if (!a || a.o !== sid) return { ok: false, msg: "\u6B64\u519B\u975E\u5C5E\u4F60" };
  if (p.role === "min" && p.tong < 45) return { ok: false, msg: `${p.name}\u4E0D\u4E60\u5175` };
  const cur = personById(g, a.gen);
  if (cur) cur.army = null;
  a.gen = p.id;
  p.army = a.id;
  return { ok: true, msg: "" };
}
function cmdDeclareWar(g, sid, foe) {
  const s = g.states[sid];
  const bad = check(g, sid, 1);
  if (bad) return bad;
  const touch = borderRegions(g, sid).some((i) => g.map.regions[i].adj.some((j) => g.regions[j].owner === foe));
  if (!touch) return { ok: false, msg: "\u4E0D\u63A5\u58E4\uFF0C\u65E0\u4ECE\u5174\u5E08" };
  if ((g.grudges[pairKey(sid, foe)] || 0) < 5) {
    if (s.prestige < 15) return { ok: false, msg: "\u65E0\u8845\u800C\u5174\u5E08\uFF0C\u5A01\u671B\u4E0D\u8DB3\uFF08\u970015\uFF09" };
    s.prestige -= 15;
    for (const o of livingStates(g)) {
      if (o.tribal || o.id === sid || o.id === foe) continue;
      const k = pairKey(sid, o.id);
      g.grudges[k] = (g.grudges[k] || 0) + 6;
    }
    pushLog(g, `${s.name}\u65E0\u8845\u800C\u4F10${stateName(g, foe)}\uFF0C\u8BF8\u4FAF\u7531\u662F\u7591\u4E4B\u3002`, "war");
  }
  pay(g, sid, 1);
  declareWar(g, sid, foe);
  return { ok: true, msg: "" };
}
function cmdPeace(g, sid, foe) {
  const s = g.states[sid];
  if (!isAtWar(g, sid, foe)) return { ok: false, msg: "\u672C\u672A\u4EA4\u5175" };
  const stronger = regionsOf(g, foe).length >= regionsOf(g, sid).length;
  if (!stronger && s.prestige < 10) return { ok: false, msg: "\u80DC\u52BF\u6C42\u548C\uFF0C\u5A01\u671B\u4E0D\u8DB3" };
  const bad = check(g, sid, 1, 18);
  if (bad) return bad;
  pay(g, sid, 1, 18);
  makePeace(g, sid, foe);
  return { ok: true, msg: "" };
}
function economyPhase(g, rng) {
  for (const s of Object.values(g.states)) {
    if (!s.alive) continue;
    const inc = stateIncome(g, s.id);
    let size = 0;
    for (const a of g.armies.filter((x) => x.o === s.id)) size += armySize(a);
    s.gold += inc.gold - size * COST.goldPerK;
    s.food += inc.food - size * COST.foodPerK;
    s.mp = clamp(s.mp + inc.mp * 0.22, 0, inc.mp);
    if (s.food < 0) {
      s.food = 0;
      for (const a of g.armies.filter((x) => x.o === s.id)) {
        a.mor = clamp(a.mor - 18, 0, 100);
        const k = mainUnit(a);
        a.c[k] = Math.max(0, (a.c[k] || 0) - Math.max(1, Math.round(armySize(a) * 0.05)));
      }
      if (g.turn % 4 === 0) pushLog(g, `${s.name}\u519B\u7CAE\u4E0D\u7EE7\uFF0C\u58EB\u5352\u9003\u6563\u3002`, "eco");
    }
    if (s.gold < 0) {
      s.gold = 0;
      for (const ri of regionsOf(g, s.id)) g.regions[ri].stab = clamp(g.regions[ri].stab - 2, 0, 100);
    }
    s.prestige = clamp(s.prestige - 0.6, 0, 200);
    for (const ri of regionsOf(g, s.id)) {
      const r = g.regions[ri], m = g.map.regions[ri];
      if (r.occ > 0) r.occ--;
      const native = r.native === s.id;
      const base = native ? 72 + s.reform / 5 : 38 + s.reform / 9;
      r.stab = clamp(r.stab + (base - r.stab) * 0.16, 0, 100);
      if (r.stab < 22 && rng() < 0.15) {
        const back = g.states[r.native];
        if (back && back.alive) {
          r.owner = r.native;
          r.stab = 55;
          pushLog(g, `${m.n}\u53DB\uFF0C\u5F52${back.name}\u3002`, "war");
        } else {
          r.stab = 44;
          pushLog(g, `${m.n}\u7FA4\u76D7\u8D77\u3002`, "war");
        }
      }
    }
    cleanup(g);
  }
}
function resetCmd(g) {
  for (const s of Object.values(g.states)) {
    if (!s.alive) continue;
    s.cmd = 3 + (s.reform >= 55 ? 1 : 0);
    for (const a of g.armies.filter((x) => x.o === s.id)) {
      setMoved(a, 0);
      a.mor = clamp(a.mor + 6, 0, 100);
    }
  }
}
function ageAndDeath(g) {
  for (const p of g.persons) {
    if (!p.alive || p.died == null || g.year <= p.died) continue;
    p.alive = false;
    if (p.army) {
      const a = g.armies.find((x) => x.id === p.army);
      if (a) a.gen = null;
      p.army = null;
    }
    const st = g.states[p.o];
    if (!st || !st.alive) continue;
    if (p.role === "ruler") {
      pushLog(g, `${st.name}${p.name}\u5352\uFF08${fmtYear(p.died)}\uFF09\u3002`, "evt");
      const heir = personsOf(g, st.id).filter((x) => x.id !== p.id && x.role !== "hermit").sort((a, b) => b.de + b.zheng - (a.de + a.zheng))[0];
      if (heir) {
        heir.role = "ruler";
        st.prestige = clamp(st.prestige - 8, 0, 200);
        for (const ri of regionsOf(g, st.id)) g.regions[ri].stab = clamp(g.regions[ri].stab - 10, 0, 100);
        pushLog(g, `${heir.name}\u55E3\u4F4D\u3002`, "evt");
      } else {
        st.reform = Math.max(0, st.reform - 10);
        pushLog(g, `${st.name}\u65E0\u55E3\uFF0C\u56FD\u653F\u7D0A\u3002`, "evt");
      }
    }
  }
}
var score = (g, s) => regionsOf(g, s.id).length * 2 + s.prestige + s.reform;
function checkVictory(g) {
  const civ = civilLiving(g);
  if (civ.length === 1) {
    g.winner = civ[0].id;
    return;
  }
  const native = new Set(g.map.regions.filter((m) => !g.states[m.s].tribal).map((m) => m.i));
  for (const s of civ) {
    if (regionsOf(g, s.id).filter((i) => native.has(i)).length >= native.size) g.winner = s.id;
  }
  if (!g.winner && g.turn >= g.scenario.turns) g.winner = civ.sort((a, b) => score(g, b) - score(g, a))[0]?.id || null;
}

// src/sim/events.ts
function readVar(g, sid, k) {
  if (k === "stab") {
    const rs = regionsOf(g, sid);
    return rs.length ? rs.reduce((a, i) => a + g.regions[i].stab, 0) / rs.length : 0;
  }
  if (k === "turn") return g.turn;
  if (k === "regions") return regionsOf(g, sid).length;
  return g.states[sid][k] ?? 0;
}
function cmp(a, op, b) {
  return op === ">=" ? a >= b : op === "<=" ? a <= b : op === ">" ? a > b : op === "<" ? a < b : op === "==" ? a === b : false;
}
var resolve = (g, scope, sid) => sid === "self" ? scope : sid;
function checkCond(g, scope, c) {
  const [k, ...a] = c;
  switch (k) {
    case "turn":
      return g.turn >= a[0] && g.turn <= a[1];
    case "exists": {
      const s = g.states[resolve(g, scope, a[0])];
      return !!s && s.alive;
    }
    case "dead": {
      const s = g.states[resolve(g, scope, a[0])];
      return !s || !s.alive;
    }
    case "has": {
      const p = g.persons.find((x) => x.id === a[0]);
      return !!p && p.alive && p.o === scope;
    }
    case "nothas": {
      const p = g.persons.find((x) => x.id === a[0]);
      return !p || !p.alive || p.o !== scope;
    }
    case "var":
      return cmp(readVar(g, scope, a[0]), a[1], a[2]);
    case "owns": {
      const names = a[0];
      return g.map.regions.some((m, i) => names.indexOf(m.n) >= 0 && g.regions[i].owner === scope);
    }
    case "city":
      return !!g.map.regions.find((m, i) => m.n === a[0] && g.regions[i].owner === scope);
    case "war":
      return isAtWar(g, scope, resolve(g, scope, a[0]));
    default:
      return true;
  }
}
function eventOk(g, ev, scope) {
  const s = g.states[scope];
  if (!s || !s.alive) return false;
  const key = ev.once ? ev.id : ev.id + "@" + scope;
  const last = g.fired[key];
  if (last != null && (ev.once || g.turn - last < 7)) return false;
  if (ev.sc !== "any" && ev.sc !== scope) return false;
  if (ev.at && (g.turn < ev.at[0] || g.turn > ev.at[1])) return false;
  for (const c of ev.c || []) if (!checkCond(g, scope, c)) return false;
  return true;
}
function applyFx(g, scope, f, rng) {
  const out = [];
  const S = g.states[scope];
  const [k, ...a] = f;
  const addVar = (key, v) => {
    if (key === "stab") return;
    S[key] = Math.max(0, readVar(g, scope, key) + v);
  };
  switch (k) {
    case "var":
      addVar(a[0], a[1]);
      break;
    case "stab":
      for (const ri of regionsOf(g, scope)) g.regions[ri].stab = clamp(g.regions[ri].stab + a[0], 0, 100);
      break;
    case "claim": {
      const from = resolve(g, scope, a[0]), to = resolve(g, scope, a[1]);
      for (const ri of regionsOf(g, from)) {
        occupy(g, ri, to);
      }
      out.push(`${stateName(g, from)}\u4E4B\u5730\u5C3D\u5F52\u4E8E${stateName(g, to)}\u3002`);
      break;
    }
    case "claimR": {
      const names = a[0], to = resolve(g, scope, a[1]);
      let n = 0;
      for (let i = 0; i < g.map.regions.length; i++) {
        if (names.indexOf(g.map.regions[i].n) < 0 || g.regions[i].owner === to) continue;
        occupy(g, i, to);
        n++;
      }
      if (n) out.push(`${n}\u5730\u5F52\u4E8E${stateName(g, to)}\u3002`);
      break;
    }
    case "loss": {
      const sid = resolve(g, scope, a[0]), v = a[1];
      for (const ri of regionsOf(g, sid)) {
        const m = g.map.regions[ri];
        m.pop = Math.max(1, Math.round(m.pop * (1 - v / 100)));
        g.regions[ri].stab = clamp(g.regions[ri].stab - v / 2, 0, 100);
      }
      out.push(`${stateName(g, sid)}\u4E27\u6C11${v}%\u3002`);
      break;
    }
    case "join": {
      const p = g.persons.find((x) => x.id === a[0]);
      if (p) {
        p.alive = true;
        p.o = p.o === "refugee" ? scope : p.o;
        if (g.year - p.born < 14) p.born = g.year - 20;
        out.push(`${p.name}\u51FA\u4ED5\u4E8E${stateName(g, p.o)}\u3002`);
      }
      break;
    }
    case "to": {
      const p = g.persons.find((x) => x.id === a[0]);
      if (p && p.alive) {
        const to = resolve(g, scope, a[1]);
        if (p.army) {
          const ar = g.armies.find((x) => x.id === p.army);
          if (ar) ar.gen = null;
          p.army = null;
        }
        p.o = to;
        out.push(`${p.name}\u53BB${stateName(g, scope)}\u800C\u4E4B${stateName(g, to)}\u3002`);
      }
      break;
    }
    case "kill": {
      const p = g.persons.find((x) => x.id === a[0]);
      if (p && p.alive) {
        p.alive = false;
        p.died = g.year;
        if (p.army) {
          const ar = g.armies.find((x) => x.id === p.army);
          if (ar) ar.gen = null;
          p.army = null;
        }
        out.push(`${p.name}\u6B7B\u3002`);
      }
      break;
    }
    case "ruler": {
      const p = g.persons.find((x) => x.id === a[0]);
      if (p) {
        p.alive = true;
        p.o = scope;
        p.role = "ruler";
        if (g.year - p.born < 14) p.born = g.year - 22;
        for (const q of personsOf(g, scope)) if (q.id !== p.id && q.role === "ruler") q.role = "min";
        out.push(`${p.name}\u4E3A${S.name}\u4E4B\u4E3B\u3002`);
      }
      break;
    }
    case "army": {
      const name = a[0], c = a[1];
      const ri = g.map.regions.findIndex((m) => m.n === name);
      if (ri >= 0) {
        if (g.regions[ri].owner !== scope) {
          g.regions[ri].owner = scope;
          g.regions[ri].stab = 30;
        }
        let ar = g.armies.find((x) => x.r === ri && x.o === scope);
        if (!ar) {
          ar = { id: `ae${g.turn}_${ri}`, o: scope, r: ri, c: {}, train: 45, mor: 75, gen: null };
          g.armies.push(ar);
        }
        for (const u of Object.keys(c)) ar.c[u] = (ar.c[u] || 0) + (c[u] || 0);
      }
      break;
    }
    case "armyR": {
      const c = a[0];
      const rs = regionsOf(g, scope);
      if (!rs.length) break;
      const ri = rs[Math.floor(rng() * rs.length)];
      let ar = g.armies.find((x) => x.r === ri && x.o === scope);
      if (!ar) {
        ar = { id: `ar${g.turn}_${ri}`, o: scope, r: ri, c: {}, train: 40, mor: 70, gen: null };
        g.armies.push(ar);
      }
      for (const u of Object.keys(c)) ar.c[u] = (ar.c[u] || 0) + (c[u] || 0);
      break;
    }
    case "disbandR": {
      let left = a[0];
      for (const ar of g.armies.filter((x) => x.o === scope)) {
        for (const u of Object.keys(ar.c)) {
          const n = ar.c[u] || 0, cut = Math.min(n, left);
          ar.c[u] = n - cut;
          left -= cut;
          if (!left) break;
        }
        if (!left) break;
      }
      cleanup(g);
      break;
    }
    case "war": {
      const b = resolve(g, scope, a[1] ?? a[0]);
      const aa = resolve(g, scope, a[0]);
      if (g.states[aa] && g.states[b]) declareWar(g, aa, b);
      break;
    }
    case "peace":
      makePeace(g, resolve(g, scope, a[0]), resolve(g, scope, a[1]));
      break;
    case "unlock":
      if (g.unlocked.indexOf(a[0]) < 0) {
        g.unlocked.push(a[0]);
        out.push(`\u65B0\u6CD5\u6210\uFF1A${a[0] === "qi" ? "\u9A91\u5175" : String(a[0])}\u53EF\u7528\u3002`);
      }
      break;
    case "vassal": {
      const v = g.states[resolve(g, scope, a[0])];
      if (v && v.alive) {
        v.vassal = scope;
        out.push(`${v.name}\u4E3A${S.name}\u4E4B\u4E0E\u56FD\uFF08\u9644\u5EB8\uFF09\u3002`);
      }
      break;
    }
    case "grudge": {
      for (const o of civilLiving(g)) if (o.id !== scope) g.grudges[pairKey(scope, o.id)] = (g.grudges[pairKey(scope, o.id)] || 0) + a[0];
      break;
    }
    case "recruit": {
      const r = cmdSeekPerson(g, scope, rng);
      if (!r.ok && r.msg) out.push(r.msg);
      break;
    }
    case "recruit_lose": {
      const own = personsOf(g, scope).filter((p) => p.role !== "ruler");
      if (own.length) {
        const p = own[Math.floor(rng() * own.length)];
        const to = civilLiving(g).filter((s) => s.id !== scope)[0];
        if (to) {
          p.o = to.id;
          out.push(`${p.name}\u53BB\u6211\u800C\u4E4B${to.name}\u3002`);
        }
      }
      break;
    }
    case "log":
      out.push(a[0]);
      break;
    case "win":
      g.winner = resolve(g, scope, a[0]);
      break;
    default:
      break;
  }
  return out;
}
function fireEvent(g, ev, scope, optIndex) {
  const S = g.states[scope];
  if (!S) return;
  const opt = ev.o[clamp(optIndex, 0, ev.o.length - 1)];
  g.fired[ev.once ? ev.id : ev.id + "@" + scope] = g.turn;
  if (ev.ch) g.chain[ev.ch] = (g.chain[ev.ch] || 0) + 1;
  const rng = makeRng(g);
  const lines = [`\u3010${ev.T}\u3011${opt.t}`];
  for (const f of opt.fx) lines.push(...applyFx(g, scope, f, rng));
  pushLog(g, lines.filter(Boolean).join(" "), "evt");
  if (scope === g.player && S) S.cmd = Math.max(0, S.cmd);
}
function drawEvents(g) {
  const rng = makeRng(g);
  g.pending = [];
  for (const s of livingStates(g)) {
    const pool = g.scenario.events.filter((e) => eventOk(g, e, s.id));
    if (!pool.length) continue;
    const roll = rng();
    const n = roll < 0.12 ? 2 : roll < 0.55 ? 1 : 0;
    const sorted = pool.sort((a, b) => b.w - a.w || a.id.localeCompare(b.id));
    for (let i = 0; i < n && i < sorted.length; i++) {
      const ev = sorted[i];
      if (s.id === g.player) g.pending.push(ev);
      else {
        const best = ev.o.map((o, idx) => ({ idx, ok: (o.req || []).every((r) => checkCond(g, s.id, r)) })).filter((x) => x.ok).sort((x, y) => ev.o[y.idx].s - ev.o[x.idx].s)[0];
        if (best) fireEvent(g, ev, s.id, best.idx);
        else g.fired[ev.once ? ev.id : ev.id + "@" + s.id] = g.turn;
      }
    }
  }
  return g.pending;
}

// src/sim/ai.ts
var sum = (a) => a.reduce((x, y) => x + y, 0);
var foesOf = (g, sid) => Array.from(new Set(g.wars.filter((w) => w.split("|").indexOf(sid) >= 0).map((w) => w.split("|").find((x) => x !== sid)).filter(Boolean)));
function distField(g, sid, foe) {
  const n = g.map.regions.length;
  const d = new Int16Array(n).fill(-1);
  const q = [];
  for (let i = 0; i < n; i++) {
    if (g.regions[i].owner === sid && g.map.regions[i].adj.some((j) => g.regions[j].owner === foe)) {
      d[i] = 0;
      q.push(i);
    }
  }
  for (let h = 0; h < q.length; h++) {
    for (const j of g.map.regions[q[h]].adj) {
      if (d[j] >= 0) continue;
      const o = g.regions[j].owner;
      if (o !== sid && o !== foe) continue;
      d[j] = d[q[h]] + 1;
      q.push(j);
    }
  }
  return d;
}
function pickFoe(g, sid) {
  const s = g.states[sid];
  const near = new Set(borderRegions(g, sid).flatMap((i) => g.map.regions[i].adj.map((j) => g.regions[j].owner)));
  const cands = livingStates(g).filter((o) => o.id !== sid && !o.tribal && near.has(o.id) && o.vassal !== sid && s.vassal !== o.id);
  if (!cands.length) return null;
  const myPower = sum(g.armies.filter((a) => a.o === sid).map((a) => armyPower(g, a, false, null, "p", 0)));
  const wars = g.wars.filter((w) => w.split("|").indexOf(sid) >= 0).length;
  const scored = cands.map((o) => {
    const their = sum(g.armies.filter((a) => a.o === o.id).map((a) => armyPower(g, a, true, null, g.map.regions[a.r].t, defOf(g, a.r))));
    const u = (myPower - their) / Math.max(1, myPower + their) * 60 + (g.grudges[pairKey(sid, o.id)] || 0) - wars * 22;
    return { id: o.id, u };
  }).sort((a, b) => b.u - a.u);
  return scored[0].u > 6 ? scored[0].id : null;
}
function aiArmyAct(g, a, wars, dist, rng) {
  const s = g.states[a.o];
  if (s.cmd < 1) return false;
  const here = g.map.regions[a.r];
  const targets = here.adj.map((j) => ({ j, o: g.regions[j].owner })).filter((x) => x.o !== a.o && wars.indexOf(pairKey(a.o, x.o)) >= 0);
  if (targets.length) {
    const scored = targets.map((t) => {
      const m = g.map.regions[t.j];
      const keepers = g.armies.filter((d) => d.r === t.j && d.o === g.regions[t.j].owner);
      const mine = armyPower(g, a, false, keepers[0] || null, m.t, 0);
      const theirs = sum(keepers.map((d) => armyPower(g, d, true, a, m.t, defOf(g, t.j)))) || 0.5;
      const val = mine / (mine + theirs) + (m.k ? 0.3 : 0) + (g.regions[t.j].stab < 40 ? 0.15 : 0) - (m.pass ? 0.12 : 0);
      return { j: t.j, u: val - 0.52 };
    }).filter((x) => x.u > 0).sort((x, y) => y.u - x.u);
    if (scored.length) {
      cmdAttack(g, a.o, a.id, scored[0].j, rng);
      return true;
    }
  }
  let bestJ = -1, bestD = 1e9;
  for (const j of here.adj) {
    if (g.regions[j].owner !== a.o) continue;
    for (const foe of wars.map((w) => w.split("|").find((x) => x !== a.o))) {
      const d = dist.get(foe);
      if (!d || d[j] < 0 || d[j] >= bestD) continue;
      bestD = d[j];
      bestJ = j;
    }
  }
  if (bestJ >= 0) {
    cmdMove(g, a.o, a.id, bestJ);
    return true;
  }
  return false;
}
function aiTurn(g, sid) {
  const s = g.states[sid];
  if (!s || !s.alive) return;
  const rng = makeRng(g);
  const own = regionsOf(g, sid);
  if (!own.length) return;
  const myArmies = g.armies.filter((a) => a.o === sid);
  const size = sum(myArmies.map(armySize));
  let wars = g.wars.filter((w) => w.split("|").indexOf(sid) >= 0);
  if (wars.length >= 2) {
    const weakest = foesOf(g, sid).sort((a, b) => regionsOf(g, a).length - regionsOf(g, b).length)[0];
    if (weakest) cmdPeace(g, sid, weakest);
  }
  if (wars.length < 2 && s.cmd >= 1) {
    const foe = pickFoe(g, sid);
    if (foe && (g.grudges[pairKey(sid, foe)] || 0) >= 4 && cmdDeclareWar(g, sid, foe).ok) wars = wars.concat(pairKey(sid, foe));
  }
  const worst = own.map((i) => ({ i, stab: g.regions[i].stab })).sort((a, b) => a.stab - b.stab)[0];
  if (worst && worst.stab < 45 && s.gold > 60) cmdBuild(g, sid, worst.i, "stab");
  if (s.reform < 46 && s.gold > 90 && g.turn % 2 === 0) cmdReform(g, sid);
  if (s.worthy > 35 && personsOf(g, sid).filter((p) => p.role === "min").length < 3 && s.gold > 80) cmdSeekPerson(g, sid, rng);
  if (s.mp > 12 && s.gold > 70 && size < s.pop * 0.75) {
    const pool = own.filter((i) => g.map.regions[i].pop > 15).sort((a, b) => (g.regions[a].stab < 50 ? 1 : 0) - (g.regions[b].stab < 50 ? 1 : 0) || g.map.regions[b].pop - g.map.regions[a].pop);
    const ri = pool[0];
    if (ri != null) {
      const k = Math.min(12, Math.max(3, Math.round(s.mp / 5)));
      const comp = g.unlocked.indexOf("qi") >= 0 && s.reform > 40 ? [["tu", k], ["qi", Math.max(2, Math.round(k / 3))]] : s.id === "han" ? [["nu", k], ["tu", k]] : [["tu", k]];
      for (const [u, n] of comp) if (s.cmd >= 1) cmdRecruit(g, sid, ri, u, Math.min(n, Math.floor(s.mp)), 1);
    }
  }
  const dist = new Map(foesOf(g, sid).map((f) => [f, distField(g, sid, f)]));
  let guard = 10;
  for (const a of g.armies.filter((x) => x.o === sid)) {
    if (s.cmd < 1 || armySize(a) <= 0) continue;
    aiArmyAct(g, a, wars, dist, rng);
    if (--guard <= 0) break;
  }
  for (const v of civilLiving(g)) if (v.vassal === sid && v.alive) {
    s.gold += v.gold * 0.1;
    v.gold *= 0.9;
  }
}
function coalitionPhase(g) {
  for (const s of livingStates(g)) {
    if (s.tribal || !s.alive || regionsOf(g, s.id).length < 5) continue;
    for (const o of livingStates(g)) {
      if (o.tribal || !o.alive || o.id === s.id) continue;
      const k = pairKey(s.id, o.id);
      if (isAtWar(g, s.id, o.id) || (g.grudges[k] || 0) < 55) continue;
      if (regionsOf(g, o.id).length < 6) continue;
      const touch = borderRegions(g, s.id).some((i) => g.map.regions[i].adj.some((j) => g.regions[j].owner === o.id));
      if (!touch) continue;
      if (armyPowerTotal(g, s.id) < armyPowerTotal(g, o.id) * 0.7) continue;
      declareWar(g, s.id, o.id);
      pushLog(g, `${s.name}\u5FAA\u5408\u7EB5\u4E4B\u8C0B\uFF0C\u4E0E${o.name}\u7EDD\u3002`, "war");
      g.grudges[k] = 20;
    }
  }
}
var armyPowerTotal = (g, sid) => sum(g.armies.filter((a) => a.o === sid).map((a) => armyPower(g, a, false, null, g.map.regions[a.r].t, 0)));

// src/sim/index.ts
var livingCivilStates = (g) => Object.values(g.states).filter((s) => s.alive && !s.tribal);
function endTurn(g) {
  if (g.winner) return g;
  for (const s of livingCivilStates(g)) if (s.id !== g.player) aiTurn(g, s.id);
  coalitionPhase(g);
  economyPhase(g, makeRng(g));
  ageAndDeath(g);
  g.turn++;
  g.year++;
  resetCmd(g);
  drawEvents(g);
  checkVictory(g);
  return g;
}
function chooseOption(g, evId, optIndex) {
  const ev = g.pending.find((e) => e.id === evId);
  if (!ev) return false;
  g.pending = g.pending.filter((e) => e.id !== evId);
  fireEvent(g, ev, g.player, optIndex);
  checkVictory(g);
  return true;
}
var grudgeOf = (g, a, b) => clamp(g.grudges[pairKey(a, b)] || 0, -100, 100);

// src/render/map.ts
var TERRAIN_TINT = { p: 1.06, h: 0.96, m: 0.84, w: 1 };
function shade(hex, k) {
  const n = parseInt(hex.slice(1), 16);
  const r = Math.min(255, Math.max(0, Math.round((n >> 16 & 255) * k)));
  const g = Math.min(255, Math.max(0, Math.round((n >> 8 & 255) * k)));
  const b = Math.min(255, Math.max(0, Math.round((n & 255) * k)));
  return `rgb(${r},${g},${b})`;
}
var MapView = class {
  constructor(canvas, map) {
    this.canvas = canvas;
    this.map = map;
    this.ctx = canvas.getContext("2d");
    this.kmPerDegLon = 111 * Math.cos(map.proj.lat0 * Math.PI / 180);
    for (const r of map.regions) {
      const p = new Path2D();
      for (const ring of r.rings) {
        ring.forEach(([lon, lat], i) => {
          const [x, y] = this.toWorld(lon, lat);
          if (i === 0) p.moveTo(x, y);
          else p.lineTo(x, y);
        });
        p.closePath();
      }
      this.paths.push(p);
    }
    this.buildIndex();
  }
  ctx;
  paths = [];
  border = new Path2D();
  kmPerDegLon;
  view = { z: 0.02, x: 0, y: 0 };
  dirty = true;
  hover = -1;
  dpr = Math.max(1, window.devicePixelRatio || 1);
  toWorld(lon, lat) {
    return [(lon - this.map.proj.lon0) * this.kmPerDegLon, (this.map.proj.lat0 - lat) * 111];
  }
  toScreen(x, y) {
    return [x * this.view.z + this.view.x, y * this.view.z + this.view.y];
  }
  toWorldScreen(sx, sy) {
    return [(sx - this.view.x) / this.view.z, (sy - this.view.y) / this.view.z];
  }
  fit(w, h) {
    let x0 = 1e9, y0 = 1e9, x1 = -1e9, y1 = -1e9;
    for (const r of this.map.regions) {
      if (r.tribal && (r.n === "\u9C9C\u5351\u5C71" || r.n === "\u8D3A\u5170" || r.n === "\u6D77\u6E1A" || r.n === "\u6D77\u5C9B")) continue;
      for (const ring of r.rings) for (const [lon, lat] of ring) {
        const [x, y] = this.toWorld(lon, lat);
        x0 = Math.min(x0, x);
        x1 = Math.max(x1, x);
        y0 = Math.min(y0, y);
        y1 = Math.max(y1, y);
      }
    }
    const z = Math.min(w / (x1 - x0 + 400), h / (y1 - y0 + 400));
    this.view.z = z;
    this.view.x = w / 2 - (x0 + x1) / 2 * z;
    this.view.y = h / 2 - (y0 + y1) / 2 * z;
  }
  buildIndex() {
    this.cells = /* @__PURE__ */ new Map();
    this.map.regions.forEach((r, i) => {
      r.rings.forEach((ring, ri) => {
        ring.forEach(([lon, lat], pi) => {
          const key = `${Math.floor(lon / 0.12)},${Math.floor(lat / 0.12)}`;
          let a = this.cells.get(key);
          if (!a) this.cells.set(key, a = []);
          a.push([i, ri, pi]);
        });
      });
    });
  }
  cells;
  /** 只在与他国接壤的边上描国界，一次成路径 */
  rebuildBorders(g) {
    const p = new Path2D();
    const cells = this.cells;
    const near = (lon, lat, self) => {
      const out = /* @__PURE__ */ new Set();
      for (let dx = -1; dx <= 1; dx++) for (let dy = -1; dy <= 1; dy++) {
        const a = cells.get(`${Math.floor(lon / 0.12) + dx},${Math.floor(lat / 0.12) + dy}`);
        if (!a) continue;
        for (const [i] of a) if (i !== self) out.add(i);
      }
      return out;
    };
    this.map.regions.forEach((r, i) => {
      const mine = g.regions[i].owner;
      r.rings.forEach((ring) => {
        for (let k = 0; k < ring.length; k++) {
          const [x1, y1] = ring[k], [x2, y2] = ring[(k + 1) % ring.length];
          const cand = near(x1, y1, i);
          let isBorder = false;
          for (const j of cand) if (g.regions[j].owner !== mine && this.map.regions[i].adj.indexOf(j) >= 0) {
            isBorder = true;
            break;
          }
          if (!isBorder) continue;
          const [ax, ay] = this.toWorld(x1, y1), [bx, by] = this.toWorld(x2, y2);
          p.moveTo(ax, ay);
          p.lineTo(bx, by);
        }
      });
    });
    this.border = p;
    this.dirty = false;
  }
  resize() {
    const c = this.canvas, d = this.dpr;
    const w = Math.round(c.clientWidth * d), h = Math.round(c.clientHeight * d);
    if (c.width !== w || c.height !== h) {
      c.width = w;
      c.height = h;
    }
    return { w, h };
  }
  draw(g, hl) {
    const { w, h } = this.resize();
    const ctx = this.ctx, v = this.view;
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.fillStyle = "#ded0ae";
    ctx.fillRect(0, 0, w, h);
    ctx.setTransform(v.z * this.dpr, 0, 0, v.z * this.dpr, v.x * this.dpr, v.y * this.dpr);
    if (this.dirty) this.rebuildBorders(g);
    for (let i = 0; i < this.map.regions.length; i++) {
      const m = this.map.regions[i], r = g.regions[i];
      const st = g.states[r.owner];
      let k = TERRAIN_TINT[m.t] ?? 1;
      if (m.tribal) k *= 0.93;
      ctx.fillStyle = shade(st?.color || "#888", k);
      ctx.fill(this.paths[i]);
      if (r.stab < 45 && !st?.tribal) {
        ctx.fillStyle = `rgba(120,20,20,${(45 - r.stab) / 130})`;
        ctx.fill(this.paths[i]);
      }
    }
    const tint = (idx, col) => {
      ctx.fillStyle = col;
      for (const i of idx) if (i >= 0) ctx.fill(this.paths[i]);
    };
    tint(hl.moves, "rgba(90,160,90,.36)");
    tint(hl.attacks, "rgba(200,60,50,.36)");
    if (hl.sel >= 0) {
      ctx.fillStyle = "rgba(255,240,190,.42)";
      ctx.fill(this.paths[hl.sel]);
    }
    ctx.lineJoin = "round";
    ctx.strokeStyle = "rgba(50,38,26,.16)";
    ctx.lineWidth = 0.8 / v.z;
    for (let i = 0; i < this.paths.length; i++) ctx.stroke(this.paths[i]);
    ctx.strokeStyle = "#3a2c1c";
    ctx.lineWidth = 3.4 / v.z;
    ctx.stroke(this.border);
    if (hl.armyAt >= 0) {
      ctx.strokeStyle = "#fff8dc";
      ctx.lineWidth = 2.2 / v.z;
      ctx.stroke(this.paths[hl.armyAt]);
    }
    ctx.setTransform(this.dpr, 0, 0, this.dpr, 0, 0);
    const z = v.z * this.dpr;
    const label = v.z > 0.014;
    for (let i = 0; i < this.map.regions.length; i++) {
      const m = this.map.regions[i];
      const [sx, sy] = this.toScreen(...this.toWorld(m.c[0], m.c[1]));
      if (sx < -60 || sy < -40 || sx > w / this.dpr + 60 || sy > h / this.dpr + 40) continue;
      if (m.k) {
        ctx.fillStyle = "#3a2c1c";
        ctx.beginPath();
        ctx.arc(sx, sy, 4.6, 0, 7);
        ctx.fill();
        ctx.fillStyle = "#f4e6c8";
        ctx.beginPath();
        ctx.arc(sx, sy, 2.4, 0, 7);
        ctx.fill();
      } else if (m.pass) {
        ctx.fillStyle = "#6b3a2a";
        ctx.beginPath();
        ctx.moveTo(sx, sy - 5.5);
        ctx.lineTo(sx + 4.6, sy + 3.6);
        ctx.lineTo(sx - 4.6, sy + 3.6);
        ctx.closePath();
        ctx.fill();
      }
      const armies = g.armies.filter((a) => a.r === i && armySize(a) > 0);
      armies.forEach((a, n) => {
        const y = sy - 12 - n * 17;
        ctx.fillStyle = g.states[a.o].color;
        ctx.strokeStyle = "#2b2117";
        ctx.lineWidth = 1;
        ctx.beginPath();
        ctx.rect(sx - 17, y - 7, 34, 14);
        ctx.fill();
        ctx.stroke();
        ctx.fillStyle = "#f6efdc";
        ctx.font = "10px system-ui";
        ctx.textAlign = "center";
        ctx.textBaseline = "middle";
        ctx.fillText(`${armySize(a)}`, sx + (a.gen ? -5 : 0), y);
        if (a.gen) {
          const p = g.persons.find((x) => x.id === a.gen);
          ctx.fillStyle = "#ffe9a8";
          ctx.fillText(`\u203B${p ? p.name.slice(0, 2) : ""}`, sx + 11, y);
        }
      });
      if (!label) continue;
      const alpha = Math.min(1, (v.z - 0.014) / 0.012);
      ctx.fillStyle = `rgba(43,33,23,${0.55 + 0.45 * alpha})`;
      ctx.font = `${m.k ? "bold " : ""}11px system-ui`;
      ctx.textAlign = "center";
      ctx.textBaseline = "top";
      ctx.fillText(m.n, sx, sy + (armies.length ? 6 + armies.length * 17 : 7));
      if (m.pass && v.z > 0.026) {
        ctx.fillStyle = `rgba(107,58,42,${alpha})`;
        ctx.font = "10px system-ui";
        ctx.fillText(m.pass, sx, sy + 20 + armies.length * 17);
      }
    }
    void z;
  }
  pick(sx, sy) {
    const [x, y] = this.toWorldScreen(sx, sy);
    const m = this.map;
    const order = m.regions.map((r, i) => {
      const [wx, wy] = this.toWorld(r.c[0], r.c[1]);
      return { i, d: (wx - x) ** 2 + (wy - y) ** 2 };
    }).sort((a, b) => a.d - b.d).slice(0, 60);
    for (const { i } of order) {
      for (const ring of m.regions[i].rings) if (pointInRing(x, y, ring, this)) return i;
    }
    return order.length ? order[0].i : -1;
  }
};
function pointInRing(x, y, ring, mv) {
  let inside = false;
  for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) {
    const [xi, yi] = mv.toWorld(ring[i][0], ring[i][1]);
    const [xj, yj] = mv.toWorld(ring[j][0], ring[j][1]);
    if (yi > y !== yj > y && x < (xj - xi) * (y - yi) / (yj - yi) + xi) inside = !inside;
  }
  return inside;
}

// src/ui/ui.ts
var el = (tag, cls = "", html = "") => {
  const e = document.createElement(tag);
  if (cls) e.className = cls;
  if (html) e.innerHTML = html;
  return e;
};
var btn = (label, on, cls = "") => {
  const b = document.createElement("button");
  b.className = `b ${cls}`;
  b.innerHTML = label;
  b.onclick = (ev) => {
    ev.stopPropagation();
    on();
  };
  return b;
};
var TERR = { p: "\u5E73\u539F", h: "\u4E18\u9675", m: "\u5C71\u5730", w: "\u6C34\u57DF" };
var ROLE = { ruler: "\u541B", gen: "\u5C06", min: "\u81E3", hermit: "\u58EB" };
var UI = class {
  app;
  root;
  top;
  left;
  right;
  log;
  modal;
  toastEl;
  popEl = null;
  timer = 0;
  constructor(app) {
    this.app = app;
    this.root = document.getElementById("ui");
    this.top = el("div", "panel top");
    this.left = el("div", "panel side left");
    this.right = el("div", "panel side right");
    this.log = el("div", "panel log");
    this.modal = el("div", "modal");
    this.toastEl = el("div", "toast");
    this.root.append(this.top, this.left, this.right, this.log, this.modal, this.toastEl);
  }
  flash(msg) {
    this.toastEl.textContent = msg;
    this.toastEl.classList.add("on");
    clearTimeout(this.timer);
    this.timer = window.setTimeout(() => this.toastEl.classList.remove("on"), 2400);
  }
  res(r) {
    if (r.msg) this.flash(r.msg);
    this.app.after();
  }
  refresh() {
    const g = this.app.g;
    this.renderTop(g);
    this.renderRegion(g);
    this.renderArmy(g);
    this.renderLog(g);
    this.renderModal(g);
  }
  renderTop(g) {
    const s = g.states[g.player];
    const inc = stateIncome(g, s.id);
    let size = 0;
    for (const a of g.armies.filter((x) => x.o === s.id)) size += armySize(a);
    const cell = (k, v, d, tip) => `<span class="res" title="${tip}"><i>${k}</i><b>${Math.round(v)}</b>${d ? `<em class="${d > 0 ? "up" : "dn"}">${d > 0 ? "+" : ""}${d.toFixed(0)}</em>` : ""}</span>`;
    const cmdMax = 3 + (s.reform >= 55 ? 1 : 0);
    this.top.innerHTML = `<div class="hdr"><b>${stateName(g, s.id)}</b><span>${fmtYear(g.year)} \xB7 \u7B2C ${g.turn + 1}/${g.scenario.turns} \u56DE\u5408</span><span class="cmd" title="\u6BCF\u56DE\u5408\u53EF\u4E0B\u7684\u547D\u4EE4\u6570">\u653F\u4EE4 ${"\u25CF".repeat(s.cmd)}${"\u25CB".repeat(Math.max(0, cmdMax - s.cmd))}</span></div><div class="row wrap">` + cell("\u91D1", s.gold, inc.gold - size * 0.08, "\u56FD\u5E93\u3002\u6BCF\u56DE\u5408\u7530\u8D4B\u4E0E\u5E02\u7A0E") + cell("\u7CAE", s.food, inc.food - size * 0.5, "\u519B\u7CAE\u3002\u6BCF\u5343\u4EBA\u6BCF\u56DE\u5408\u8017 0.5") + cell("\u6C11\u529B", s.mp, 0, "\u53EF\u5F81\u5175\u6E90\uFF0C\u5F81\u540E\u9700\u6570\u56DE\u5408\u6062\u590D") + cell("\u5175", size, 0, "\u73B0\u5F79\u5343\u4EBA") + cell("\u5730", regionsOf(g, s.id).length, 0, "\u90E1\u53BF\u6570") + cell("\u5A01\u671B", s.prestige, 0, "\u65E0\u8845\u5F00\u6218\u9700 15\uFF1B\u4F1A\u76DF\u79F0\u738B\u4E4B\u672C") + cell("\u8D24\u540D", s.worthy, 0, "\u62DB\u8D24\u4E0E\u4EBA\u624D\u6765\u5954\u7684\u6982\u7387") + cell("\u53D8\u6CD5", s.reform, 0, "\u63D0\u9AD8\u4EA7\u51FA\u3001\u5175\u6E90\u4E0E\u653F\u4EE4\u4E0A\u9650\uFF0C\u4F46\u4E16\u65CF\u4E0D\u5B89") + `</div><div class="row"><button class="b" id="t-act">\u56FD\u653F\xB7\u5916\u4EA4</button><button class="b" id="t-men">\u4EBA\u7269</button><button class="b pri" id="t-end">\u7ED3\u675F\u56DE\u5408 \u25B8</button></div>`;
    this.top.querySelector("#t-end").onclick = () => this.app.endTurn();
    this.top.querySelector("#t-men").onclick = () => this.menPanel();
    this.top.querySelector("#t-act").onclick = () => this.actPanel();
  }
  actPanel() {
    const g = this.app.g, s = g.states[g.player];
    const box = el("div", "pop");
    const gain = 4 + Math.round((personsOf(g, s.id).sort((a, b) => b.zheng - a.zheng)[0]?.zheng || 30) / 16);
    const add = (label, hint, fn) => box.append(btn(`${label}<small>${hint}</small>`, () => this.res(fn()), "wide"));
    add(`\u63A8\u884C\u53D8\u6CD5 +${gain}`, `\u8D39\u91D1 ${20 + Math.round(s.reform * 0.8)} \xB7 \u653F\u4EE41 \xB7 \u5404\u5730\u5B89\u5B9A -${s.reform > 45 ? 7 : 3}`, () => cmdReform(g, s.id));
    add("\u62DB\u8D24", "\u8D39\u91D1 28 \xB7 \u653F\u4EE41 \xB7 \u8D24\u540D\u8D8A\u9AD8\u8D8A\u6613\u5F97\u540D\u58EB\u4E0E\u5BA2\u537F\u6765\u5954", () => cmdSeekPerson(g, s.id));
    box.append(el("div", "sep"));
    box.append(el("div", "pop-t", "\u5916\u4EA4"));
    const myWars = g.wars.filter((w) => w.split("|").indexOf(s.id) >= 0).map((w) => w.split("|").find((x) => x !== s.id));
    if (!myWars.length) box.append(el("div", "dim", "\u76EE\u524D\u65E0\u6218\u4E8B"));
    for (const wid of myWars) add(`\u4E0E${stateName(g, wid)}\u8BAE\u548C`, "\u8D39\u91D1 18 \xB7 \u653F\u4EE41 \xB7 \u52A3\u52BF\u65B9\u6C42\u548C\u514D\u5A01\u671B", () => cmdPeace(g, s.id, wid));
    for (const o of Object.values(g.states)) {
      if (!o.alive || o.tribal || o.id === s.id || o.vassal === s.id || isAtWar(g, s.id, o.id)) continue;
      const near = regionsOf(g, s.id).some((i) => g.map.regions[i].adj.some((j) => g.regions[j].owner === o.id));
      if (!near) continue;
      const gr = grudgeOf(g, s.id, o.id);
      add(`\u5BA3\u6218 ${o.name}`, gr >= 5 ? `\u6709\u8845\uFF08\u6068 ${gr}\uFF09\uFF0C\u4E0D\u8D39\u5A01\u671B` : "\u65E0\u8845 \xB7 \u8D39\u5A01\u671B 15 \xB7 \u8BF8\u4FAF\u7591\u4E4B", () => cmdDeclareWar(g, s.id, o.id));
    }
    this.pop(box);
  }
  menPanel() {
    const g = this.app.g, s = g.states[g.player];
    const box = el("div", "pop wide-pop");
    const chosen = { pid: "" };
    box.append(el("div", "pop-t", "\u5148\u70B9\u4EBA\u7269\uFF0C\u518D\u70B9\u519B\u961F\u5373\u53EF\u59D4\u4EFB\u4E3A\u4E3B\u5C06"));
    const list = personsOf(g, s.id).slice().sort((a, b) => b.tong + b.zheng + b.mou - (a.tong + a.zheng + a.mou));
    for (const p of list) {
      const row = el("div", "prow");
      row.innerHTML = `<b>${p.name}</b><i class="r${p.role}">${ROLE[p.role]}</i><span>\u7EDF${p.tong} \u6B66${p.wu} \u8C0B${p.mou} \u653F${p.zheng} \u5FB7${p.de}</span><em>${p.army ? `\u9886 ${g.map.regions[g.armies.find((a) => a.id === p.army).r].n}\u519B` : p.note}</em>`;
      row.onclick = () => {
        chosen.pid = p.id;
        box.querySelectorAll(".prow").forEach((x) => x.classList.remove("on"));
        row.classList.add("on");
      };
      box.append(row);
    }
    box.append(el("div", "sep"), el("div", "pop-t", "\u59D4\u4EFB"));
    for (const a of g.armies.filter((x) => x.o === s.id)) {
      const row = el("div", "prow");
      const gen = g.persons.find((p) => p.id === a.gen);
      row.innerHTML = `<b>${g.map.regions[a.r].n}\u519B</b><i>${armySize(a)}\u5343</i><span>${gen ? `\u4E3B\u5C06 ${gen.name}\uFF08\u7EDF${gen.tong}\uFF09` : "\u65E0\u4E3B\u5C06\uFF08\u6218\u529B\u6298\u534A\uFF09"}</span>`;
      row.onclick = () => {
        if (!chosen.pid) {
          this.flash("\u5148\u5728\u4E0A\u9762\u9009\u4E00\u4E2A\u4EBA");
          return;
        }
        this.res(cmdAssign(g, s.id, chosen.pid, a.id));
        this.menPanel();
      };
      box.append(row);
    }
    box.append(btn("\u7F62\u5B98\u5F52\u91CC\uFF08\u89E3\u9664\u6240\u9009\u4EBA\u7269\u7684\u519B\u804C\uFF09", () => {
      if (!chosen.pid) {
        this.flash("\u5148\u9009\u4E00\u4E2A\u4EBA");
        return;
      }
      this.res(cmdAssign(g, s.id, chosen.pid, null));
      this.menPanel();
    }, "wide"));
    this.pop(box);
  }
  renderRegion(g) {
    const i = this.app.sel;
    this.left.innerHTML = "";
    if (i < 0) {
      this.left.classList.remove("show");
      return;
    }
    const m = g.map.regions[i], r = g.regions[i], own = g.states[r.owner];
    this.left.classList.add("show");
    const head = el("div", "hdr");
    head.innerHTML = `<b>${m.n}</b>` + (m.pass ? `<span class="tag pass">${m.pass}</span>` : "") + (m.k ? '<span class="tag">\u90FD\u57CE</span>' : "") + `<span class="tag">${TERR[m.t]}</span><span class="tag own" style="background:${own?.color || "#888"}">${own?.name || r.owner}</span>`;
    this.left.append(head);
    const here = g.armies.filter((a) => a.r === i);
    const grid = el("div", "grid");
    grid.innerHTML = `<span>\u6237\u53E3</span><b>${m.pop} \u4E07</b><span>\u7530\u7B49</span><b>${"\u2605".repeat(m.farm)}${"\u2606".repeat(5 - m.farm)}</b><span>\u6C34\u5229</span><b>${m.irr} / 3</b><span>\u57CE\u9632</span><b>${defOf(g, i)}</b><span>\u5B89\u5B9A</span><b class="${r.stab < 45 ? "bad" : ""}">${Math.round(r.stab)}</b><span>\u9A7B\u519B</span><b>${here.length ? here.map((a) => `${stateName(g, a.o)} ${armySize(a)}\u5343`).join("\uFF0C") : "\u65E0"}</b>` + (r.occ > 0 ? `<span>\u521D\u9644</span><b>\u5C1A\u9700 ${r.occ} \u56DE\u5408\u5B89\u629A\uFF0C\u4EA7\u51FA\u516D\u6298</b>` : "") + (r.native !== r.owner ? `<span>\u4EBA\u5FC3</span><b>\u6545${stateName(g, r.native)}\u4E4B\u5730</b>` : "") + `<span>\u90BB\u63A5</span><b class="adj">${m.adj.map((j) => `<i style="border-color:${g.states[g.regions[j].owner].color}">${g.map.regions[j].n}\xB7${g.states[g.regions[j].owner].name}</i>`).join("")}</b>`;
    this.left.append(grid);
    if (r.owner === g.player && !g.winner) {
      const row = el("div", "row");
      row.append(btn("\u6CBB\u6E20 +\u6C34\u5229", () => this.res(cmdBuild(g, g.player, i, "irr"))));
      row.append(btn("\u5B89\u8F91 +\u5B89\u5B9A", () => this.res(cmdBuild(g, g.player, i, "stab"))));
      row.append(btn("\u7EC3\u5175 +\u8BAD\u7EC3", () => this.res(cmdBuild(g, g.player, i, "train"))));
      this.left.append(row);
      const r2 = el("div", "row wrap");
      for (const [k, u] of Object.entries(g.scenario.units)) {
        if (u.needs && g.unlocked.indexOf(u.needs) < 0) continue;
        r2.append(btn(`\u52DF${u.name} 5\u5343`, () => this.res(cmdRecruit(g, g.player, i, k, 5, 1)), `u ${u.needs || ""}`));
      }
      this.left.append(r2);
    }
  }
  renderArmy(g) {
    const a = g.armies.find((x) => x.id === this.app.army && x.o === g.player);
    this.right.innerHTML = "";
    if (!a) {
      this.right.classList.remove("show");
      return;
    }
    this.right.classList.add("show");
    const gen = g.persons.find((p) => p.id === a.gen);
    const head = el("div", "hdr");
    head.innerHTML = `<b>${g.map.regions[a.r].n}\u519B</b><span class="tag own">${armySize(a)} \u5343</span><span class="tag">\u8BAD\u7EC3 ${Math.round(a.train)}</span><span class="tag">\u58EB\u6C14 ${Math.round(a.mor)}</span>` + (gen ? `<span class="tag pass">\u5C06 ${gen.name}</span>` : '<span class="tag bad">\u65E0\u5C06</span>');
    this.right.append(head);
    const rows = el("div", "grid");
    const total = armyPower(g, a, false, null, g.map.regions[a.r].t, 0);
    for (const [u, n] of Object.entries(a.c)) {
      if (!n) continue;
      rows.innerHTML += `<span>${g.scenario.units[u].name}</span><b>${n} \u5343</b>`;
    }
    rows.innerHTML += `<span>\u6218\u529B</span><b>${total.toFixed(0)}</b>`;
    const threat = g.armies.filter((d) => d.o !== g.player && g.map.regions[a.r].adj.indexOf(d.r) >= 0 && isAtWar(g, g.player, d.o));
    if (threat.length) {
      const t = threat.sort((x, y) => armySize(y) - armySize(x))[0];
      rows.innerHTML += `<span>\u5F53\u9762\u4E4B\u654C</span><b>${stateName(g, t.o)} ${armySize(t)}\u5343 @${g.map.regions[t.r].n}</b>`;
    }
    this.right.append(rows);
    const row = el("div", "row");
    row.append(btn(this.app.mode === "move" ? "\u53D6\u6D88" : "\u79FB\u52A8 \u25B8", () => this.setMode("move"), this.app.mode === "move" ? "on" : ""));
    row.append(btn(this.app.mode === "attack" ? "\u53D6\u6D88" : "\u653B\u51FB \u25B8", () => this.setMode("attack"), this.app.mode === "attack" ? "on" : ""));
    this.right.append(row);
    const adj = g.map.regions[a.r].adj;
    const canMove = adj.filter((j) => g.regions[j].owner === g.player).length;
    const canHit = adj.filter((j) => g.regions[j].owner !== g.player && isAtWar(g, g.player, g.regions[j].owner)).length;
    this.right.append(el("div", "hint", canMove || canHit ? `\u53EF\u52A8 ${canMove} \u5904\uFF08\u7EFF\uFF09\uFF0C\u53EF\u653B ${canHit} \u5904\uFF08\u7EA2\uFF09\u3002\u9009\u6A21\u5F0F\u540E\u76F4\u63A5\u70B9\u5730\u5757\u3002` : "\u6B64\u5730\u56DB\u5468\u65E0\u53EF\u52A8\u53EF\u653B\u4E4B\u76EE\u6807\u3002"));
  }
  setMode(m) {
    this.app.mode = this.app.mode === m ? "idle" : m;
    this.refresh();
  }
  renderLog(g) {
    const lines = g.log.slice(-80).reverse();
    this.log.innerHTML = `<div class="hdr"><b>\u5929\u4E0B</b><span class="tag">${fmtYear(g.year)}</span></div>` + lines.map((l) => `<div class="li ${l.kind || ""}"><i>${fmtYear(g.scenario.year + l.turn)}</i>${l.text}</div>`).join("");
    this.log.classList.add("show");
  }
  renderModal(g) {
    this.modal.innerHTML = "";
    this.modal.classList.remove("on");
    if (g.winner) {
      const w = g.states[g.winner];
      const total = g.map.regions.filter((m) => !g.states[m.s].tribal).length;
      const box2 = el("div", "card");
      box2.innerHTML = `<div class="ev-t">${g.winner === g.player ? "\u5929\u4E0B\u4E00" : `${w.name}\u5E76\u5929\u4E0B`}</div><div class="ev-x">${fmtYear(g.year)}\uFF0C${w.name}\u6709\u534E\u590F ${regionsOf(g, w.id).length} / ${total} \u90E1\uFF0C\u53D8\u6CD5 ${w.reform}\uFF0C\u5A01\u671B ${Math.round(w.prestige)}\u3002${g.player === w.id ? "" : `\u4F60\uFF08${stateName(g, g.player)}\uFF09\u636E ${regionsOf(g, g.player).length} \u90E1\u3002`}</div>`;
      box2.append(btn("\u6362\u4E2A\u56FD\u5BB6\u91CD\u6765", () => this.app.restart(), "wide pri"));
      this.modal.append(box2);
      this.modal.classList.add("on");
      return;
    }
    const ev = g.pending[0];
    if (!ev) return;
    const box = el("div", "card");
    box.append(el("div", "ev-t", ev.T));
    box.append(el("div", "ev-x", ev.x));
    ev.o.forEach((o, idx) => {
      const blocked = (o.req || []).some((r) => r[0] === "var" && !(r[1] === "worthy" && g.states[g.player].worthy >= r[3]));
      const b = btn(o.t, () => {
        chooseOption(g, ev.id, idx);
        this.app.after();
      }, "opt wide");
      if (blocked) b.disabled = true;
      box.append(b);
    });
    if (ev.o.length > 1) box.append(el("div", "dim", `\u4E0D\u9009\u62E9\u5219\u6401\u7F6E\uFF08\u4E0B\u56DE\u5408\u4ECD\u4F1A\u63D0\u793A\uFF09`));
    this.modal.append(box);
    this.modal.classList.add("on");
  }
  pop(box) {
    this.closePop();
    box.classList.add("on");
    this.popEl = box;
    box.append(btn("\u2715 \u5173\u95ED", () => this.closePop(), "close"));
    this.root.append(box);
  }
  closePop() {
    this.popEl?.remove();
    this.popEl = null;
  }
  highlights(g) {
    const a = g.armies.find((x) => x.id === this.app.army && x.o === g.player);
    if (!a) return { sel: this.app.sel, moves: [], attacks: [], armyAt: -1 };
    const adj = g.map.regions[a.r].adj;
    return {
      sel: this.app.sel,
      moves: adj.filter((j) => g.regions[j].owner === g.player),
      attacks: adj.filter((j) => g.regions[j].owner !== g.player && isAtWar(g, g.player, g.regions[j].owner)),
      armyAt: a.r
    };
  }
};

// src/platform/web.ts
function bindMap(canvas, h) {
  let down = null;
  const pos = (e) => {
    const r = canvas.getBoundingClientRect();
    return [e.clientX - r.left, e.clientY - r.top];
  };
  canvas.addEventListener("pointerdown", (e) => {
    const [x, y] = pos(e);
    down = { x, y, moved: 0 };
    canvas.setPointerCapture(e.pointerId);
  });
  canvas.addEventListener("pointermove", (e) => {
    const [x, y] = pos(e);
    if (down) {
      const dx = x - down.x, dy = y - down.y;
      if (Math.abs(dx) + Math.abs(dy) > 2) {
        h.onPan(dx, dy);
        down.x = x;
        down.y = y;
        down.moved += Math.abs(dx) + Math.abs(dy);
      }
    } else h.onHover(x, y);
  });
  canvas.addEventListener("pointerup", (e) => {
    const [x, y] = pos(e);
    if (down && down.moved < 6) h.onTap(x, y);
    down = null;
  });
  canvas.addEventListener("pointerleave", () => {
    down = null;
  });
  canvas.addEventListener("wheel", (e) => {
    e.preventDefault();
    const [x, y] = pos(e);
    h.onZoom(x, y, e.deltaY < 0 ? 1.16 : 1 / 1.16);
  }, { passive: false });
}
function loop(fn) {
  let alive = true;
  const step = () => {
    if (!alive) return;
    fn();
    requestAnimationFrame(step);
  };
  requestAnimationFrame(step);
  return () => {
    alive = false;
  };
}

// src/main.ts
var CHOICES = ["qin", "wei", "zhao", "han", "qi", "chu", "yan", "yue", "shu", "song", "zhongshan", "lu"];
async function boot() {
  const canvas = document.getElementById("map");
  const err = document.getElementById("err");
  let scenario, map;
  try {
    ({ scenario, map } = await loadScenario("warring_350bc"));
  } catch (e) {
    err.style.display = "block";
    err.textContent = `\u6570\u636E\u672A\u6784\u5EFA\uFF1A${String(e)}
\u5148\u8FD0\u884C npm run data && npm run build`;
    return;
  }
  const view = new MapView(canvas, map);
  let started = false;
  const app = {
    g: newGame(scenario, map, "qin"),
    sel: -1,
    army: null,
    mode: "idle",
    after() {
      view.dirty = true;
      ui.refresh();
    },
    endTurn() {
      if (app.g.winner) return;
      endTurn(app.g);
      app.mode = "idle";
      app.army = app.g.armies.find((a) => a.id === app.army && a.o === app.g.player)?.id || null;
      app.after();
    },
    tryTarget(i) {
      const g = app.g;
      const a = g.armies.find((x) => x.id === app.army && x.o === g.player);
      if (!a) return false;
      const hl = ui.highlights(g);
      if (app.mode === "move" && hl.moves.indexOf(i) >= 0) {
        const r = cmdMove(g, g.player, a.id, i);
        if (r.msg) ui.flash(r.msg);
        app.mode = "idle";
        return true;
      }
      if (app.mode === "attack" && hl.attacks.indexOf(i) >= 0) {
        const r = cmdAttack(g, g.player, a.id, i);
        if (r.msg) ui.flash(r.msg);
        app.mode = "idle";
        return true;
      }
      return false;
    },
    restart() {
      location.reload();
    }
  };
  const ui = new UI(app);
  bindMap(canvas, {
    onTap(x, y) {
      if (!started || app.g.winner) return;
      const i = view.pick(x, y);
      if (i < 0) return;
      if (app.tryTarget(i)) {
        app.after();
        return;
      }
      app.sel = i;
      app.mode = "idle";
      const own = app.g.armies.filter((a) => a.r === i && a.o === app.g.player && armySize(a) > 0);
      app.army = own.length ? own[0].id : null;
      app.after();
    },
    onHover() {
    },
    onPan(dx, dy) {
      view.view.x += dx;
      view.view.y += dy;
    },
    onZoom(x, y, k) {
      const v = view.view;
      const nz = Math.min(0.5, Math.max(6e-3, v.z * k));
      const f = nz / v.z;
      v.x = x - (x - v.x) * f;
      v.y = y - (y - v.y) * f;
      v.z = nz;
    }
  });
  view.fit(canvas.clientWidth, canvas.clientHeight);
  ui.refresh();
  loop(() => {
    if (!started) return;
    view.draw(app.g, ui.highlights(app.g));
  });
  const box = document.createElement("div");
  box.className = "start";
  const card = document.createElement("div");
  card.className = "start-card";
  card.innerHTML = `<h1>\u6218\u56FD \xB7 \u524D${-scenario.year}\u5E74</h1><p>${map.regions.length} \u90E1\uFF0C${Object.keys(scenario.states).length} \u56FD\uFF0C${scenario.turns} \u56DE\u5408\u81F3\u524D 221 \u5E74\u3002\u8FB9\u754C\u6765\u81EA\u771F\u5B9E\u73B0\u4EE3\u5DDE\u754C\uFF0C\u8BF8\u4FAF\u7586\u57DF\u7531\u90E1\u56FD\u805A\u5408\u3002</p><p class="dim">\u56DE\u5408\u5236\uFF1A\u4E00\u56DE\u5408\u4E00\u5E74\u3002\u4F60\u6BCF\u56DE\u5408\u6709 3 \u70B9\u653F\u4EE4\uFF0C\u53EF\u4EE5\u4E0B\u4E00\u9053\u547D\u4EE4\u3002\u6EDA\u8F6E\u7F29\u653E\uFF0C\u62D6\u52A8\u5E73\u79FB\uFF0C\u70B9\u5730\u5757\u9009\u4E2D\u3002</p>`;
  const grid = document.createElement("div");
  grid.className = "start-grid";
  for (const sid of CHOICES) {
    const s = scenario.states[sid];
    const b = document.createElement("button");
    b.className = "start-btn";
    b.innerHTML = `<b>${s.name}</b><span>${s.desc}</span><i>${s.regions.length}\u90E1 \xB7 ${s.pop}\u4E07\u6237 \xB7 \u53D8\u6CD5${s.reform} \xB7 \u5175${Math.round(s.pop * 0.6)}\u5343</i>`;
    b.onclick = () => {
      app.g = newGame(scenario, map, sid);
      app.sel = scenario.capOf[sid] ?? -1;
      started = true;
      box.remove();
      view.fit(canvas.clientWidth, canvas.clientHeight);
      app.after();
      ui.flash(`\u4F60\u626E\u6F14${stateName(app.g, sid)}\u3002\u628A\u534E\u590F\u6D82\u6210\u4E00\u8272\u3002`);
    };
    grid.append(b);
  }
  box.append(card, grid);
  document.getElementById("ui").append(box);
  window.__war = {
    app,
    view,
    ui,
    started: () => started,
    draw: () => view.draw(app.g, ui.highlights(app.g))
  };
}
boot().catch((e) => {
  const err = document.getElementById("err");
  err.style.display = "block";
  err.textContent = `\u542F\u52A8\u5931\u8D25\uFF1A${String(e)}`;
});
//# sourceMappingURL=game.js.map
