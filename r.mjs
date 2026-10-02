import { mkdir, rename, writeFile } from "node:fs/promises";
import { dirname } from "node:path";

const H = { "user-agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0 Safari/537.36" };
const E = { amp: "&", lt: "<", gt: ">", quot: '"', apos: "'", nbsp: " " };

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const ent = (t) => t.replace(/&(#x[0-9a-f]+|#\d+|[a-z]+);/gi, (m, c) => {
  const l = c.toLowerCase();
  if (l[0] !== "#") return E[l] ?? m;
  return String.fromCodePoint(l[1] === "x" ? parseInt(l.slice(2), 16) : +l.slice(1));
});
const val = (t) => {
  const m = /^\s*<!\[CDATA\[([\s\S]*?)\]\]>\s*$/.exec(t);
  return m ? m[1] : ent(t);
};
const tag = (t, n) => {
  const m = new RegExp(`<${n}\\b[^>]*>([\\s\\S]*?)</${n}>`).exec(t);
  return m ? val(m[1]) : undefined;
};
const plain = (t) => ent(t.replace(/<br\s*\/?>/gi, "\n").replace(/<[^>]+>/g, "")).replace(/[ \t]+/g, " ").trim();
const num = (v) => (v === "" || v == null ? NaN : +v);
const pt = (x, y) => (Number.isFinite(x) && Number.isFinite(y) ? { type: "Point", coordinates: [x, y] } : null);
const ring = (c) => c.trim().split(/\s+/).filter(Boolean).map((p) => p.split(",").slice(0, 2).map(Number));

function stable(v) {
  if (Array.isArray(v)) return `[${v.map(stable).join(",")}]`;
  if (v && typeof v === "object") {
    return `{${Object.keys(v).sort().filter((k) => v[k] !== undefined).map((k) => `${JSON.stringify(k)}:${stable(v[k])}`).join(",")}}`;
  }
  return JSON.stringify(v ?? null);
}

function cmp(a, b) {
  const x = num(a), y = num(b);
  if (Number.isFinite(x) && Number.isFinite(y)) return x - y;
  return String(a ?? "").localeCompare(String(b ?? ""));
}

const P = {
  a: (t) => JSON.parse(t).features,
  b: (t, s) => JSON.parse(t).map((o) => {
    const { [s.p]: f, ...q } = o;
    let g = pt(num(o[s.x]), num(o[s.y]));
    if (Array.isArray(f) && f.length >= 6) {
      const r = [];
      for (let i = 0; i + 1 < f.length; i += 2) r.push([f[i], f[i + 1]]);
      const [h, z] = [r[0], r[r.length - 1]];
      if (h[0] !== z[0] || h[1] !== z[1]) r.push(h);
      g = { type: "Polygon", coordinates: [r] };
    }
    return { type: "Feature", geometry: g, properties: q };
  }),
  c: (t, s) => {
    const root = /<(\w+)\s*\/>|<(\w+)>([\s\S]*)<\/\2>/.exec(t.replace(/<\?[\s\S]*?\?>/g, ""));
    if (!root) throw new Error("parse");
    if (root[1]) return [];
    return [...root[3].matchAll(/<(\w+)>([\s\S]*?)<\/\1>/g)].map(([, , b]) => {
      const q = {};
      for (const m of b.matchAll(/<(\w+)\s*\/>|<(\w+)>([\s\S]*?)<\/\2>/g)) q[m[1] ?? m[2]] = m[1] ? "" : val(m[3]);
      return { type: "Feature", geometry: pt(num(q[s.x]), num(q[s.y])), properties: q };
    });
  },
  e: (t) => {
    if (!/<kml\b/.test(t)) throw new Error("parse");
    return [...t.matchAll(/<Placemark\b[^>]*>([\s\S]*?)<\/Placemark>/g)].map(([, b]) => {
      const g = [];
      for (const [, p] of b.matchAll(/<Polygon\b[^>]*>([\s\S]*?)<\/Polygon>/g)) {
        const o = /<outerBoundaryIs>[\s\S]*?<coordinates>([\s\S]*?)<\/coordinates>/.exec(p);
        const i = [...p.matchAll(/<innerBoundaryIs>[\s\S]*?<coordinates>([\s\S]*?)<\/coordinates>/g)].map((m) => ring(m[1]));
        if (o) g.push({ type: "Polygon", coordinates: [ring(o[1]), ...i] });
      }
      for (const [, p] of b.matchAll(/<Point\b[^>]*>[\s\S]*?<coordinates>([\s\S]*?)<\/coordinates>/g)) {
        g.push({ type: "Point", coordinates: ring(p)[0] });
      }
      const d = tag(b, "description");
      const cells = d ? [...d.matchAll(/<t[dh]\b[^>]*>([\s\S]*?)<\/t[dh]>/gi)].map((m) => plain(m[1])).filter(Boolean) : [];
      return {
        type: "Feature",
        geometry: g.length === 0 ? null : g.length === 1 ? g[0] : g.every((x) => x.type === "Polygon")
          ? { type: "MultiPolygon", coordinates: g.map((x) => x.coordinates) }
          : { type: "GeometryCollection", geometries: g },
        properties: {
          name: tag(b, "name")?.trim(),
          style: tag(b, "styleUrl")?.trim().replace(/^#/, ""),
          description: d === undefined ? undefined : cells.length ? cells : plain(d),
        },
      };
    });
  },
};

async function get(s) {
  let e;
  for (let i = 0; i < 3; i++) {
    try {
      const r = await fetch(s.u, { method: s.m ?? "GET", headers: H, signal: AbortSignal.timeout(60000) });
      if (!r.ok) throw new Error(`http ${r.status}`);
      return await r.text();
    } catch (x) {
      e = x;
      if (i < 2) await sleep(5000 * (i + 1));
    }
  }
  throw e;
}

async function run(s) {
  const f = P[s.t](await get(s), s);
  if (!Array.isArray(f)) throw new Error("parse");
  const l = f.map(stable).map((j, i) => [f[i].properties?.[s.k], j]);
  l.sort((a, b) => cmp(a[0], b[0]) || (a[1] < b[1] ? -1 : a[1] > b[1] ? 1 : 0));
  const out = `{"type":"FeatureCollection","features":[\n${l.map((x) => x[1]).join(",\n")}\n]}\n`;
  await mkdir(dirname(s.o), { recursive: true });
  await writeFile(`${s.o}.tmp`, out);
  await rename(`${s.o}.tmp`, s.o);
  return f.length;
}

const S = JSON.parse(process.env.S ?? "[]");
const R = await Promise.allSettled(S.map(run));
let bad = 0;
R.forEach((r, i) => {
  if (r.status === "fulfilled") console.log(`${S[i].o} ${r.value}`);
  else {
    bad++;
    console.log(`${S[i].o} fail ${r.reason?.name ?? ""} ${/^(http \d+|parse)$/.test(r.reason?.message) ? r.reason.message : ""}`.trim());
  }
});
if (bad) process.exitCode = 1;
