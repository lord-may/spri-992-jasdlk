import { mkdir, rename, writeFile } from "node:fs/promises";
import { dirname } from "node:path";
import { gunzipSync, inflateRawSync } from "node:zlib";

const H = {
  "user-agent":
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0 Safari/537.36",
};
const E = { amp: "&", lt: "<", gt: ">", quot: '"', apos: "'", nbsp: " " };

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const ent = (t) =>
  t.replace(/&(#x[0-9a-f]+|#\d+|[a-z]+);/gi, (m, c) => {
    const l = c.toLowerCase();
    if (l[0] !== "#") return E[l] ?? m;
    return String.fromCodePoint(
      l[1] === "x" ? parseInt(l.slice(2), 16) : +l.slice(1),
    );
  });
const val = (t) => {
  const m = /^\s*<!\[CDATA\[([\s\S]*?)\]\]>\s*$/.exec(t);
  return m ? m[1] : ent(t);
};
const tag = (t, n) => {
  const m = new RegExp(`<${n}\\b[^>]*>([\\s\\S]*?)</${n}>`).exec(t);
  return m ? val(m[1]) : undefined;
};
const plain = (t) =>
  ent(t.replace(/<br\s*\/?>/gi, "\n").replace(/<[^>]+>/g, ""))
    .replace(/[ \t]+/g, " ")
    .trim();
const num = (v) => (v === "" || v == null ? NaN : +v);
const pt = (x, y) =>
  Number.isFinite(x) && Number.isFinite(y)
    ? { type: "Point", coordinates: [x, y] }
    : null;
const ring = (c) =>
  c
    .trim()
    .split(/\s+/)
    .filter(Boolean)
    .map((p) => p.split(",").slice(0, 2).map(Number));
const shut = (r) => {
  const [h, z] = [r[0], r[r.length - 1]];
  if (r.length && (h[0] !== z[0] || h[1] !== z[1])) r.push(h);
  return r;
};
const one = (g) =>
  g.length === 0
    ? null
    : g.length === 1
      ? g[0]
      : g.every((x) => x.type === "Polygon")
        ? { type: "MultiPolygon", coordinates: g.map((x) => x.coordinates) }
        : { type: "GeometryCollection", geometries: g };
const at = (o, p) =>
  p.split(".").reduce((x, k) => (x == null || k === "" ? x : x[k]), o);

function unzip(b) {
  const e = b.lastIndexOf(Buffer.from("PK\x05\x06"));
  if (e < 0) throw new Error("parse");
  const c = b.readUInt32LE(e + 16);
  const [m, n, l] = [
    b.readUInt16LE(c + 10),
    b.readUInt32LE(c + 20),
    b.readUInt32LE(c + 42),
  ];
  const d = l + 30 + b.readUInt16LE(l + 26) + b.readUInt16LE(l + 28);
  return m === 8 ? inflateRawSync(b.subarray(d, d + n)) : b.subarray(d, d + n);
}
const txt = (b) =>
  (b.length > 3 && b.readUInt32LE(0) === 0x04034b50
    ? unzip(b)
    : b[0] === 0x1f && b[1] === 0x8b
      ? gunzipSync(b)
      : b
  )
    .toString("utf8")
    .replace(/^\uFEFF/, "");

function poly(e) {
  const r = [];
  let i = 0,
    x = 0,
    y = 0;
  while (i < e.length) {
    for (const d of [0, 1]) {
      let b,
        s = 0,
        h = 0;
      do {
        b = e.charCodeAt(i++) - 63;
        h |= (b & 31) << s;
        s += 5;
      } while (b >= 32);
      const v = h & 1 ? ~(h >> 1) : h >> 1;
      if (d) x += v;
      else y += v;
    }
    r.push([x / 1e5, y / 1e5]);
  }
  return r;
}

const kf = (t) =>
  JSON.parse(t).file_data.map(({ title, desc, geom }) => ({
    type: "Feature",
    geometry: one([
      ...(geom?.a ?? []).map((e) => ({
        type: "Polygon",
        coordinates: [shut(poly(e))],
      })),
      ...(geom?.l ?? []).map((e) => ({
        type: "LineString",
        coordinates: poly(e),
      })),
      ...(geom?.p ?? []).map((e) => ({
        type: "Point",
        coordinates: poly(e)[0],
      })),
    ]),
    properties: { title, ...desc },
  }));

const qk = (x, y, z) => {
  let q = "";
  for (let i = z; i > 0; i--)
    q += ((x >> (i - 1)) & 1) + 2 * ((y >> (i - 1)) & 1);
  return q;
};
const tile = (lon, lat, z) => {
  const n = 2 ** z,
    s = Math.sin((lat * Math.PI) / 180);
  return [
    Math.floor(((lon + 180) / 360) * n),
    Math.floor((0.5 - Math.log((1 + s) / (1 - s)) / (4 * Math.PI)) * n),
  ];
};

async function crawl(s) {
  const [[x0, y0], [x1, y1]] = [
    tile(s.g[0], s.g[3], s.z),
    tile(s.g[2], s.g[1], s.z),
  ];
  const out = new Map(),
    seen = new Map(),
    w = [];
  let k = 0;
  const lim = async (f) => {
    while (k >= 8) await new Promise((r) => w.push(r));
    k++;
    try {
      return await f();
    } finally {
      k--;
      w.shift()?.();
    }
  };
  // clusters can hold outages from neighbouring tiles, so descend into the 3x3 tiles around each cluster
  const near = (c, z) => {
    const [x, y] = tile(...c, z),
      q = [];
    for (let i = -1; i <= 1; i++)
      for (let j = -1; j <= 1; j++) q.push(qk(x + i, y + j, z));
    return q;
  };
  const go = (q) => {
    if (!seen.has(q))
      seen.set(
        q,
        (async () => {
          const t = await lim(() =>
            get(
              {},
              s.u
                .replace("{qkh}", [...q.slice(-3)].reverse().join(""))
                .replace("{q}", q),
              true,
            ),
          );
          if (t == null) return false;
          const f = kf(t);
          await Promise.all(
            f.map(async (x) => {
              const c =
                x.properties.cluster &&
                x.geometry?.type === "Point" &&
                q.length < 16;
              if (
                !c ||
                !(
                  await Promise.all(
                    near(x.geometry.coordinates, q.length + 1).map(go),
                  )
                ).some(Boolean)
              )
                out.set(stable(x), x);
            }),
          );
          return true;
        })(),
      );
    return seen.get(q);
  };
  const l = [];
  for (let x = x0; x <= x1; x++)
    for (let y = y0; y <= y1; y++) l.push(go(qk(x, y, s.z)));
  await Promise.all(l);
  return [...out.values()];
}

function stable(v) {
  if (Array.isArray(v)) return `[${v.map(stable).join(",")}]`;
  if (v && typeof v === "object") {
    return `{${Object.keys(v)
      .sort()
      .filter((k) => v[k] !== undefined)
      .map((k) => `${JSON.stringify(k)}:${stable(v[k])}`)
      .join(",")}}`;
  }
  return JSON.stringify(v ?? null);
}

function cmp(a, b) {
  const x = num(a),
    y = num(b);
  if (Number.isFinite(x) && Number.isFinite(y)) return x - y;
  return String(a ?? "").localeCompare(String(b ?? ""));
}

const P = {
  a: (t) => {
    const j = JSON.parse(t);
    if (j.exceededTransferLimit || j.properties?.exceededTransferLimit)
      throw new Error("parse");
    return j.features;
  },
  b: (t, s) =>
    at(JSON.parse(t), s.r ?? "").map((o) => {
      const { [s.p]: f, ...q } = o;
      let g = pt(num(at(o, s.x)), num(at(o, s.y)));
      const r = [];
      if (Array.isArray(f) && typeof f[0] === "number")
        for (let i = 0; i + 1 < f.length; i += 2) r.push([f[i], f[i + 1]]);
      else if (Array.isArray(f))
        for (const v of f)
          if (Number.isFinite(v?.x) && Number.isFinite(v?.y))
            r.push([v.x, v.y]);
      if (r.length >= 3) g = { type: "Polygon", coordinates: [shut(r)] };
      return { type: "Feature", geometry: g, properties: q };
    }),
  c: (t, s) => {
    const root = /<(\w+)\s*\/>|<(\w+)>([\s\S]*)<\/\2>/.exec(
      t.replace(/<\?[\s\S]*?\?>/g, ""),
    );
    if (!root) throw new Error("parse");
    if (root[1]) return [];
    return [...root[3].matchAll(/<(\w+)>([\s\S]*?)<\/\1>/g)].map(([, , b]) => {
      const q = {};
      for (const m of b.matchAll(/<(\w+)\s*\/>|<(\w+)>([\s\S]*?)<\/\2>/g))
        q[m[1] ?? m[2]] = m[1] ? "" : val(m[3]);
      return {
        type: "Feature",
        geometry: pt(num(q[s.x]), num(q[s.y])),
        properties: q,
      };
    });
  },
  e: (t) => {
    if (!/<kml\b/.test(t)) throw new Error("parse");
    return [...t.matchAll(/<Placemark\b[^>]*>([\s\S]*?)<\/Placemark>/g)].map(
      ([, b]) => {
        const g = [];
        for (const [, p] of b.matchAll(
          /<Polygon\b[^>]*>([\s\S]*?)<\/Polygon>/g,
        )) {
          const o =
            /<outerBoundaryIs>[\s\S]*?<coordinates>([\s\S]*?)<\/coordinates>/.exec(
              p,
            );
          const i = [
            ...p.matchAll(
              /<innerBoundaryIs>[\s\S]*?<coordinates>([\s\S]*?)<\/coordinates>/g,
            ),
          ].map((m) => ring(m[1]));
          if (o) g.push({ type: "Polygon", coordinates: [ring(o[1]), ...i] });
        }
        for (const [, p] of b.matchAll(
          /<Point\b[^>]*>[\s\S]*?<coordinates>([\s\S]*?)<\/coordinates>/g,
        )) {
          g.push({ type: "Point", coordinates: ring(p)[0] });
        }
        const d = tag(b, "description");
        const cells = d
          ? [...d.matchAll(/<t[dh]\b[^>]*>([\s\S]*?)<\/t[dh]>/gi)]
              .map((m) => plain(m[1]))
              .filter(Boolean)
          : [];
        // self-closing elements (<SimpleData name="X" />) are empty values; without the
        // `\/>` branch they swallowed every element up to the next closing tag
        const x = [
          ...b.matchAll(
            /<(Data|SimpleData)\b[^>]*?\bname="([^"]*)"[^>]*?(?:\/>|>((?:(?!<\/\1>)[\s\S])*)<\/\1>)/g,
          ),
        ].map(([, e, k, v]) => [
          k,
          v === undefined ? "" : e === "Data" ? tag(v, "value") : val(v),
        ]);
        return {
          type: "Feature",
          geometry: one(g),
          properties: {
            ...Object.fromEntries(x.map(([k, v]) => [ent(k), v?.trim()])),
            name: tag(b, "name")?.trim(),
            style: tag(b, "styleUrl")?.trim().replace(/^#/, ""),
            description:
              d === undefined ? undefined : cells.length ? cells : plain(d),
          },
        };
      },
    );
  },
  g: (t) => {
    const o = JSON.parse(JSON.parse(t).d);
    const v = new Map();
    for (const r of o.Table ?? []) {
      if (!v.has(r.Outageid)) v.set(r.Outageid, []);
      v.get(r.Outageid).push([r.Longitude, r.Latitude]);
    }
    return (o.Table1 ?? []).map((q) => {
      const r = shut([...(v.get(q.Outageid) ?? [])]);
      return {
        type: "Feature",
        geometry:
          r.length >= 4
            ? { type: "Polygon", coordinates: [r] }
            : pt(num(q.OutageLongitude), num(q.OutageLatitude)),
        properties: q,
      };
    });
  },
  h: (t, s) =>
    at(JSON.parse(t), s.r ?? "").map((a) => {
      const c = a.find(
        (x) =>
          typeof x === "string" &&
          /^\[\s*-?[\d.]+\s*,\s*-?[\d.]+\s*\]$/.test(x),
      );
      const [x, y] = c ? JSON.parse(c) : [];
      return {
        type: "Feature",
        geometry: pt(x, y),
        properties: Object.fromEntries(a.map((v, i) => [s.n?.[i] ?? i, v])),
      };
    }),
  k: (t, s) => (t == null ? crawl(s) : kf(t)),
  m: (t) => {
    const j = JSON.parse(t);
    return j.values.map((v, i) => ({
      type: "Feature",
      geometry: pt(
        j.origins[0] + j.xs[i] * j.scales[0],
        j.origins[1] + j.ys[i] * j.scales[1],
      ),
      properties: Object.fromEntries(j.fields.map((f, k) => [f, v[k]])),
    }));
  },
};

async function get(s, u = s.u, n = false) {
  let e;
  for (let i = 0; i < 3; i++) {
    try {
      const r = await fetch(u, {
        method: s.m ?? "GET",
        headers: {
          ...H,
          ...s.h,
          ...(s.b && { "content-type": "application/json; charset=utf-8" }),
        },
        body: s.b ? JSON.stringify(s.b) : undefined,
        signal: AbortSignal.timeout(60000),
      });
      if (n && (r.status === 403 || r.status === 404)) return null;
      if (!r.ok) throw new Error(`http ${r.status}`);
      return txt(Buffer.from(await r.arrayBuffer()));
    } catch (x) {
      e = x;
      if (i < 2) await sleep(5000 * (i + 1));
    }
  }
  throw e;
}

async function url(s) {
  if (!s.v) return s.u;
  const j = JSON.parse(await get({}, s.v));
  const u = s.u.replace(/\{([\w.]*)\}/g, (m, p) => {
    const x = at(j, p);
    return typeof x === "string" || typeof x === "number" ? x : m;
  });
  if (/\{\w*\.[\w.]*\}|\{\}/.test(u)) throw new Error("parse");
  return u;
}

// s.j: regex whose first group is the data inside a page, e.g. a JS string literal holding JSON
function pick(t, s) {
  if (!s.j) return t;
  const m = new RegExp(s.j).exec(t);
  if (!m) throw new Error("parse");
  return m[1].startsWith('"') ? JSON.parse(m[1]) : m[1];
}

// Geometry is normalized before writing so the same shape always serializes the same way:
// coordinates are rounded to 6 decimals (~10 cm), and polygons are rebuilt from their rings by
// containment, because ArcGIS alternates between one Polygon with several rings and a
// MultiPolygon for the same shape (each flip rewrote the whole geometry in git)
const r6 = (v) => Math.round(v * 1e6) / 1e6;
const xy = (p) => [r6(p[0]), r6(p[1])];
const nodup = (r) =>
  r.filter((p, i) => !i || p[0] !== r[i - 1][0] || p[1] !== r[i - 1][1]);
const area = (r) => {
  let a = 0;
  for (let i = 0, j = r.length - 1; i < r.length; j = i++)
    a += r[j][0] * r[i][1] - r[i][0] * r[j][1];
  return a / 2;
};
const inside = ([x, y], r) => {
  let c = false;
  for (let i = 0, j = r.length - 1; i < r.length; j = i++) {
    const [xi, yi] = r[i],
      [xj, yj] = r[j];
    if (yi > y !== yj > y && x < ((xj - xi) * (y - yi)) / (yj - yi) + xi) c = !c;
  }
  return c;
};
// outer rings counter-clockwise, holes clockwise (RFC 7946)
const orient = (r, ccw) => (area(r) > 0 === ccw ? r : [...r].reverse());
const order = (a, b) => b.a - a.a || (String(a.r[0]) < String(b.r[0]) ? -1 : 1);

function polys(rings) {
  const R = rings
    .map((r) => shut(nodup(r.map(xy))))
    .filter((r) => r.length >= 4)
    .map((r) => ({ r, a: Math.abs(area(r)), v: new Set(r.map(String)) }));
  // ring i is within ring j if one of its vertices not shared with j lies inside j
  const within = R.map((x, i) =>
    R.map((o, j) => {
      if (i === j || o.a <= x.a) return false;
      const p = x.r.find((q) => !o.v.has(String(q)));
      return p !== undefined && inside(p, o.r);
    }),
  );
  const depth = within.map((w) => w.filter(Boolean).length);
  const outer = R.map((x, i) => ({ ...x, i, holes: [] })).filter(
    (_, i) => depth[i] % 2 === 0,
  );
  R.forEach((x, i) => {
    if (depth[i] % 2 === 0) return;
    // a hole belongs to the smallest ring containing it, one level up
    const p = outer
      .filter((o) => within[i][o.i] && depth[o.i] === depth[i] - 1)
      .sort((a, b) => a.a - b.a)[0];
    p?.holes.push(x);
  });
  const c = outer
    .sort(order)
    .map((o) => [
      orient(o.r, true),
      ...o.holes.sort(order).map((h) => orient(h.r, false)),
    ]);
  return c.length === 0
    ? null
    : c.length === 1
      ? { type: "Polygon", coordinates: c[0] }
      : { type: "MultiPolygon", coordinates: c };
}

function geo(g) {
  switch (g?.type) {
    case "Point":
      return Array.isArray(g.coordinates)
        ? { type: "Point", coordinates: xy(g.coordinates) }
        : null;
    case "MultiPoint":
      return { type: g.type, coordinates: g.coordinates.map(xy) };
    case "LineString":
      return { type: g.type, coordinates: nodup(g.coordinates.map(xy)) };
    case "MultiLineString":
      return {
        type: g.type,
        coordinates: g.coordinates.map((l) => nodup(l.map(xy))),
      };
    case "Polygon":
      return polys(g.coordinates);
    case "MultiPolygon":
      return polys(g.coordinates.flat());
    case "GeometryCollection":
      return {
        type: g.type,
        geometries: g.geometries.map(geo).filter(Boolean),
      };
    default:
      return g ?? null;
  }
}

async function run(s) {
  const q = { ...s, u: await url(s) };
  const f = await P[s.t](q.u.includes("{q}") ? null : pick(await get(q), s), q);
  if (!Array.isArray(f)) throw new Error("parse");
  for (const x of f) for (const k of s.i ?? []) delete x.properties?.[k];
  for (const x of f) {
    if (!x) continue;
    // ArcGIS adds a feature-level `id` copying OBJECTID; it's outside `properties`, so `i` can't drop it
    delete x.id;
    x.geometry = geo(x.geometry);
  }
  const l = f.map(stable).map((j, i) => [f[i].properties?.[s.k], j]);
  l.sort((a, b) => cmp(a[0], b[0]) || (a[1] < b[1] ? -1 : a[1] > b[1] ? 1 : 0));
  const out = `{"type":"FeatureCollection","features":[\n${l.map((x) => x[1]).join(",\n")}\n]}\n`;
  await mkdir(dirname(s.o), { recursive: true });
  await writeFile(`${s.o}.tmp`, out);
  await rename(`${s.o}.tmp`, s.o);
  return f.length;
}

// logs are public: keep messages that can't contain a url or host (network errors only expose cause.code)
const why = (e) => {
  const m = e?.message ?? "";
  if (/^(http \d+|parse)$/.test(m)) return m;
  const c = e?.cause?.code ?? "";
  return `${/:\/\/|\w\.\w/.test(m) ? "" : m} ${c}`.trim();
};

const S = JSON.parse(process.env.S ?? "[]");
const R = await Promise.allSettled(S.map(run));
let bad = 0;
R.forEach((r, i) => {
  if (r.status === "fulfilled") console.log(`${S[i].o} ${r.value}`);
  else {
    bad++;
    console.log(
      `${S[i].o} fail ${r.reason?.name ?? ""} ${why(r.reason)}`.trim(),
    );
  }
});
// a few sources being down is normal; only fail the job when nothing worked
if (bad && bad === S.length) process.exitCode = 1;
