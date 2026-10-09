import { mkdir, rename, writeFile } from "node:fs/promises";
import { dirname } from "node:path";
import { brotliDecompressSync, gunzipSync, inflateRawSync } from "node:zlib";

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

function unproject(w) {
  if (!/^\s*PROJCS/.test(w)) return (x, y) => [x, y];
  const [, A, I] = /SPHEROID\["[^"]*",\s*([\d.]+),\s*([\d.]+)/.exec(w);
  const a = +A,
    f = 1 / +I,
    e2 = 2 * f - f * f,
    e = Math.sqrt(e2);
  const q = Object.fromEntries(
    [...w.matchAll(/PARAMETER\["([^"]+)",\s*(-?[\d.eE+-]+)\]/g)].map(
      ([, k, v]) => [k.toLowerCase(), +v],
    ),
  );
  const u = +[...w.matchAll(/UNIT\["[^"]*",\s*([\d.eE+-]+)/g)].at(-1)[1];
  const d = Math.PI / 180,
    k0 = q.scale_factor ?? 1,
    fe = q.false_easting ?? 0,
    fn = q.false_northing ?? 0,
    l0 = (q.central_meridian ?? q.longitude_of_origin ?? 0) * d,
    p0 = (q.latitude_of_origin ?? 0) * d;
  if (/Lambert_Conformal_Conic/i.test(w)) {
    const m = (p) => Math.cos(p) / Math.sqrt(1 - e2 * Math.sin(p) ** 2);
    const t = (p) =>
      Math.tan(Math.PI / 4 - p / 2) /
      ((1 - e * Math.sin(p)) / (1 + e * Math.sin(p))) ** (e / 2);
    const p1 = (q.standard_parallel_1 ?? q.latitude_of_origin) * d,
      p2 =
        (q.standard_parallel_2 ??
          q.standard_parallel_1 ??
          q.latitude_of_origin) * d;
    const n =
      Math.abs(p1 - p2) < 1e-12
        ? Math.sin(p1)
        : (Math.log(m(p1)) - Math.log(m(p2))) /
          (Math.log(t(p1)) - Math.log(t(p2)));
    const F = m(p1) / (n * t(p1) ** n),
      r0 = a * F * k0 * t(p0) ** n,
      s = Math.sign(n);
    return (x, y) => {
      const dx = (x - fe) * u,
        dy = r0 - (y - fn) * u;
      const r = s * Math.hypot(dx, dy),
        tp = (r / (a * F * k0)) ** (1 / n);
      let p = Math.PI / 2 - 2 * Math.atan(tp);
      for (let i = 0; i < 15; i++)
        p =
          Math.PI / 2 -
          2 *
            Math.atan(
              tp * ((1 - e * Math.sin(p)) / (1 + e * Math.sin(p))) ** (e / 2),
            );
      return [(Math.atan2(s * dx, s * dy) / n + l0) / d, p / d];
    };
  }
  if (/Transverse_Mercator/i.test(w)) {
    const ep2 = e2 / (1 - e2),
      M = (p) =>
        a *
        ((1 - e2 / 4 - (3 * e2 ** 2) / 64 - (5 * e2 ** 3) / 256) * p -
          ((3 * e2) / 8 + (3 * e2 ** 2) / 32 + (45 * e2 ** 3) / 1024) *
            Math.sin(2 * p) +
          ((15 * e2 ** 2) / 256 + (45 * e2 ** 3) / 1024) * Math.sin(4 * p) -
          ((35 * e2 ** 3) / 3072) * Math.sin(6 * p));
    const e1 = (1 - Math.sqrt(1 - e2)) / (1 + Math.sqrt(1 - e2));
    return (x, y) => {
      const mu =
        (M(p0) + ((y - fn) * u) / k0) /
        (a * (1 - e2 / 4 - (3 * e2 ** 2) / 64 - (5 * e2 ** 3) / 256));
      const p1 =
        mu +
        ((3 * e1) / 2 - (27 * e1 ** 3) / 32) * Math.sin(2 * mu) +
        ((21 * e1 ** 2) / 16 - (55 * e1 ** 4) / 32) * Math.sin(4 * mu) +
        ((151 * e1 ** 3) / 96) * Math.sin(6 * mu) +
        ((1097 * e1 ** 4) / 512) * Math.sin(8 * mu);
      const C = ep2 * Math.cos(p1) ** 2,
        T = Math.tan(p1) ** 2,
        N = a / Math.sqrt(1 - e2 * Math.sin(p1) ** 2),
        R = (a * (1 - e2)) / (1 - e2 * Math.sin(p1) ** 2) ** 1.5,
        D = ((x - fe) * u) / (N * k0);
      const p =
        p1 -
        ((N * Math.tan(p1)) / R) *
          (D ** 2 / 2 -
            ((5 + 3 * T + 10 * C - 4 * C ** 2 - 9 * ep2) * D ** 4) / 24 +
            ((61 + 90 * T + 298 * C + 45 * T ** 2 - 252 * ep2 - 3 * C ** 2) *
              D ** 6) /
              720);
      const l =
        l0 +
        (D -
          ((1 + 2 * T + C) * D ** 3) / 6 +
          ((5 - 2 * C + 28 * T - 3 * C ** 2 + 8 * ep2 + 24 * T ** 2) * D ** 5) /
            120) /
          Math.cos(p1);
      return [l / d, p / d];
    };
  }
  throw new Error("parse");
}

async function raw(s) {
  let e;
  for (let i = 0; i < 3; i++) {
    try {
      const r = await fetch(s.u, {
        headers: { ...H, ...s.h },
        signal: AbortSignal.timeout(60000),
      });
      if (!r.ok) throw new Error(`http ${r.status}`);
      return Buffer.from(await r.arrayBuffer());
    } catch (x) {
      e = x;
      if (i < 2) await sleep(5000 * (i + 1));
    }
  }
  throw e;
}

const vi = (a, p) => {
  let v = 0,
    m = 1,
    c;
  do {
    c = a[p.i++];
    v += (c & 127) * m;
    m *= 128;
  } while (c & 128);
  return v;
};
function pbf(a) {
  const p = { i: 0 },
    f = [];
  while (p.i < a.length) {
    const k = vi(a, p),
      w = k % 8,
      n = Math.floor(k / 8);
    if (w === 0) f.push([n, vi(a, p)]);
    else if (w === 2) {
      const l = vi(a, p);
      f.push([n, a.subarray(p.i, p.i + l)]);
      p.i += l;
    } else if (w === 1) {
      f.push([n, a.readDoubleLE(p.i)]);
      p.i += 8;
    } else if (w === 5) {
      f.push([n, a.readFloatLE(p.i)]);
      p.i += 4;
    } else throw new Error("parse");
  }
  return f;
}
const unz = (b, c) =>
  c === 2
    ? gunzipSync(b)
    : c === 3
      ? brotliDecompressSync(b)
      : c <= 1
        ? b
        : (() => {
            throw new Error("parse");
          })();
const clip = (r, e) => {
  for (const [i, lo] of [
    [0, true],
    [0, false],
    [1, true],
    [1, false],
  ]) {
    const v = lo ? 0 : e,
      ok = (p) => (lo ? p[i] >= v : p[i] <= v),
      o = [];
    for (let j = 0; j < r.length; j++) {
      const a = r[j],
        b = r[(j + 1) % r.length];
      if (ok(a)) o.push(a);
      if (ok(a) !== ok(b)) {
        const t = (v - a[i]) / (b[i] - a[i]),
          c = [a[0] + t * (b[0] - a[0]), a[1] + t * (b[1] - a[1])];
        c[i] = v;
        o.push(c);
      }
    }
    r = o;
  }
  return r;
};

const P = {
  a: (t) => {
    const j = JSON.parse(t);
    if (j.exceededTransferLimit || j.properties?.exceededTransferLimit)
      throw new Error("parse");
    return j.features;
  },
  b: (t, s) =>
    (at(JSON.parse(t), s.r ?? "") ?? (s.d ? [] : undefined)).map((o) => {
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
  n: async (t, s) => {
    const [c, b] = await Promise.all(
      ["config", "outage.bounds"].map(async (f) =>
        JSON.parse(
          (await get(s, s.u.replace(/summary\.json/, `${f}.json`), true)) ??
            "{}",
        ),
      ),
    );
    const [ox, oy] = c.mapSettings.boundaryExtent;
    const ll = ([x, y]) => [
      ((x + ox) / 6378137) * (180 / Math.PI),
      (2 * Math.atan(Math.exp((y + oy) / 6378137)) - Math.PI / 2) *
        (180 / Math.PI),
    ];
    const a = new Map();
    for (const o of b.outageBoundaries ?? []) {
      const r = shut((o.outageGeometry ?? []).map(ll));
      if (r.length < 4) continue;
      const k = String(o.outageId);
      if (!a.has(k)) a.set(k, []);
      a.get(k).push({ type: "Polygon", coordinates: [r] });
    }
    return JSON.parse(t).outages.map(({ x, y, ...q }) => ({
      type: "Feature",
      geometry: one([
        ...(a.get(String(q.id)) ?? []),
        ...(Number.isFinite(x) && Number.isFinite(y)
          ? [{ type: "Point", coordinates: ll([x, y]) }]
          : []),
      ]),
      properties: q,
    }));
  },
  p: async (t, s) => {
    const c = JSON.parse(
      await get({}, s.u.replace(/mPowerOMSAPI\.asmx.*$/, "Setup.json")),
    );
    const f = unproject(c.Outages?.Proj4Coordsys ?? c.Proj4Coordsys);
    return JSON.parse(JSON.parse(t).d).map(({ X, Y, ...q }) => ({
      type: "Feature",
      geometry: pt(...f(X, Y)),
      properties: q,
    }));
  },
  o: (t) => {
    const m = /mapOverlayData=eval\('\(([\s\S]*?)\)'\);/.exec(t);
    if (!m) throw new Error("parse");
    const j = JSON.parse(
      m[1].replace(/\\(u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|[\s\S])/g, (x, c) =>
        c.length > 2 && /^[ux]/.test(c)
          ? String.fromCharCode(parseInt(c.slice(1), 16))
          : ({ n: "\n", t: "\t", r: "\r" }[c] ?? c),
      ),
    );
    const f = [];
    for (const [k, l] of Object.entries(j)) {
      let c;
      for (const v of l) {
        if (v.vertice != null || !c) {
          const { lat, lon, vertice, hover, label, ...q } = v;
          const rows = [
            ...String(hover ?? "").matchAll(/<tr\b[^>]*>([\s\S]*?)<\/tr>/gi),
          ].map(([, r]) =>
            [...r.matchAll(/<td\b[^>]*>([\s\S]*?)<\/td>/gi)].map((d) =>
              plain(d[1]),
            ),
          );
          c = {
            p: [],
            q: {
              overlay: k,
              label: plain(String(label ?? "")),
              ...q,
              ...(rows.length
                ? Object.fromEntries(
                    rows
                      .filter((r) => r.length === 2)
                      .map(([a, b]) => [a.replace(/\s+/g, " "), b]),
                  )
                : { hover: plain(String(hover ?? "")) }),
            },
          };
          f.push(c);
        }
        c.p.push([v.lon, v.lat]);
      }
    }
    return f.map(({ p, q }) => ({
      type: "Feature",
      geometry:
        p.length >= 3
          ? { type: "Polygon", coordinates: [shut(p)] }
          : pt(p[0][0], p[0][1]),
      properties: q,
    }));
  },
  // Co-op association statewide outage map (`…/outages/details`, POST): one feature per county with
  // its total and per-co-op counts; geometry from the counties GeoJSON at `f`, matched on `county<id>`.
  d: async (t, s) => {
    const g = new Map();
    if (s.f)
      for (const x of JSON.parse((await get({}, s.f, true)) ?? "{}").features ?? [])
        g.set(String(x.id), x.geometry);
    const n = (v) => +String(v).replace(/,/g, "");
    return [
      ...(JSON.parse(t).DetailsByCountyAlpha ?? "").matchAll(
        /<dl\b[^>]*\bid="county([^"]+)"[^>]*>([\s\S]*?)<\/dl>/g,
      ),
    ].map(([, id, b]) => ({
      type: "Feature",
      geometry: g.get(id) ?? null,
      properties: {
        id,
        county: plain(tag(b, "dt") ?? ""),
        out: n(/([\d,]+)\s+member/.exec(b)?.[1]),
        coops: Object.fromEntries(
          [...b.matchAll(/<li\b[^>]*>([\s\S]*?)<\/li>/g)].map(([, l]) => {
            const m = /^([\s\S]*):\s*([\d,]+)$/.exec(plain(l));
            return m ? [m[1].trim(), n(m[2])] : [plain(l), null];
          }),
        ),
      },
    }));
  },
  // PMTiles v3 vector tileset (MVT): features of layer `r` in the zoom-`z` tiles. Polygons are
  // clipped to their tile and pieces with the same `k` merged; buffer copies of points dropped.
  u: Object.assign(
    async (t, s) => {
      const b = await raw(s),
        n = (o) => Number(b.readBigUInt64LE(o));
      if (b.toString("latin1", 0, 7) !== "PMTiles" || b[7] !== 3 || b[99] !== 1)
        throw new Error("parse");
      const T = [],
        z0 = (4 ** s.z - 1) / 3,
        D = n(56);
      const dir = (o, l) => {
        const a = unz(b.subarray(o, o + l), b[97]),
          p = { i: 0 },
          c = vi(a, p),
          e = [];
        let id = 0;
        for (let i = 0; i < c; i++) e.push({ id: (id += vi(a, p)) });
        for (const x of e) x.r = vi(a, p);
        for (const x of e) x.l = vi(a, p);
        e.forEach((x, i) => {
          const v = vi(a, p);
          x.o = v === 0 && i ? e[i - 1].o + e[i - 1].l : v - 1;
        });
        for (const x of e) if (x.r) T.push(x);
        else dir(n(40) + x.o, x.l);
      };
      dir(n(8), n(16));
      const G = new Map(),
        zz = (v) => (v % 2 ? -(v + 1) / 2 : v / 2);
      for (const x of T)
        for (let k = 0; k < x.r; k++) {
          let d = x.id + k - z0,
            tx = 0,
            ty = 0;
          if (d < 0 || d >= 4 ** s.z) continue;
          for (let m = 1; m < 2 ** s.z; m *= 2) {
            const rx = Math.floor(d / 2) % 2,
              ry = (d % 2) ^ rx;
            if (!ry) {
              if (rx) [tx, ty] = [m - 1 - tx, m - 1 - ty];
              [tx, ty] = [ty, tx];
            }
            tx += m * rx;
            ty += m * ry;
            d = Math.floor(d / 4);
          }
          for (const [f, L] of pbf(unz(b.subarray(D + x.o, D + x.o + x.l), b[98]))) {
            if (f !== 3) continue;
            const K = [],
              V = [],
              F = [];
            let nm,
              ex = 4096;
            for (const [g, v] of pbf(L)) {
              if (g === 1) nm = v.toString();
              else if (g === 2) F.push(v);
              else if (g === 3) K.push(v.toString());
              else if (g === 4) {
                const [[c, w]] = pbf(v);
                V.push(c === 1 ? w.toString() : c === 6 ? zz(w) : c === 7 ? !!w : w);
              } else if (g === 5) ex = v;
            }
            if (nm !== s.r) continue;
            const ll = ([px, py]) => {
              const X = (tx + px / ex) / 2 ** s.z,
                Y = (ty + py / ex) / 2 ** s.z;
              return [
                X * 360 - 180,
                (Math.atan(Math.sinh(Math.PI * (1 - 2 * Y))) * 180) / Math.PI,
              ];
            };
            for (const ft of F) {
              const q = {},
                c = [],
                R = [];
              let gt = 0,
                cur,
                cx = 0,
                cy = 0;
              for (const [g, v] of pbf(ft)) {
                if (g !== 2 && g !== 4) {
                  if (g === 3) gt = v;
                  continue;
                }
                const p = { i: 0 },
                  a = [];
                while (p.i < v.length) a.push(vi(v, p));
                if (g === 2)
                  for (let i = 0; i + 1 < a.length; i += 2) q[K[a[i]]] = V[a[i + 1]];
                else c.push(...a);
              }
              for (let i = 0; i < c.length; ) {
                const o = c[i] & 7,
                  m = c[i++] >> 3;
                if (o === 7) continue;
                for (let j = 0; j < m; j++) {
                  cx += zz(c[i++]);
                  cy += zz(c[i++]);
                  if (o === 1) R.push((cur = []));
                  cur.push([cx, cy]);
                }
              }
              const g =
                gt === 1
                  ? R.flat()
                      .filter((p) => p.every((v) => v >= 0 && v < ex))
                      .map((p) => ({ type: "Point", coordinates: ll(p) }))
                  : gt === 2
                    ? R.map((r) => ({ type: "LineString", coordinates: r.map(ll) }))
                    : R.map((r) => clip(r, ex))
                        .filter((r) => r.length >= 3)
                        .map((r) => ({ type: "Polygon", coordinates: [shut(r.map(ll))] }));
              if (!g.length) continue;
              const id = q[s.k] ?? {};
              if (!G.has(id)) G.set(id, { q, g: [] });
              G.get(id).g.push(...g);
            }
          }
        }
      return [...G.values()].map(({ q, g }) => ({
        type: "Feature",
        geometry: one(g),
        properties: q,
      }));
    },
    { raw: true },
  ),
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

function pick(t, s) {
  if (!s.j) return t;
  const m = new RegExp(s.j).exec(t);
  if (!m) throw new Error("parse");
  return m[1].startsWith('"') ? JSON.parse(m[1]) : m[1];
}

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
    if (yi > y !== yj > y && x < ((xj - xi) * (y - yi)) / (yj - yi) + xi)
      c = !c;
  }
  return c;
};
const orient = (r, ccw) => (area(r) > 0 === ccw ? r : [...r].reverse());
const order = (a, b) => b.a - a.a || (String(a.r[0]) < String(b.r[0]) ? -1 : 1);

function polys(rings) {
  const R = rings
    .map((r) => shut(nodup(r.map(xy))))
    .filter((r) => r.length >= 4)
    .map((r) => ({ r, a: Math.abs(area(r)), v: new Set(r.map(String)) }));
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
  if (s.c) q.h = { ...s.h, authorization: `Bearer ${(await get({}, s.c)).trim()}` };
  const f = await P[s.t](q.u.includes("{q}") || P[s.t]?.raw ? null : pick(await get(q), s), q);
  if (!Array.isArray(f)) throw new Error("parse");
  // q: drop rows whose property equals a listed value, e.g. {"status":["SCHEDULED"]}
  if (s.q)
    for (let j = f.length - 1; j >= 0; j--)
      if (Object.entries(s.q).some(([k, v]) => v.includes(f[j]?.properties?.[k]))) f.splice(j, 1);
  for (const x of f) for (const k of s.i ?? []) delete x.properties?.[k];
  for (const x of f) {
    if (!x) continue;
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
if (bad && bad === S.length) process.exitCode = 1;
