/* Genera los iconos a partir del sprite del juego:
   minerva.ico / minerva.png para el acceso directo de Windows y los de la app (icons/). */
const fs = require('fs'), zlib = require('zlib'), path = require('path');
require('./src/sprite.js');
const SP = globalThis.SPRITE, G = SP.grid('happy');
const hex = h => [parseInt(h.slice(1, 3), 16), parseInt(h.slice(3, 5), 16), parseInt(h.slice(5, 7), 16)];

/* o: frac = parte del lado que ocupa la lechuza · bg/bg2 = damero de fondo · edge = borde con esquinas transparentes */
function pixels(size, o) {
  const u = Math.max(1, Math.floor(size * o.frac / 24)), owl = 24 * u, off = Math.floor((size - owl) / 2);
  const b = o.edge ? Math.max(1, Math.floor(size / 20)) : 0, cell = Math.max(1, Math.round(size / 8));
  const rows = [];
  for (let y = 0; y < size; y++) {
    const row = [];
    for (let x = 0; x < size; x++) {
      const edgeX = x < b || x >= size - b, edgeY = y < b || y >= size - b;
      if (b && edgeX && edgeY) { row.push([0, 0, 0, 0]); continue; }
      let px = [...((Math.floor(x / cell) + Math.floor(y / cell)) % 2 ? o.bg2 : o.bg), 255];
      if (b && (edgeX || edgeY)) px = [...o.edge, 255];
      const ox = x - off, oy = y - off;
      if (ox >= 0 && ox < owl && oy >= 0 && oy < owl) {
        const c = G[Math.floor(oy / u)][Math.floor(ox / u)];
        if (c !== '.') px = [...hex(SP.PAL[c]), 255];
      }
      row.push(px);
    }
    rows.push(row);
  }
  return rows;
}
function crc(buf) {
  if (zlib.crc32) return zlib.crc32(buf) >>> 0;
  const t = [];
  for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; t[n] = c >>> 0; }
  let r = 0xffffffff;
  for (const v of buf) r = t[(r ^ v) & 255] ^ (r >>> 8);
  return (r ^ 0xffffffff) >>> 0;
}
function chunk(type, data) {
  const len = Buffer.alloc(4); len.writeUInt32BE(data.length);
  const td = Buffer.concat([Buffer.from(type), data]), c = Buffer.alloc(4); c.writeUInt32BE(crc(td));
  return Buffer.concat([len, td, c]);
}
function png(size, o) {
  const rows = pixels(size, o), raw = Buffer.concat(rows.map(r => Buffer.from([0, ...r.flat()])));
  const ihdr = Buffer.alloc(13); ihdr.writeUInt32BE(size, 0); ihdr.writeUInt32BE(size, 4); ihdr[8] = 8; ihdr[9] = 6;
  return Buffer.concat([Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]), chunk('IHDR', ihdr), chunk('IDAT', zlib.deflateSync(raw, { level: 9 })), chunk('IEND', Buffer.alloc(0))]);
}
function dib(size, o) {
  const rows = pixels(size, o), head = Buffer.alloc(40);
  head.writeUInt32LE(40, 0); head.writeInt32LE(size, 4); head.writeInt32LE(size * 2, 8); head.writeUInt16LE(1, 12); head.writeUInt16LE(32, 14);
  const xor = Buffer.from(rows.slice().reverse().flatMap(r => r.flatMap(p => [p[2], p[1], p[0], p[3]])));
  const stride = Math.floor((size + 31) / 32) * 4, and = Buffer.alloc(stride * size);
  rows.slice().reverse().forEach((r, y) => r.forEach((p, x) => { if (p[3] === 0) and[y * stride + (x >> 3)] |= 0x80 >> (x & 7); }));
  return Buffer.concat([head, xor, and]);
}

/* acceso directo de Windows */
const WIN = { frac: 0.86, bg: hex('#2f9950'), bg2: hex('#2f9950'), edge: hex('#1d1438') };
const imgs = [[16, dib(16, WIN)], [32, dib(32, WIN)], [48, dib(48, WIN)], [256, png(256, WIN)]];
const dir = Buffer.alloc(6 + 16 * imgs.length);
dir.writeUInt16LE(1, 2); dir.writeUInt16LE(imgs.length, 4);
let off = dir.length;
imgs.forEach(([s, d], i) => {
  const e = 6 + 16 * i;
  dir[e] = s % 256; dir[e + 1] = s % 256; dir.writeUInt16LE(1, e + 4); dir.writeUInt16LE(32, e + 6); dir.writeUInt32LE(d.length, e + 8); dir.writeUInt32LE(off, e + 12);
  off += d.length;
});
fs.writeFileSync(path.join(__dirname, 'minerva.ico'), Buffer.concat([dir, ...imgs.map(x => x[1])]));
fs.writeFileSync(path.join(__dirname, 'minerva.png'), png(256, WIN));

/* app del celular: fondo a sangre (el sistema recorta las esquinas); la «maskable» deja más margen */
const APP = { frac: 0.8, bg: hex('#33479e'), bg2: hex('#2c3e8c') };
const icons = path.join(__dirname, 'icons');
fs.mkdirSync(icons, { recursive: true });
fs.writeFileSync(path.join(icons, 'icon-192.png'), png(192, APP));
fs.writeFileSync(path.join(icons, 'icon-512.png'), png(512, APP));
fs.writeFileSync(path.join(icons, 'apple-touch-icon.png'), png(180, APP));
fs.writeFileSync(path.join(icons, 'maskable-512.png'), png(512, Object.assign({}, APP, { frac: 0.6 })));
console.log('iconos generados');
