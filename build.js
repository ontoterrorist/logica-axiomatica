/* Une src/ en un solo archivo, index.html: el juego completo (fuentes y fondos incrustados, funciona sin internet).
   Es también la app instalable (GitHub Pages): junto al index.html salen manifest.webmanifest, sw.js e icons/. */
const fs = require('fs'), path = require('path'), crypto = require('crypto');
const src = f => fs.readFileSync(path.join(__dirname, 'src', f), 'utf8');

const TITLE = 'Lógica Axiomática', SHORT = 'Axiomática', CACHE = 'logica-axiomatica';
const DESC = 'Juego para aprender lógica formal con el cálculo axiomático de Hilbert: proposicional, primer orden, modal, intuicionista y paraconsistente, hasta los teoremas de Gödel.';

const FONTS = [['Jersey 20', 'jersey20.woff2'], ['VT323', 'vt323.woff2'], ['Press Start 2P', 'pressstart2p.woff2']];
const fontCss = FONTS.map(([name, file]) => {
  const b64 = fs.readFileSync(path.join(__dirname, 'src', 'fonts', file)).toString('base64');
  return `@font-face { font-family: '${name}'; font-style: normal; font-weight: 400; font-display: block; src: url(data:font/woff2;base64,${b64}) format('woff2'); }`;
}).join('\n');

/* fondos de los mundos (tools/fondos.py): src/bg/w<k>.png pasa a la variable --img-w<k> */
const bgDir = path.join(__dirname, 'src', 'bg');
const bgCss = !fs.existsSync(bgDir) ? '' : ':root {\n' + fs.readdirSync(bgDir).filter(f => /^w\d+\.png$/.test(f)).sort()
  .map(f => `  --img-${f.slice(0, -4)}: url(data:image/png;base64,${fs.readFileSync(path.join(bgDir, f)).toString('base64')});`).join('\n') + '\n}';

/* motor + contenido + interfaz */
const game = ['engine.js', 'validity.js', 'content.js', 'ui.js'].map(src).join('\n');
if (/<\/script/i.test(game)) throw new Error('el código contiene </script> y rompería la página');

const head = `<title>${TITLE}</title>
<meta name="description" content="${DESC}">
<meta name="theme-color" content="#12102a">
<link rel="manifest" href="manifest.webmanifest">
<link rel="icon" type="image/png" sizes="192x192" href="icons/icon-192.png">
<link rel="apple-touch-icon" href="icons/apple-touch-icon.png">
<meta name="mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-status-bar-style" content="black-translucent">
<meta name="apple-mobile-web-app-title" content="${TITLE}">`;
const reg = `<script>
if ('serviceWorker' in navigator && location.protocol.startsWith('http')) window.addEventListener('load', () => { navigator.serviceWorker.register('sw.js').catch(() => {}); });
</script>
</body>`;

const html = src('index.template.html')
  .replace('/*CSS*/', () => fontCss + '\n' + bgCss + '\n' + src('style.css'))
  .replace('/*COMMON*/', () => src('sprite.js') + '\n' + src('music.js'))
  .replace('/*GAME*/', () => game)
  .replace('<title>Lógica Axiomática</title>', () => head)
  .replace('</body>', () => reg);
if (!html.includes('manifest.webmanifest')) throw new Error('no se pudo insertar la cabecera de la app');
fs.writeFileSync(path.join(__dirname, 'index.html'), html);
console.log(`index.html ${Math.round(html.length / 1024)} KB`);

/* ---------- app instalable ---------- */
if (!fs.existsSync(path.join(__dirname, 'icons', 'icon-192.png'))) require('./mkico.js');   // los iconos de la app salen del sprite de Minerva
fs.writeFileSync(path.join(__dirname, 'manifest.webmanifest'), JSON.stringify({
  name: TITLE, short_name: SHORT, description: DESC, lang: 'es', dir: 'ltr',
  start_url: './', scope: './', display: 'standalone', display_override: ['fullscreen', 'standalone'], orientation: 'any',
  background_color: '#12102a', theme_color: '#12102a', categories: ['education', 'games'],
  icons: [
    { src: 'icons/icon-192.png', sizes: '192x192', type: 'image/png', purpose: 'any' },
    { src: 'icons/icon-512.png', sizes: '512x512', type: 'image/png', purpose: 'any' },
    { src: 'icons/maskable-512.png', sizes: '512x512', type: 'image/png', purpose: 'maskable' }
  ]
}, null, 2));
const version = crypto.createHash('sha1').update(html).digest('hex').slice(0, 10);
fs.writeFileSync(path.join(__dirname, 'sw.js'), `/* ${TITLE} — service worker: deja la app guardada en el teléfono para jugar sin conexión. */
const PREFIX = '${CACHE}-';
const CACHE = PREFIX + 'v2-${version}';
const SHELL = ['./', 'index.html', 'manifest.webmanifest', 'icons/icon-192.png', 'icons/icon-512.png', 'icons/maskable-512.png', 'icons/apple-touch-icon.png'];
/* al instalar se baja todo de la red, sin pasar por la copia HTTP del navegador */
self.addEventListener('install', e => {
  e.waitUntil(caches.open(CACHE).then(c => c.addAll(SHELL.map(u => new Request(u, { cache: 'reload' })))).then(() => self.skipWaiting()));
});
self.addEventListener('activate', e => {
  e.waitUntil(caches.keys().then(ks => Promise.all(ks.filter(k => k.startsWith(PREFIX) && k !== CACHE).map(k => caches.delete(k)))).then(() => self.clients.claim()));
});
self.addEventListener('fetch', e => {
  const req = e.request;
  if (req.method !== 'GET' || !req.url.startsWith(self.registration.scope)) return;
  e.respondWith(caches.open(CACHE).then(c => {
    const hit = () => c.match(req, { ignoreSearch: true });
    const net = opt => fetch(req.url, opt).then(res => { if (res && res.ok) c.put(req, res.clone()); return res; });
    /* la página: primero la red, para ver siempre la última versión; sin conexión o con red lenta, la copia guardada */
    if (req.mode === 'navigate') {
      const fresh = net({ cache: 'no-cache' });
      const slow = new Promise(r => setTimeout(r, 4000)).then(hit).then(h => h || fresh);
      return Promise.race([fresh, slow]).catch(() => hit());
    }
    return hit().then(h => h || net());
  }));
});
`);
fs.writeFileSync(path.join(__dirname, '.nojekyll'), '');
console.log('app instalable · versión ' + version);
module.exports = { html };
