const CACHE = 'mineirart-v1';
const SHELL = [
  '/mineirart-lagos/',
  '/mineirart-lagos/index.html',
  '/mineirart-lagos/css/style.css',
  '/mineirart-lagos/js/app.js',
  '/mineirart-lagos/img/logo.png',
  '/mineirart-lagos/manifest.json'
];

// Instala e faz cache do shell
self.addEventListener('install', e => {
  e.waitUntil(
    caches.open(CACHE).then(c => c.addAll(SHELL)).then(() => self.skipWaiting())
  );
});

// Remove caches antigos
self.addEventListener('activate', e => {
  e.waitUntil(
    caches.keys()
      .then(keys => Promise.all(keys.filter(k => k !== CACHE).map(k => caches.delete(k))))
      .then(() => self.clients.claim())
  );
});

// Cache-first para assets do shell, network-first para o resto
self.addEventListener('fetch', e => {
  const url = new URL(e.request.url);
  // Ignora requests não-GET e externos (Firebase, Google Fonts etc)
  if(e.request.method !== 'GET') return;
  if(url.origin !== location.origin) return;

  e.respondWith(
    caches.match(e.request).then(cached => {
      const network = fetch(e.request).then(res => {
        if(res.ok) caches.open(CACHE).then(c => c.put(e.request, res.clone()));
        return res;
      }).catch(() => cached);
      return cached || network;
    })
  );
});
