// Mineirart Lagos — Service Worker PWA (corrigido)
const CACHE = 'mineirart-v2';

// Só cacheia assets estáticos locais
const STATIC = [
  '/mineirart-lagos/css/style.css',
  '/mineirart-lagos/img/logo.png'
];

self.addEventListener('install', e => {
  e.waitUntil(
    caches.open(CACHE)
      .then(c => c.addAll(STATIC))
      .then(() => self.skipWaiting())
  );
});

self.addEventListener('activate', e => {
  e.waitUntil(
    caches.keys()
      .then(keys => Promise.all(keys.filter(k => k !== CACHE).map(k => caches.delete(k))))
      .then(() => self.clients.claim())
  );
});

self.addEventListener('fetch', e => {
  const url = e.request.url;

  // NUNCA interceptar Firebase, Google APIs ou scripts do app
  if (
    url.includes('firebase') ||
    url.includes('googleapis') ||
    url.includes('gstatic') ||
    url.includes('firebaseapp') ||
    url.includes('firebaseio') ||
    url.includes('.js') ||
    url.includes('identitytoolkit')
  ) {
    return; // deixa o browser lidar normalmente
  }

  // Só cacheia CSS e imagens
  e.respondWith(
    caches.match(e.request).then(cached => {
      if (cached) return cached;
      return fetch(e.request).then(res => {
        if (res && res.status === 200) {
          const clone = res.clone();
          caches.open(CACHE).then(c => c.put(e.request, clone));
        }
        return res;
      });
    })
  );
});
