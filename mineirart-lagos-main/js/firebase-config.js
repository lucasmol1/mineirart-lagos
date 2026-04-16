// ════════════════════════════════════════════════════════
//  🔥 CONFIGURAÇÃO DO FIREBASE — Mineirart Lagos
// ════════════════════════════════════════════════════════
import { initializeApp } from "https://www.gstatic.com/firebasejs/10.12.0/firebase-app.js";
import { getAuth }       from "https://www.gstatic.com/firebasejs/10.12.0/firebase-auth.js";
import { getDatabase }   from "https://www.gstatic.com/firebasejs/10.12.0/firebase-database.js";

const firebaseConfig = {
  apiKey:            "AIzaSyC74x-5nNCKFkD1q4ntIa-OSN66k8p8Q5Y",
  authDomain:        "mineirart-lagos.firebaseapp.com",
  databaseURL:       "https://mineirart-lagos-default-rtdb.firebaseio.com",
  projectId:         "mineirart-lagos",
  storageBucket:     "mineirart-lagos.firebasestorage.app",
  messagingSenderId: "977839046071",
  appId:             "1:977839046071:web:a7aba72fb7d8b3ede2bc32"
};

export const app  = initializeApp(firebaseConfig);
export const auth = getAuth(app);
export const db   = getDatabase(app);
