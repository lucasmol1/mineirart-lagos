// ════════════════════════════════════════════════════════
//  Mineirart Lagos — App v4
//  - Canais removidos
//  - Fluxograma conectado com áreas (clicável)
//  - Proteções Firebase para evitar cobranças
// ════════════════════════════════════════════════════════
import { auth, db } from "./firebase-config.js";
import { signInWithEmailAndPassword, signOut, onAuthStateChanged } from "https://www.gstatic.com/firebasejs/10.12.0/firebase-auth.js";
import { ref, onValue, set, push, remove, get } from "https://www.gstatic.com/firebasejs/10.12.0/firebase-database.js";

// ── CONSTANTS ─────────────────────────────────────────────────────────────────
const STATUS   = {"a-fazer":{label:"A Fazer",color:"#7c6eff"},"em-andamento":{label:"Em Andamento",color:"#f0a832"},"concluido":{label:"Concluído",color:"#c8f04e"},"bloqueado":{label:"Bloqueado",color:"#ff6b6b"}};
const PRIORITY = {alta:{label:"Alta",color:"#ff6b6b"},media:{label:"Média",color:"#f0a832"},baixa:{label:"Baixa",color:"#c8f04e"}};
const AREA_COLORS=["#e8624a","#e8a84a","#c8e04a","#4ae89c","#4ac8e8","#4a7ee8","#a84ae8","#e84ab8","#c8f04e","#7c6eff"];
const NOTE_COLORS=["#c8f04e","#7c6eff","#4ac8e8","#f0a832","#ff6b6b","#4ae89c"];

// ── FIREBASE SAFETY LIMITS ────────────────────────────────────────────────────
// Spark plan: 1 GB storage, 10 GB/month download, 100 simultaneous connections
// These limits keep the app safely within the free tier for a team of up to ~30 people
const LIMITS = {
  MAX_TASKS:           500,
  MAX_AREAS:            30,  // áreas NUNCA removidas automaticamente
  MAX_NOTES:           200,
  MAX_AREA_NOTES:      100,
  MAX_AUDIT_LOGS:      400,  // inicia purga ao atingir 400
  MAX_PERSONAL_NOTES:   50,
  MAX_FLOW_NODES:       80,
  AUDIT_PURGE_KEEP:    300,  // preserva as 300 mais recentes
  TASK_PURGE_TARGET:   400, // após purga, mantém esse número
  MAX_ORG_NODES:        60,  // max blocos no organograma
};

// ── SECURITY — Rate limiting (prevent abuse / accidental overuse) ─────────────
const _writeCounts={};
function checkRateLimit(key, maxPerMin=60){
  const now=Date.now(), windowMs=60000;
  if(!_writeCounts[key]||now-_writeCounts[key].t>windowMs){
    _writeCounts[key]={t:now,n:0};
  }
  _writeCounts[key].n++;
  if(_writeCounts[key].n>maxPerMin){
    console.warn(`Rate limit hit: ${key} (${_writeCounts[key].n}/${maxPerMin} per min)`);
    return false;
  }
  return true;
}
function uid(){return Date.now().toString(36)+Math.random().toString(36).slice(2);}
function fmtDate(d){if(!d)return"—";const[y,m,day]=d.split("-");return`${day}/${m}/${y}`;}
function fmtTs(ts){if(!ts)return"";const d=new Date(ts);return`${d.toLocaleDateString("pt-BR")} ${d.toLocaleTimeString("pt-BR",{hour:"2-digit",minute:"2-digit"})}`;}
function initials(n){return(n||"?").split(" ").map(w=>w[0]).join("").toUpperCase().slice(0,2);}
function linkify(text){
  if(!text)return"";
  const escaped=esc(text);
  return escaped.replace(/(https?:\/\/[^\s<>"]+)/g,'<a href="$1" target="_blank" rel="noopener" style="color:#4ac8e8;text-decoration:underline;word-break:break-all" onclick="event.stopPropagation()">$1</a>');
}
function esc(s){return String(s||"").replace(/&/g,"&amp;").replace(/</g,"&lt;").replace(/>/g,"&gt;");}

function deadlineClass(d){if(!d)return null;const diff=new Date(d+"T23:59:59")-new Date();if(diff<=0)return null;if(diff<=10800000)return"warn-now";if(diff<=86400000)return"warn-1";if(diff<=172800000)return"warn-2";if(diff<=259200000)return"warn-3";return null;}
function deadlineBadge(d){const c=deadlineClass(d);if(!c)return"";const m={"warn-now":"⚠️ <3h","warn-1":"🔴 Amanhã","warn-2":"🟠 2 dias","warn-3":"🟡 3 dias"},mp={"warn-now":"wnow","warn-1":"w1","warn-2":"w2","warn-3":"w3"};return`<span class="deadline-badge ${mp[c]}">${m[c]}</span>`;}

// ── STATE ─────────────────────────────────────────────────────────────────────
let currentUser=null, currentProfile=null, isAdmin1=false;
let page="dashboard", activeAreaId=null, dropdownOpen=false;
let areas={}, tasks={}, notes={}, users={}, flowData={nodes:{},edges:{}}, orgData={nodes:{},edges:{}}, calEvents={};
let auditLog={}, personalNotes={}, pendingUsers={}, areaNotes={}, taskComments={};
let dragging=null, connecting=null, selEdge=null, mousePos={x:0,y:0};
let selectedNodes=new Set(), groupDragging=null, selBox=null, flowResizing=null;
let flowSelecting=false, flowSelStart={x:0,y:0}; // drag-to-select state
let flowSelectMode=false; // true = select mode, false = pan mode
let orgSelectMode=false;
let flowContainerExpanded={}; // {containerId: true/false}
let expandedAreas=new Set(); // sidebar subarea toggle
let areaNotesListeners={};
let alertsSent={}, calAlertsSent={};

// ── DB HELPERS ────────────────────────────────────────────────────────────────
const dbRef=p=>ref(db,p);
// ── UNDO SYSTEM ──────────────────────────────────────────────────────────────
const _undoStack=[]; // [{path, before, after}]
const MAX_UNDO=5;
let _undoInProgress=false;

async function _captureAndSet(p,v){
  if(_undoInProgress)return set(dbRef(p),v);
  // Capture current value before overwriting
  try{
    const snap=await get(dbRef(p));
    const before=snap.val();
    const entry=_undoStack[_undoStack.length-1];
    // Group rapid writes to same root path (e.g. drag x/y) into one undo step
    const rootPath=p.split("/").slice(0,3).join("/");
    if(entry&&entry.rootPath===rootPath&&Date.now()-entry.ts<800){
      // Update the "after" but keep the original "before"
      entry.ops.push({path:p,before,after:v});
    } else {
      if(_undoStack.length>=MAX_UNDO)_undoStack.shift();
      _undoStack.push({rootPath,ts:Date.now(),ops:[{path:p,before,after:v}]});
    }
  }catch(e){}
  return set(dbRef(p),v);
}

async function undoLastAction(){
  if(!_undoStack.length){toast("Nada para desfazer","error");return;}
  const entry=_undoStack.pop();
  _undoInProgress=true;
  // Restore all ops in reverse order
  const ops=[...entry.ops].reverse();
  for(const op of ops){
    if(op.before===null||op.before===undefined) await remove(dbRef(op.path));
    else await set(dbRef(op.path),op.before);
  }
  _undoInProgress=false;
  toast("↩ Ação desfeita","success");
}

function dbSet(p,v){
  const isPos=/\/(x|y|w|h)$/.test(p);
  if(!isPos&&!checkRateLimit("write",600))return Promise.resolve();
  return _captureAndSet(p,v);
}
function dbPush(p,v){return push(dbRef(p),v);}
function dbRemove(p){
  if(!checkRateLimit("write",600))return Promise.resolve();
  if(!_undoInProgress){
    // Capture before remove
    get(dbRef(p)).then(snap=>{
      const before=snap.val();
      if(before!==null){
        if(_undoStack.length>=MAX_UNDO)_undoStack.shift();
        _undoStack.push({rootPath:p,ts:Date.now(),ops:[{path:p,before,after:null}]});
      }
    }).catch(()=>{});
  }
  return remove(dbRef(p));
}
function dbListen(p,cb){
  onValue(dbRef(p),s=>cb(s.val()||{}),err=>{
    console.error(`Firebase permission denied: ${p}`,err.code,err.message);
    if(err.code==="PERMISSION_DENIED"){
      // Regras do Firebase incompatíveis com estrutura compartilhada do app.
      // Use: { "rules": { ".read": "auth != null", ".write": "auth != null" } }
      toast("Erro de permissão no Firebase — verifique as Security Rules","error");
    }
  });
}

// ── AUDIT ─────────────────────────────────────────────────────────────────────
async function logAction(action,detail){
  if(!currentProfile) return;
  // Auto-purge audit log if getting too large (protects storage)
  const logs=Object.entries(auditLog);
  if(logs.length>=LIMITS.MAX_AUDIT_LOGS){
    const sorted=logs.sort((a,b)=>new Date(a[1].ts)-new Date(b[1].ts));
    const toDelete=sorted.slice(0,logs.length-LIMITS.AUDIT_PURGE_KEEP);
    for(const[id] of toDelete) await dbRemove(`audit/${id}`);
  }
  await dbPush("audit",{action,detail,userId:currentUser.uid,userName:currentProfile.name,userEmail:currentProfile.email,ts:new Date().toISOString()});
}

// ── PURGA SEGURA DE TAREFAS (preserva fixadas e mantém áreas intactas) ────────
async function safePurgeTasks(){
  const all=Object.entries(tasks);
  if(all.length<LIMITS.MAX_TASKS) return false;
  // nunca remove tarefas fixadas — só as mais antigas não fixadas
  const unpinned=all.filter(([,t])=>!t.pinned).sort((a,b)=>new Date(a[1].createdAt)-new Date(b[1].createdAt));
  const removeCount=Math.max(1, all.length - LIMITS.TASK_PURGE_TARGET);
  const toDelete=unpinned.slice(0, removeCount);
  if(toDelete.length===0){toast("Todas as tarefas estão fixadas. Desfixe algumas para criar novas.","error");return false;}
  for(const[id] of toDelete) await dbRemove(`tasks/${id}`);
  await logAction("purga_tarefas",`${toDelete.length} tarefas antigas removidas (não fixadas). Áreas e fixadas preservadas.`);
  toast(`${toDelete.length} tarefas antigas removidas. Fixadas e áreas preservadas.`,"warning");
  return true;
}

// ── SIDEBAR RESIZE ────────────────────────────────────────────────────────────
function initSidebarResize(){
  const sidebar=document.querySelector(".sidebar"); if(!sidebar)return;
  if(sidebar.querySelector(".sidebar-resizer"))return; // já inicializado
  const resizer=document.createElement("div");
  resizer.className="sidebar-resizer";
  sidebar.appendChild(resizer);
  // Restaurar largura salva
  const saved=localStorage.getItem("sidebarWidth");
  if(saved){const w=parseInt(saved);sidebar.style.width=w+"px";if(w<72)sidebar.classList.add("collapsed");else sidebar.classList.remove("collapsed");}
  let startX=0,startW=0;
  resizer.addEventListener("mousedown",e=>{
    e.preventDefault();
    startX=e.clientX; startW=sidebar.getBoundingClientRect().width;
    resizer.classList.add("dragging");
    document.body.style.cursor="col-resize"; document.body.style.userSelect="none";
    function onMove(ev){
      const w=Math.max(52,Math.min(480,startW+(ev.clientX-startX)));
      sidebar.style.width=w+"px";
      w<72?sidebar.classList.add("collapsed"):sidebar.classList.remove("collapsed");
    }
    function onUp(){
      resizer.classList.remove("dragging");
      document.body.style.cursor=""; document.body.style.userSelect="";
      localStorage.setItem("sidebarWidth",Math.round(sidebar.getBoundingClientRect().width));
      document.removeEventListener("mousemove",onMove);
      document.removeEventListener("mouseup",onUp);
    }
    document.addEventListener("mousemove",onMove);
    document.addEventListener("mouseup",onUp);
  });
  // Duplo clique reseta para 220px
  resizer.addEventListener("dblclick",()=>{
    sidebar.style.width="220px"; sidebar.classList.remove("collapsed");
    localStorage.setItem("sidebarWidth","220");
  });
}

// ── LISTENERS ─────────────────────────────────────────────────────────────────
let listenersReady=0;
function checkReady(){listenersReady++;if(listenersReady>=10){document.getElementById("loader").style.display="none";document.getElementById("app").style.display="flex";render();startAlertWatcher();initSidebarResize();}}

function initListeners(){
  dbListen("areas", v=>{
    areas=v||{};
    // Subscribe to notes for each area
    Object.keys(areas).forEach(aId=>{
      if(!areaNotesListeners[aId]){
        areaNotesListeners[aId]=true;
        onValue(dbRef(`area_notes/${aId}`),s=>{areaNotes[aId]=s.val()||{};render();});
      }
    });
    checkReady(); render();
  });
  dbListen("tasks",        v=>{tasks=v||{};        checkReady(); render(); checkDeadlineAlerts();});
  dbListen("notes",        v=>{notes=v||{};        checkReady(); render();});
  dbListen("users",        v=>{users=v||{};        checkReady(); render();});
  dbListen("flow",         v=>{flowData=v||{nodes:{},edges:{}}; checkReady(); render();});
  dbListen("flow/stickies",v=>{flowStickies=v||{}; if(page==="fluxo")renderStickies();});
  dbListen("org/stickies", v=>{orgStickies=v||{}; if(page==="organograma")renderOrgStickies();});
  // Re-render when own profile changes (catches manageAreas grant)
  dbListen(`users/${currentUser?.uid||'__none__'}`, v=>{ if(v&&currentProfile){const hadMA=currentProfile.manageAreas; currentProfile={...currentProfile,...v}; if(!!v.manageAreas!==!!hadMA)render();}});
  dbListen("fyi_notes", v=>{fyiNotes=v||{}; render();});
  dbListen("audit",        v=>{auditLog=v||{};     checkReady(); render();});
  dbListen("pending_users",v=>{pendingUsers=v||{}; checkReady(); render();});
  dbListen("org",         v=>{orgData=v||{nodes:{},edges:{}}; checkReady(); render();});
  dbListen("cal_events",  v=>{calEvents=v||{}; checkReady(); render(); checkCalAlerts();});
  dbListen("freela_events",v=>{freelaEvents=v||{}; render();});
  dbListen("prosp_events",v=>{prospEvents=v||{}; render();});
  if(currentUser) onValue(dbRef(`personal_notes/${currentUser.uid}`),s=>{personalNotes=s.val()||{};render();});
  checkReady();
}

// ── AUTH ──────────────────────────────────────────────────────────────────────
// ── SECURITY GUARDS ──────────────────────────────────────────────────────────
// Rate limit: track write attempts per minute to avoid runaway loops
onAuthStateChanged(auth, async user=>{
  if(user){
    currentUser=user;
    const uSnap=await get(dbRef(`users/${user.uid}`));
    if(!uSnap.exists()){
      const pSnap=await get(dbRef(`pending_users/${user.uid}`));
      if(pSnap.exists()&&pSnap.val().status==="pending"){showPendingScreen();return;}
      const allSnap=await get(dbRef("users"));
      if(!allSnap.exists()){
        // First ever user → becomes Super Admin
        const p={name:user.displayName||user.email.split("@")[0],email:user.email,role:"admin1",permissions:[],createdAt:new Date().toISOString()};
        await dbSet(`users/${user.uid}`,p); currentProfile=p; isAdmin1=true;
        document.getElementById("login-screen").style.display="none";
        document.getElementById("loader").style.display="flex";
        initListeners();
      } else {
        await dbSet(`pending_users/${user.uid}`,{name:user.displayName||user.email.split("@")[0],email:user.email,status:"pending",requestedAt:new Date().toISOString()});
        showPendingScreen();
      }
      return;
    }
    currentProfile=uSnap.val(); isAdmin1=currentProfile.role==="admin1";
    document.getElementById("login-screen").style.display="none";
    document.getElementById("pending-screen").style.display="none";
    document.getElementById("loader").style.display="flex";
    initListeners();
  } else {
    currentUser=null; currentProfile=null; isAdmin1=false; listenersReady=0;
    ["loader","app","pending-screen"].forEach(id=>document.getElementById(id).style.display="none");
    document.getElementById("login-screen").style.display="flex";
  }
});

function showPendingScreen(){
  ["loader","login-screen","app"].forEach(id=>document.getElementById(id).style.display="none");
  document.getElementById("pending-screen").style.display="flex";
  document.getElementById("btn-pending-logout").onclick=()=>signOut(auth);
}

document.getElementById("btn-login").addEventListener("click",doLogin);
document.getElementById("login-password").addEventListener("keydown",e=>{if(e.key==="Enter")doLogin();});
async function doLogin(){
  const email=document.getElementById("login-email").value.trim(),pass=document.getElementById("login-password").value;
  document.getElementById("login-error").style.display="none";
  if(!email||!pass){showLoginError("Preencha e-mail e senha.");return;}
  document.getElementById("login-loading").style.display="block";
  document.getElementById("btn-login").disabled=true;
  try{await signInWithEmailAndPassword(auth,email,pass);}
  catch(e){
    document.getElementById("login-loading").style.display="none";
    document.getElementById("btn-login").disabled=false;
    showLoginError({"auth/user-not-found":"Usuário não encontrado.","auth/wrong-password":"Senha incorreta.","auth/invalid-email":"E-mail inválido.","auth/too-many-requests":"Muitas tentativas. Aguarde."}[e.code]||"Erro ao entrar.");
  }
}
function showLoginError(msg){const e=document.getElementById("login-error");e.textContent=msg;e.style.display="block";}

// ── HELPERS ───────────────────────────────────────────────────────────────────
function isAdmin(){return currentProfile?.role==="admin1"||currentProfile?.role==="admin";}
function canManageAreas(){return isAdmin()||!!currentProfile?.manageAreas;}
function visibleAreas(){
  const all=Object.entries(areas).map(([id,a])=>({id,...a}));
  if(isAdmin()) return all;
  // User sees area if directly permitted OR parent area is permitted
  const permitted=new Set(currentProfile?.permissions||[]);
  return all.filter(a=>permitted.has(a.id)||(a.parentId&&permitted.has(a.parentId)));
}

function nav(p,extra){
  // Resetar filtro de área do calendário ao sair
  if(page==="calendario"&&p!=="calendario") calAreaFilter=[];
  page=p;dropdownOpen=false;
  if(p==="area")activeAreaId=extra;
  // Fechar drawer mobile ao navegar
  const sidebar=document.querySelector(".sidebar");
  const overlay=document.getElementById("drawer-overlay");
  if(sidebar&&window.innerWidth<=768){
    sidebar.classList.remove("mobile-open");
    if(overlay)overlay.style.display="none";
  }
  render();
}

// ── ALERT WATCHER ─────────────────────────────────────────────────────────────
let alertInterval=null;
function startAlertWatcher(){alertInterval=setInterval(checkDeadlineAlerts,10*60*1000);setInterval(checkCalAlerts,60*60*1000);setTimeout(checkCalAlerts,3000);listenUserNotifs();}
async function checkDeadlineAlerts(){
  for(const[id,t]of Object.entries(tasks)){
    if(!t.date||t.status==="concluido")continue;
    const cls=deadlineClass(t.date);if(!cls)continue;
    const key=`${id}-${cls}`;if(alertsSent[key])continue;
    alertsSent[key]=true;
    if(t.resp){const found=Object.values(users).find(u=>u.name===t.resp);if(found?.email)await dbPush("email_queue",{to:found.email,subject:`[Mineirart] Prazo: ${t.title}`,body:`Olá ${t.resp},\n\nPrazo próximo!\nTarefa: ${t.title}\nPrazo: ${fmtDate(t.date)}\n\n— Mineirart Lagos`,sentAt:new Date().toISOString()});}
  }
}

// ── RENDER ────────────────────────────────────────────────────────────────────
function render(){
  if(!currentUser||!currentProfile)return;
  renderSidebar(); renderTopbar(); renderContent();
}

// ── SIDEBAR ───────────────────────────────────────────────────────────────────
function renderSidebar(){
  const sn=document.getElementById("sidenav"),sb=document.getElementById("sidebar-bottom");if(!sn||!sb)return;
  const myAreas=visibleAreas().map(a=>a.id);
  const urgentCount=Object.values(tasks).filter(t=>myAreas.includes(t.areaId)&&t.date&&t.status!=="concluido"&&["warn-now","warn-1"].includes(deadlineClass(t.date))).length;
  const pendingCount=Object.values(pendingUsers).filter(p=>p.status==="pending").length;
  function ni(p,icon,label,extra=""){return`<div class="nav-item ${page===p?"active":""}" data-nav="${p}"><span style="font-size:14px;margin-right:8px">${icon}</span><span style="flex:1">${label}</span>${extra}${page===p?'<span class="active-bar"></span>':""}</div>`;}
  // ── Build area tree HTML ──────────────────────────────────────────────────
  const allAreas=Object.entries(areas).map(([id,a])=>({id,...a}));
  const vis=visibleAreas().map(x=>x.id);
  const childrenOf=pid=>allAreas.filter(a=>a.parentId===pid);
  function areaItem(a,depth){
    const kids=childrenOf(a.id);
    // show if user has access to this area or any descendant
    const hasAccess=vis.includes(a.id)||kids.some(k=>vis.includes(k.id));
    if(!hasAccess)return"";
    const tc=Object.values(tasks).filter(t=>t.areaId===a.id&&t.status!=="concluido").length;
    const isExp=expandedAreas.has(a.id);
    const isCur=page==="area"&&activeAreaId===a.id;
    const indent=depth>0?`padding-left:${10+depth*14}px`:"";
    const arrow=kids.length
      ?`<span class="area-arrow" data-aid="${a.id}" style="font-size:9px;color:#7a7a8a;margin-right:5px;cursor:pointer;display:inline-block;transition:transform .15s;transform:${isExp?"rotate(90deg)":"rotate(0deg)"};flex-shrink:0">▶</span>`
      :`<span style="width:14px;display:inline-block;flex-shrink:0"></span>`;
    const addBtn=isAdmin()
      ?`<span class="area-add-sub" data-pid="${a.id}" title="Nova subárea" style="font-size:11px;color:#5a5a6a;cursor:pointer;margin-left:2px;flex-shrink:0;opacity:0;transition:opacity .1s">＋</span>`
      :"";
    let html=`<div class="nav-item area-row ${isCur?"active":""}" data-nav="area" data-id="${a.id}" draggable="true" style="${isCur?`color:${a.color}`:""};${indent}">`
      +`<span class="area-drag-handle" data-aid="${a.id}" title="Arrastar para reordenar" style="font-size:11px;color:#3a3a4a;cursor:grab;margin-right:4px;flex-shrink:0;user-select:none">⠿</span>`
      +arrow
      +`<span class="dot" style="background:${a.color};margin-right:6px;flex-shrink:0;width:8px;height:8px;border-radius:50%"></span>`
      +`<span style="flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:13px">${esc(a.name)}</span>`
      +(tc>0?`<span style="font-size:10px;color:#7a7a8a;margin-right:2px">(${tc})</span>`:"")
      +addBtn
      +(isCur?'<span class="active-bar"></span>':"")
      +"</div>";
    if(kids.length&&isExp) html+=kids.map(k=>areaItem(k,depth+1)).join("");
    return html;
  }
  const rootAreas=allAreas.filter(a=>!a.parentId).sort((a,b)=>(a.order||0)-(b.order||0));
  const areaTreeHtml=rootAreas.map(a=>areaItem(a,0)).join("");

  sn.innerHTML=`
    ${ni("dashboard","⬡","Dashboard")}
    ${ni("alertas","🔔","Alertas",urgentCount>0?`<span class="nav-alert-count">${urgentCount}</span>`:"")}
    ${ni("minhas-tarefas","📋","Minhas Tarefas")}
    ${ni("fluxo","⟆","Fluxograma")}
    ${ni("calendario","📅","Calendário")}
    ${ni("prospecção","🎯","Cal. Prospecção")}
    ${ni("organograma","🏢","Organograma")}
    ${ni("fyi","💡","FYI")}
    ${ni("notas-pessoais","📝","Rascunhos Pessoais")}
    ${(isAdmin()||currentProfile?.manageAreas)?ni("admin","⚙️","Administração",pendingCount>0?`<span class="nav-alert-count">${pendingCount}</span>`:""):""}
    ${ni("historico","🕵️","Histórico")}
    <div class="side-label">ÁREAS</div>
    ${areaTreeHtml}`;

  sb.innerHTML=isAdmin()?`<button id="btn-add-area" style="width:100%;padding:9px;border:1px dashed #2e2e3a;background:transparent;color:#7a7a8a;cursor:pointer;border-radius:8px;font-family:inherit;font-size:13px;transition:all .12s">+ Nova área raiz</button>`:"";

  // Nav click
  sn.querySelectorAll(".nav-item[data-nav]").forEach(el=>el.addEventListener("click",e=>{
    if(e.target.classList.contains("area-arrow")||e.target.classList.contains("area-add-sub"))return;
    if(e.target.classList.contains("area-drag-handle"))return;
    e.stopPropagation();
    const p=el.dataset.nav;p==="area"?nav("area",el.dataset.id):nav(p);
  }));
  // Toggle expand arrow
  sn.querySelectorAll(".area-arrow").forEach(arrow=>{
    arrow.addEventListener("click",e=>{
      e.stopPropagation();
      const aid=arrow.dataset.aid;
      expandedAreas.has(aid)?expandedAreas.delete(aid):expandedAreas.add(aid);
      renderSidebar();
    });
  });
  // Show ＋ on hover
  sn.querySelectorAll(".area-row").forEach(row=>{
    const btn=row.querySelector(".area-add-sub");if(!btn)return;
    row.addEventListener("mouseenter",()=>btn.style.opacity="1");
    row.addEventListener("mouseleave",()=>btn.style.opacity="0");
  });
  // Add subarea button
  sn.querySelectorAll(".area-add-sub").forEach(btn=>{
    btn.addEventListener("click",e=>{
      e.stopPropagation();
      openAreaModal(btn.dataset.pid);
    });
  });
  document.getElementById("btn-add-area")?.addEventListener("click",()=>openAreaModal(""));

  // ── Sidebar area drag-to-reorder ──
  let dragSrcAreaId=null;
  sn.querySelectorAll(".area-row[draggable]").forEach(row=>{
    row.addEventListener("dragstart",e=>{
      dragSrcAreaId=row.dataset.id;
      row.style.opacity="0.5";
      e.dataTransfer.effectAllowed="move";
    });
    row.addEventListener("dragend",e=>{row.style.opacity="1";dragSrcAreaId=null;});
    row.addEventListener("dragover",e=>{e.preventDefault();e.dataTransfer.dropEffect="move";row.style.background="#1e1e2a";});
    row.addEventListener("dragleave",e=>{row.style.background="";});
    row.addEventListener("drop",async e=>{
      e.preventDefault();row.style.background="";
      const targetId=row.dataset.id;
      if(!dragSrcAreaId||dragSrcAreaId===targetId)return;
      const rootIds=Object.entries(areas).filter(([id,a])=>!a.parentId).sort((a,b)=>(a[1].order||0)-(b[1].order||0)).map(([id])=>id);
      const si=rootIds.indexOf(dragSrcAreaId), ti=rootIds.indexOf(targetId);
      if(si<0||ti<0)return;
      rootIds.splice(si,1); rootIds.splice(ti,0,dragSrcAreaId);
      for(let i=0;i<rootIds.length;i++) await dbSet(`areas/${rootIds[i]}/order`,i);
    });
  });
}

// ── TOPBAR ────────────────────────────────────────────────────────────────────
function renderTopbar(){
  const tb=document.getElementById("topbar");if(!tb)return;
  const titles={dashboard:"Dashboard",fluxo:"Fluxograma",organograma:"Organograma",calendario:"Calendário",freela:"Calendário","prospecção":"Cal. Prospecção",fyi:"FYI","minhas-tarefas":"Minhas Tarefas","notas-pessoais":"Rascunhos Pessoais",alertas:"Alertas",admin:"Administração",historico:"Histórico de Ações"};
  const label=page==="area"?(areas[activeAreaId]?.name||"Área"):(titles[page]||"");
  tb.innerHTML=`<button id="hamburger-btn" aria-label="Menu">☰</button>
    <div class="topbar-title">${esc(label)}</div>
    <button id="btn-undo-topbar" title="Desfazer (Ctrl+Z)" onclick="undoLastAction()" style="background:none;border:1px solid #2e2e3a;border-radius:8px;color:#7a7a8a;cursor:pointer;padding:5px 10px;font-size:14px;flex-shrink:0;transition:all .12s" onmouseover="this.style.color='#c8f04e';this.style.borderColor='#c8f04e44'" onmouseout="this.style.color='#7a7a8a';this.style.borderColor='#2e2e3a'">↩</button>
    <div id="global-search-wrap" style="flex:1;max-width:320px;position:relative">
      <input id="global-search" placeholder="🔍 Buscar tarefas, áreas, responsáveis…" autocomplete="off"
        style="width:100%;box-sizing:border-box;background:#13131a;border:1px solid #2e2e3a;border-radius:20px;padding:7px 14px;color:#d0d0e0;font-family:'DM Sans',sans-serif;font-size:12px;outline:none;transition:border-color .15s"/>
      <div id="search-results" style="display:none;position:absolute;top:38px;left:0;right:0;background:#16161e;border:1px solid #2e2e3a;border-radius:10px;max-height:360px;overflow-y:auto;z-index:999;box-shadow:0 8px 24px rgba(0,0,0,.4)"></div>
    </div>
    <div style="position:relative">
      <div class="topbar-user" id="user-btn"><div class="user-avatar">${initials(currentProfile.name)}</div><span class="topbar-user-name">${esc(currentProfile.name)}</span><span style="font-size:10px;color:#c8f04e;margin-left:5px;font-weight:700">X/span><span style="font-size:11px;color:#7a7a8a;margin-left:2px">▾</span></div>
      ${dropdownOpen?`<div class="user-dropdown"><div style="padding:8px 12px;font-size:11px;color:#5a5a6a">${esc(currentProfile.email)}</div><div style="padding:2px 12px 8px;font-size:10px;color:#7a7a8a">${{"admin1":"👑 Super Admin","admin":"Admin","user":"Usuário"}[currentProfile.role]||""}</div><hr class="divider"/><div class="user-dropdown-item" id="dd-profile">Meu perfil</div><div class="user-dropdown-item danger" id="dd-logout">Sair</div></div>`:""}
    </div>
    </div>`;
  document.getElementById("user-btn").addEventListener("click",e=>{e.stopPropagation();dropdownOpen=!dropdownOpen;render();});

  // ── Hambúrguer mobile ──
  document.getElementById("hamburger-btn")?.addEventListener("click",e=>{
    e.stopPropagation();
    const sidebar=document.querySelector(".sidebar");
    const overlay=document.getElementById("drawer-overlay");
    if(!sidebar)return;
    const isOpen=sidebar.classList.contains("mobile-open");
    if(isOpen){
      sidebar.classList.remove("mobile-open");
      if(overlay)overlay.style.display="none";
    } else {
      sidebar.classList.add("mobile-open");
      if(overlay){overlay.style.display="block";}
    }
  });
  document.getElementById("drawer-overlay")?.addEventListener("click",()=>{
    document.querySelector(".sidebar")?.classList.remove("mobile-open");
    document.getElementById("drawer-overlay").style.display="none";
  });
  document.getElementById("dd-logout")?.addEventListener("click",()=>signOut(auth));
  document.getElementById("dd-profile")?.addEventListener("click",()=>{dropdownOpen=false;openProfileModal();});

  // ── Global search ──
  const searchInput=document.getElementById("global-search");
  const searchResults=document.getElementById("search-results");
  if(searchInput&&searchResults){
    searchInput.addEventListener("focus",()=>{if(searchInput.value.trim())searchResults.style.display="block";});
    searchInput.addEventListener("input",()=>{
      const q=searchInput.value.trim().toLowerCase();
      if(!q){searchResults.style.display="none";searchResults.innerHTML="";return;}
      const myAreaIds=visibleAreas().map(a=>a.id);
      const results=[];
      // Search tasks
      Object.entries(tasks).forEach(([id,t])=>{
        if(!myAreaIds.includes(t.areaId)&&!(Array.isArray(t.extraAreaIds)&&t.extraAreaIds.some(eid=>myAreaIds.includes(eid))))return;
        const resps=Array.isArray(t.resps)?t.resps:(t.resp?[t.resp]:[]);
        const area=areas[t.areaId];
        const match=(t.title||"").toLowerCase().includes(q)
          ||(t.desc||"").toLowerCase().includes(q)
          ||resps.some(r=>r.toLowerCase().includes(q))
          ||(area?.name||"").toLowerCase().includes(q);
        if(match)results.push({type:"task",id,t,area,resps});
      });
      // Search areas
      Object.entries(areas).forEach(([id,a])=>{
        if(!myAreaIds.includes(id))return;
        if((a.name||"").toLowerCase().includes(q))results.push({type:"area",id,a});
      });
      // Search FYI notes
      Object.entries(fyiNotes).forEach(([id,n])=>{
        if((n.title||"").toLowerCase().includes(q)||(n.body||"").toLowerCase().includes(q))
          results.push({type:"fyi",id,n});
      });
      if(!results.length){
        searchResults.innerHTML='<div style="padding:14px 16px;font-size:12px;color:#5a5a6a">Nenhum resultado para "'+esc(q)+'"</div>';
        searchResults.style.display="block"; return;
      }
      searchResults.innerHTML=results.slice(0,12).map(r=>{
        if(r.type==="task"){
          const st=STATUS[r.t.status],ar=r.area;
          return`<div class="search-result-item" data-type="task" data-id="${r.id}" style="padding:10px 14px;cursor:pointer;border-bottom:1px solid #1e1e28;display:flex;align-items:center;gap:10px">
            <span style="width:8px;height:8px;border-radius:50%;background:${st?.color||"#7a7a8a"};flex-shrink:0"></span>
            <div style="flex:1;min-width:0">
              <div style="font-size:13px;color:#d0d0e0;white-space:nowrap;overflow:hidden;text-overflow:ellipsis">${esc(r.t.title||"")}</div>
              <div style="font-size:11px;color:#5a5a6a;margin-top:2px">${ar?esc(ar.name):""}${r.resps.length?" · "+esc(r.resps.slice(0,2).join(", "))+(r.resps.length>2?" +"+( r.resps.length-2):""):""}</div>
            </div>
            <span style="font-size:10px;color:#5a5a6a;flex-shrink:0">${st?.label||""}</span>
          </div>`;
        }
        if(r.type==="area"){
          return`<div class="search-result-item" data-type="area" data-id="${r.id}" style="padding:10px 14px;cursor:pointer;border-bottom:1px solid #1e1e28;display:flex;align-items:center;gap:10px">
            <span style="width:8px;height:8px;border-radius:50%;background:${r.a.color};flex-shrink:0"></span>
            <div style="font-size:13px;color:#d0d0e0">${esc(r.a.name)}</div>
            <span style="font-size:10px;color:#5a5a6a;margin-left:auto">Área</span>
          </div>`;
        }
        if(r.type==="fyi"){
          return`<div class="search-result-item" data-type="fyi" data-id="${r.id}" style="padding:10px 14px;cursor:pointer;border-bottom:1px solid #1e1e28;display:flex;align-items:center;gap:10px">
            <span style="font-size:14px">💡</span>
            <div style="flex:1;min-width:0">
              <div style="font-size:13px;color:#d0d0e0;white-space:nowrap;overflow:hidden;text-overflow:ellipsis">${esc(r.n.title||"")}</div>
            </div>
            <span style="font-size:10px;color:#5a5a6a;flex-shrink:0">FYI</span>
          </div>`;
        }
        return"";
      }).join("");
      searchResults.style.display="block";
      // Wire clicks
      searchResults.querySelectorAll(".search-result-item").forEach(el=>{
        el.addEventListener("mouseenter",()=>el.style.background="#1e1e28");
        el.addEventListener("mouseleave",()=>el.style.background="");
        el.addEventListener("click",()=>{
          searchResults.style.display="none";
          searchInput.value="";
          if(el.dataset.type==="task") openDetailModal(el.dataset.id);
          else if(el.dataset.type==="area") nav("area",el.dataset.id);
          else if(el.dataset.type==="fyi") nav("fyi");
        });
      });
    });
    // Close on click outside
    document.addEventListener("click",e=>{
      if(!document.getElementById("global-search-wrap")?.contains(e.target))
        searchResults.style.display="none";
    });
  }
}
document.addEventListener("click",()=>{if(dropdownOpen){dropdownOpen=false;render();}});
document.addEventListener("keydown",e=>{
  if((e.ctrlKey||e.metaKey)&&e.key==="z"&&!e.shiftKey){
    const tag=document.activeElement?.tagName;
    if(tag==="INPUT"||tag==="TEXTAREA"||document.activeElement?.isContentEditable)return;
    e.preventDefault();
    undoLastAction();
  }
});
document.addEventListener("keydown",e=>{
  if((e.ctrlKey||e.metaKey)&&e.key==="z"&&!e.shiftKey){
    // Don't intercept if user is typing in an input/textarea
    const tag=document.activeElement?.tagName;
    if(tag==="INPUT"||tag==="TEXTAREA"||document.activeElement?.isContentEditable)return;
    e.preventDefault();
    undoLastAction();
  }
});

// ── CONTENT ROUTER ────────────────────────────────────────────────────────────
function renderContent(){
  const mc=document.getElementById("main-content");if(!mc)return;
  if(!window._myNotifs)window._myNotifs={};
  const map={dashboard:renderDashboard,area:renderAreaPage,fluxo:renderFlowPage,organograma:renderOrgPage,calendario:renderCalPage,freela:renderCalPage,"prospecção":renderProspPage,"minhas-tarefas":renderMyTasksPage,"notas-pessoais":renderPersonalNotesPage,fyi:renderFYIPage,alertas:renderAlertsPage,admin:renderAdminPage,historico:renderHistoricoPage};
  try{
    mc.innerHTML=(map[page]||renderDashboard)();
  }catch(err){
    console.error("renderContent error on page="+page+":", err);
    mc.innerHTML=`<div style="padding:40px;color:#ff6b6b;font-size:13px">Erro ao carregar: ${err.message}</div>`;
  }
  attachContentEvents();
}

// ── DASHBOARD ─────────────────────────────────────────────────────────────────
function renderDashboard(){
  const myAreas=visibleAreas(),myTasks=Object.values(tasks).filter(t=>myAreas.map(a=>a.id).includes(t.areaId));
  const stats=[["Total",myTasks.length,"#c8f04e"],["Em andamento",myTasks.filter(t=>t.status==="em-andamento").length,"#f0a832"],["Concluídos",myTasks.filter(t=>t.status==="concluido").length,"#4ae89c"],["Bloqueados",myTasks.filter(t=>t.status==="bloqueado").length,"#ff6b6b"]];
  const cards=myAreas.length===0
    ?`<div class="empty-state"><div style="font-size:48px;margin-bottom:12px">⬡</div><div class="empty-title">Nenhuma área disponível</div><div class="empty-sub">${isAdmin()?"Crie a primeira área pelo menu lateral":"Aguarde o administrador liberar seu acesso"}</div></div>`
    :`<div class="areas-grid">${myAreas.map(a=>{
        const at=Object.values(tasks).filter(t=>t.areaId===a.id);
        const chips=Object.entries(STATUS).map(([k,v])=>{const c=at.filter(t=>t.status===k).length;return c>0?`<span class="chip" style="background:${v.color}18;color:${v.color};border:1px solid ${v.color}30">${c} ${v.label}</span>`:""}).join("");
        return`<div class="area-card" style="border-top:3px solid ${a.color}">
          <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:10px">
            <div style="display:flex;align-items:center;gap:10px"><div class="dot" style="background:${a.color};width:12px;height:12px"></div><div style="font-family:'Syne',sans-serif;font-size:15px;font-weight:700">${esc(a.name)}</div></div>
            ${isAdmin()?`<div style="display:flex;gap:4px"><button class="icon-btn btn-edit-area" data-id="${a.id}" title="Editar área">✏</button><button class="icon-btn btn-del-area" data-id="${a.id}" title="Excluir área">✕</button></div>`:""}
          </div>
          <div style="min-height:22px;margin-bottom:12px;display:flex;gap:6px;flex-wrap:wrap">${chips||'<span style="font-size:12px;color:#5a5a6a">Nenhuma tarefa</span>'}</div>
          <div style="display:flex;gap:8px">
            <button class="btn-small btn-open-area" data-id="${a.id}" style="background:${a.color}22;color:${a.color};border:1px solid ${a.color}44">Ver tarefas →</button>
            <button class="btn-small btn-add-task-area" data-id="${a.id}" style="border:1px solid #2e2e3a;color:#7a7a8a">+ Tarefa</button>
          </div>
        </div>`;}).join("")}</div>`;
  return`<div class="page-header"><div><div class="page-title">Dashboard</div><div class="page-sub">Visão geral de todas as áreas</div></div></div>
    <div class="stats-row">${stats.map(([l,n,c])=>`<div class="stat-card"><div style="font-family:'Syne',sans-serif;font-size:32px;font-weight:800;color:${c};line-height:1">${n}</div><div style="font-size:11px;color:#7a7a8a;margin-top:4px">${l}</div></div>`).join("")}</div>
    ${cards}`;
}

// ── AREA PAGE ─────────────────────────────────────────────────────────────────
function renderAreaPage(){
  const area=areas[activeAreaId];if(!area)return`<div class="empty-state"><div class="empty-title">Área não encontrada</div></div>`;
  const myTasks=Object.entries(tasks).filter(([,t])=>t.areaId===activeAreaId).map(([id,t])=>({id,...t}));
  const cols=Object.entries(STATUS).map(([key,st])=>{
    const col=myTasks.filter(t=>t.status===key);
    const cards=col.length?col.map(t=>`<div class="card ${deadlineClass(t.date)||""}" data-detail="${t.id}" style="border-left-color:${st.color}">
      <div class="card-title">${esc(t.title)}</div>
      ${t.desc?`<div class="card-desc">${esc(t.desc)}</div>`:""}
      <div class="card-meta">
        ${t.priority?`<span class="chip" style="font-size:10px;font-weight:700;text-transform:uppercase;background:${PRIORITY[t.priority].color}18;color:${PRIORITY[t.priority].color};border:1px solid ${PRIORITY[t.priority].color}30">${t.priority}</span>`:""}
        ${deadlineBadge(t.date)}
        ${t.recurrence?`<span style="font-size:10px;color:#7c6eff;background:#7c6eff18;border:1px solid #7c6eff30;border-radius:4px;padding:2px 5px">🔁 ${({diaria:"Diária",semanal:"Semanal",quinzenal:"Quinzenal",mensal:"Mensal",anual:"Anual",custom:`${t.recurrence.interval||7}d`})[t.recurrence.freq]||"Recorr."}</span>`:""}
        ${t.date&&!deadlineClass(t.date)?`<span style="font-size:10px;color:#7a7a8a;margin-left:auto">${fmtDate(t.date)}</span>`:""}
      </div>
      <div style="display:flex;align-items:center;justify-content:space-between;margin-top:8px">
        <div style="display:flex;align-items:center;gap:4px">
          ${(()=>{
            const rs=Array.isArray(t.resps)?t.resps:(t.resp?[t.resp]:[]);
            const avatars=rs.slice(0,4).map(r=>{
              const u=Object.values(users).find(u=>u.name===r);
              const c=u?.color||"#7c6eff";
              return`<div title="${esc(r)} (Responsável)" style="width:24px;height:24px;border-radius:50%;background:${c};border:2px solid #13131a;display:flex;align-items:center;justify-content:center;font-size:9px;font-weight:700;color:#0c0c0f;margin-left:-6px;first-child:margin-left:0">${initials(r)}</div>`;
            }).join("");
            const more=rs.length>4?`<span style="font-size:10px;color:#7a7a8a;margin-left:4px">+${rs.length-4}</span>`:"";
            return rs.length?`<div style="display:flex;align-items:center;padding-left:6px">${avatars}${more}</div>`:"";
          })()}
        </div>
        ${t.creatorName?`<div title="Criado por ${esc(t.creatorName)}" style="display:flex;align-items:center;gap:4px">
          <span style="font-size:9px;color:#5a5a6a">por</span>
          <div style="width:20px;height:20px;border-radius:50%;background:${Object.values(users).find(u=>u.name===t.creatorName)?.color||"#4ac8e8"};display:flex;align-items:center;justify-content:center;font-size:8px;font-weight:700;color:#0c0c0f" title="${esc(t.creatorName)}">${initials(t.creatorName)}</div>
        </div>`:""}
      </div>
      ${Object.keys(taskComments[t.id]||{}).length>0?`<span style="font-size:10px;color:#7c6eff;background:#7c6eff18;border:1px solid #7c6eff33;border-radius:10px;padding:2px 7px">💬 ${Object.keys(taskComments[t.id]).length}</span>`:""}
    </div>`).join(""):`<div style="font-size:12px;color:#4a4a5a;text-align:center;padding:20px 8px">Vazio</div>`;
    return`<div class="column"><div class="col-header" style="border-bottom:2px solid ${st.color}35"><div class="dot" style="background:${st.color}"></div><div style="font-family:'Syne',sans-serif;font-size:12px;font-weight:700;color:${st.color};flex:1">${st.label}</div><div class="col-count">${col.length}</div></div><div class="cards-list">${cards}</div><button class="add-card-btn btn-add-task-col" data-status="${key}">+ Adicionar</button></div>`;
  }).join("");

  // ── Notes section for this area ── (block editor)
  const notesEditorHtml=renderAreaNotesEditor(activeAreaId);

  // Estado de colapso das colunas — persiste na sessão por área
  if(!areaCalCollapsed[activeAreaId]) areaCalCollapsed[activeAreaId]={};
  const colCollapsed=areaCalCollapsed[activeAreaId];

  =Object.entries(STATUS).map(([key,st])=>{
    const col=myTasks.filter(t=>t.status===key);
    const isCollapsed=!!colCollapsed[key];
    const cards=col.length?col.map(t=>`<div class="card ${deadlineClass(t.date)||""}" data-detail="${t.id}" style="border-left-color:${st.color}">
      <div class="card-title">${esc(t.title)}</div>
      ${t.desc?`<div class="card-desc">${esc(t.desc)}</div>`:""}
      <div class="card-meta">
        ${t.priority?`<span class="chip" style="font-size:10px;font-weight:700;text-transform:uppercase;background:${PRIORITY[t.priority].color}18;color:${PRIORITY[t.priority].color};border:1px solid ${PRIORITY[t.priority].color}30">${t.priority}</span>`:""}
        ${deadlineBadge(t.date)}
        ${t.recurrence?`<span style="font-size:10px;color:#7c6eff;background:#7c6eff18;border:1px solid #7c6eff30;border-radius:4px;padding:2px 5px">🔁 ${({diaria:"Diária",semanal:"Semanal",quinzenal:"Quinzenal",mensal:"Mensal",anual:"Anual",custom:`${t.recurrence.interval||7}d`})[t.recurrence.freq]||"Recorr."}</span>`:""}
        ${t.date&&!deadlineClass(t.date)?`<span style="font-size:10px;color:#7a7a8a;margin-left:auto">${fmtDate(t.date)}</span>`:""}
      </div>
      <div style="display:flex;align-items:center;justify-content:space-between;margin-top:8px">
        <div style="display:flex;align-items:center;gap:4px">
          ${(()=>{
            const rs=Array.isArray(t.resps)?t.resps:(t.resp?[t.resp]:[]);
            const avatars=rs.slice(0,4).map(r=>{
              const u=Object.values(users).find(u=>u.name===r);
              const c=u?.color||"#7c6eff";
              return`<div title="${esc(r)} (Responsável)" style="width:24px;height:24px;border-radius:50%;background:${c};border:2px solid #13131a;display:flex;align-items:center;justify-content:center;font-size:9px;font-weight:700;color:#0c0c0f;margin-left:-6px;first-child:margin-left:0">${initials(r)}</div>`;
            }).join("");
            const more=rs.length>4?`<span style="font-size:10px;color:#7a7a8a;margin-left:4px">+${rs.length-4}</span>`:"";
            return rs.length?`<div style="display:flex;align-items:center;padding-left:6px">${avatars}${more}</div>`:"";
          })()}
        </div>
        ${t.creatorName?`<div title="Criado por ${esc(t.creatorName)}" style="display:flex;align-items:center;gap:4px">
          <span style="font-size:9px;color:#5a5a6a">por</span>
          <div style="width:20px;height:20px;border-radius:50%;background:${Object.values(users).find(u=>u.name===t.creatorName)?.color||"#4ac8e8"};display:flex;align-items:center;justify-content:center;font-size:8px;font-weight:700;color:#0c0c0f" title="${esc(t.creatorName)}">${initials(t.creatorName)}</div>
        </div>`:""}
      </div>
      ${Object.keys(taskComments[t.id]||{}).length>0?`<span style="font-size:10px;color:#7c6eff;background:#7c6eff18;border:1px solid #7c6eff33;border-radius:10px;padding:2px 7px">💬 ${Object.keys(taskComments[t.id]).length}</span>`:""}
    </div>`).join(""):`<div style="font-size:12px;color:#4a4a5a;text-align:center;padding:20px 8px">Vazio</div>`;

    if(isCollapsed){
      // Coluna colapsada: só mostra cabeçalho vertical
      return`<div class="column" style="width:40px;min-width:40px;flex-shrink:0">
        <div class="col-header btn-toggle-col" data-colkey="${key}" style="border-bottom:2px solid ${st.color}35;cursor:pointer;flex-direction:column;height:auto;padding:10px 6px;gap:6px;justify-content:flex-start;align-items:center;min-height:80px" title="Expandir ${st.label}">
          <div class="dot" style="background:${st.color}"></div>
          <div style="font-family:'Syne',sans-serif;font-size:10px;font-weight:700;color:${st.color};writing-mode:vertical-rl;letter-spacing:1px">${st.label}</div>
          <div class="col-count">${col.length}</div>
        </div>
      </div>`;
    }

    return`<div class="column">
      <div class="col-header" style="border-bottom:2px solid ${st.color}35">
        <div class="dot" style="background:${st.color}"></div>
        <div style="font-family:'Syne',sans-serif;font-size:12px;font-weight:700;color:${st.color};flex:1">${st.label}</div>
        <div class="col-count">${col.length}</div>
        <button class="btn-toggle-col" data-colkey="${key}" title="Colapsar coluna" style="background:none;border:none;color:#3a3a4a;cursor:pointer;font-size:13px;padding:0 2px;line-height:1" onmouseover="this.style.color='${st.color}'" onmouseout="this.style.color='#3a3a4a'">◀</button>
      </div>
      <div class="cards-list">${cards}</div>
      <button class="add-card-btn btn-add-task-col" data-status="${key}">+ Adicionar</button>
    </div>`;
  }).join("");

  // ── Notes section for this area ── (block editor)
  const notesEditorHtml=renderAreaNotesEditor(activeAreaId);

  return`<div class="page-header">
    <div style="display:flex;align-items:center;gap:12px"><div class="dot" style="background:${area.color};width:14px;height:14px"></div><div><div style="display:flex;align-items:center;gap:8px"><div class="page-title">${esc(area.name)}</div>${isAdmin()?`<button class="icon-btn btn-edit-area" data-id="${activeAreaId}" title="Editar área" style="font-size:13px">✏</button>`:""}</div><div class="page-sub">${myTasks.length} tarefa${myTasks.length!==1?"s":""}</div></div></div>
    <div style="display:flex;gap:8px">
      <button class="btn-small" id="btn-export-area" style="border:1px solid #2e2e3a;color:#7a7a8a">⬇ Exportar</button>
      <button class="btn-primary" id="btn-add-task" style="background:${area.color};color:#0c0c0f">+ Nova tarefa</button>
    </div>
  </div>
  <div class="kanban">${cols}</div>

  <!-- Area details block -->
  <div style="margin:10px 0 4px 0;background:#13131a;border:1px solid #1e1e28;border-radius:8px;padding:10px 14px">
    <div style="display:flex;align-items:center;gap:8px;margin-bottom:4px">
      <div style="font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:.8px;color:#7a7a8a">Detalhes da área</div>
      ${isAdmin1?`<button class="btn-small" id="btn-save-area-detail" style="border:1px solid ${area.color}44;color:${area.color};font-size:10px;padding:2px 8px">Salvar</button>`:""}
    </div>
    ${isAdmin1
      ?`<textarea id="area-detail-text" rows="2" placeholder="Descrição, processos, informações relevantes…" style="width:100%;background:transparent;border:none;color:#a0a0b0;font-family:'DM Sans',sans-serif;font-size:12px;line-height:1.6;resize:vertical;outline:none">${esc(area.detail||"")}</textarea>`
      :`<div style="font-size:12px;color:#a0a0b0;line-height:1.6;min-height:18px">${esc(area.detail||"—")}</div>`}
  </div>

  ${notesEditorHtml}`;
}

// ── FLUXOGRAMA ────────────────────────────────────────────────────────────────
function renderFlowPage(){
  const allFlowNodes=Object.entries(flowData.nodes||{}).map(([id,n])=>({id,...n}));
  // Bloco-raiz: filhos só visíveis se o pai estiver expandido
  const nodes=allFlowNodes.filter(n=>{
    if(!n.flowParent)return true;
    return flowContainerExpanded[n.flowParent]===true;
  });
  const edges=Object.entries(flowData.edges||{}).map(([id,e])=>({id,...e}));
  const myAreas=visibleAreas();
  const nodeCount=nodes.length;

  // Fundo de grupo para blocos-raiz expandidos
  const svgContainers=allFlowNodes.filter(n=>n.type==="root"&&flowContainerExpanded[n.id]===true).map(c=>{
    const children=allFlowNodes.filter(n=>n.flowParent===c.id);
    if(!children.length)return"";
    const cColor=c.color||"#7c6eff";
    const xs=[c.x,...children.map(n=>n.x)];
    const ys=[c.y,...children.map(n=>n.y)];
    const ws=[c.w||150,...children.map(n=>n.w||150)];
    const hs=[c.h||48,...children.map(n=>n.h||48)];
    const bx=Math.min(...xs)-18, by=Math.min(...ys)-18;
    const br=Math.max(...xs.map((x,i)=>x+ws[i]))+18;
    const bb=Math.max(...ys.map((y,i)=>y+hs[i]))+18;
    return`<rect x="${bx}" y="${by}" width="${br-bx}" height="${bb-by}" rx="14" fill="${cColor}08" stroke="${cColor}30" stroke-width="1.5" stroke-dasharray="6,4" style="pointer-events:none"/>`;
  }).join("");

  // SVG group backgrounds (nodes that are parents of other nodes)
  const groupParents=new Map();
  nodes.forEach(n=>{if(n.groupParent){if(!groupParents.has(n.groupParent))groupParents.set(n.groupParent,[]);groupParents.get(n.groupParent).push(n);}});
  const svgGroups=Array.from(groupParents.entries()).map(([pid,kids])=>{
    const pn=nodes.find(n=>n.id===pid);if(!pn)return"";
    const allInGroup=[pn,...kids];
    const xs=allInGroup.map(n=>n.x); const ys=allInGroup.map(n=>n.y);
    const pW=pn.w||150, pH=pn.h||48;
    const ws=allInGroup.map(n=>n.w||150), hs=allInGroup.map(n=>n.h||48);
    const bx=Math.min(...xs)-16, by=Math.min(...ys)-16;
    const br=Math.max(...allInGroup.map((n,i)=>n.x+ws[i]))+16;
    const bb=Math.max(...allInGroup.map((n,i)=>n.y+hs[i]))+16;
    const bc2=pn.areaId&&areas[pn.areaId]?areas[pn.areaId].color:(pn.color||"#7c6eff");
    return`<rect x="${bx}" y="${by}" width="${br-bx}" height="${bb-by}" rx="14" fill="${bc2}08" stroke="${bc2}30" stroke-width="1.5" stroke-dasharray="6,4" style="pointer-events:none"/>
    <text x="${bx+10}" y="${by+14}" fill="${bc2}" font-size="10" font-family="DM Sans,sans-serif" style="pointer-events:none;opacity:.6">${esc(pn.label||"")}</text>`;
  }).join("");

  // SVG edges
  const svgEdges=edges.map(e=>{
    const fn=nodes.find(n=>n.id===e.from),tn=nodes.find(n=>n.id===e.to);if(!fn||!tn)return"";
    const fW=fn.w||150,fH=fn.h||48,tW=tn.w||150,tH=tn.h||48;
    const fs=e.fromSide||"right",ts=e.toSide||"left";
    const fx=fs==="right"?fn.x+fW:fs==="left"?fn.x:fn.x+fW/2;
    const fy=fs==="bottom"?fn.y+fH:fs==="top"?fn.y:fn.y+fH/2;
    const tx=ts==="right"?tn.x+tW:ts==="left"?tn.x:tn.x+tW/2;
    const ty=ts==="bottom"?tn.y+tH:ts==="top"?tn.y:tn.y+tH/2;
    const mx=(fx+tx)/2,my=(fy+ty)/2;
    const isSel=selEdge===e.id;
    const hasLabel=!!e.label, hasDetail=!!e.detail;
    const strokeColor=isSel?"#c8f04e":hasLabel||hasDetail?"#7c6eff":"#3e3e52";
    const markerSuffix=isSel?"Sel":hasLabel||hasDetail?"Det":"";
    const labelBg=hasLabel?`<rect x="${mx-46}" y="${my-11}" width="92" height="20" rx="5" fill="#13131a" stroke="${strokeColor}" stroke-width="1" style="pointer-events:none"/><text x="${mx}" y="${my}" text-anchor="middle" dominant-baseline="middle" fill="${strokeColor}" font-size="10" font-family="DM Sans,sans-serif" style="pointer-events:none">${esc(e.label.slice(0,18)+(e.label.length>18?"...":""))}</text>`:"";
    const detailDot=hasDetail&&!isSel?`<circle cx="${mx+(hasLabel?52:0)}" cy="${my-(hasLabel?0:0)}" r="4" fill="#7c6eff" style="pointer-events:none"/>`:"";
    const selBtns=isSel?`
      <rect x="${mx-52}" y="${my+14}" width="50" height="22" rx="5" fill="#ff6b6b18" stroke="#ff6b6b" stroke-width="1" class="del-edge" data-edge-id="${e.id}" style="cursor:pointer"/>
      <text x="${mx-27}" y="${my+25}" text-anchor="middle" dominant-baseline="middle" fill="#ff6b6b" font-size="10" font-family="DM Sans,sans-serif" style="pointer-events:none">Excluir</text>
      <rect x="${mx+4}" y="${my+14}" width="50" height="22" rx="5" fill="#7c6eff18" stroke="#7c6eff" stroke-width="1" class="edit-edge" data-edge-id="${e.id}" style="cursor:pointer"/>
      <text x="${mx+29}" y="${my+25}" text-anchor="middle" dominant-baseline="middle" fill="#9d93ff" font-size="10" font-family="DM Sans,sans-serif" style="pointer-events:none">Editar</text>
    `:"";
    return`<g>
      <path d="M${fx},${fy} C${fx+60},${fy} ${tx-60},${ty} ${tx},${ty}" fill="none" stroke="${strokeColor}" stroke-width="${isSel?2.5:1.8}" marker-end="url(#arrow${markerSuffix})" ${isSel?'stroke-dasharray="5,3"':""}/>
      <path d="M${fx},${fy} C${fx+60},${fy} ${tx-60},${ty} ${tx},${ty}" fill="none" stroke="transparent" stroke-width="20" class="edge-hit" data-edge-id="${e.id}" style="cursor:pointer"/>
      ${labelBg}${detailDot}${selBtns}
    </g>`;}).join("");

  // Live connecting line
  const liveEdge=(()=>{
    if(!connecting)return"";
    const fn=nodes.find(n=>n.id===connecting.fromId);if(!fn)return"";
    const W2=fn.w||150,H2=fn.h||48;
    const side=connecting.side||"right";
    const sx=side==="right"?fn.x+W2:side==="left"?fn.x:fn.x+W2/2;
    const sy=side==="bottom"?fn.y+H2:side==="top"?fn.y:fn.y+H2/2;
    return`<path d="M${sx},${sy} L${mousePos.x},${mousePos.y}" fill="none" stroke="#c8f04e" stroke-width="1.8" stroke-dasharray="6,3"/>`;
  })();

  // Build defs for multi-area gradients
  const flowGradDefs=nodes.filter(n=>Array.isArray(n.areaIds)&&n.areaIds.length>1).map(n=>{
    const colors=n.areaIds.map(aid=>areas[aid]?.color||"#7a7a8a");
    const stops=colors.map((c,i)=>{
      const p1=Math.round(i/colors.length*100), p2=Math.round((i+1)/colors.length*100);
      return`<stop offset="${p1}%" stop-color="${c}"/><stop offset="${p2}%" stop-color="${c}"/>`;
    }).join("");
    return`<linearGradient id="grad-${n.id}" x1="0%" y1="0%" x2="100%" y2="0%">${stops}</linearGradient>`;
  }).join("");

  // SVG nodes
  const svgNodes=nodes.map(n=>{
    const W=n.w||150, H=n.h||48;
    const fsize=n.fontSize||18, ffam="Syne";
    // Multi-area support
    const areaIdList=Array.isArray(n.areaIds)&&n.areaIds.length>0?n.areaIds:(n.areaId?[n.areaId]:[]);
    const hasArea=areaIdList.length>0&&areas[areaIdList[0]];
    const isMulti=areaIdList.length>1;
    const bc=hasArea?areas[areaIdList[0]].color:(n.color||"#c8f04e");
    const fillColor=isMulti?`url(#grad-${n.id})`:`${bc}20`;
    const strokeColor=isMulti?`url(#grad-${n.id})`:bc;
    const isSel=selectedNodes.has(n.id);
    const lblFull=n.label||"";
    const lbl=lblFull.length>28?lblFull.slice(0,26)+"…":lblFull;
    const detail=n.detail||"";
    const areaLabel=areaIdList.filter(id=>areas[id]).map(id=>areas[id].name.slice(0,10)).join(" · ");
    const shape=n.shape==="diamond"
      ?`<polygon points="${W/2},0 ${W},${H/2} ${W/2},${H} 0,${H/2}" fill="${fillColor}" stroke="${isSel?"#c8f04e":strokeColor}" stroke-width="${isSel?3:hasArea?2.5:1.5}"/>`
      :n.shape==="pill"
      ?`<rect x="0" y="0" width="${W}" height="${H}" rx="${H/2}" fill="${fillColor}" stroke="${isSel?"#c8f04e":strokeColor}" stroke-width="${isSel?3:1.5}"/>`
      :`<rect x="0" y="0" width="${W}" height="${H}" rx="10" fill="${fillColor}" stroke="${isSel?"#c8f04e":strokeColor}" stroke-width="${isSel?3:hasArea?2.5:1.5}"/>`;
    const textY=detail?(hasArea?H/2-14:H/2-8):(hasArea?H/2-9:H/2);
    const childCountFlow=allFlowNodes.filter(n=>n.flowParent===n.id).length;
    const isRootNode=n.type==="root";
    const isExpRoot=isRootNode&&flowContainerExpanded[n.id]===true;
    const expandBtnFlow=isRootNode?`
      <g class="flow-root-toggle" data-nid="${n.id}" style="cursor:pointer">
        <rect x="${W/2-22}" y="${H+4}" width="44" height="18" rx="9" fill="${isExpRoot?"#c8f04e22":"#1e1e28"}" stroke="${isExpRoot?"#c8f04e":"#3e3e52"}" stroke-width="1.2"/>
        <text x="${W/2}" y="${H+13}" text-anchor="middle" dominant-baseline="middle" fill="${isExpRoot?"#c8f04e":"#7a7a8a"}" font-size="9" font-family="DM Sans,sans-serif" style="pointer-events:none">${isExpRoot?`▲ ${childCountFlow}`:`▼ ${childCountFlow}`}</text>
      </g>`:"";
    const addChildBtnFlow=isAdmin1&&isRootNode?`
      <g class="flow-add-child" data-nid="${n.id}" style="cursor:pointer" title="Adicionar bloco filho">
        <circle cx="${W+12}" cy="${H+4}" r="9" fill="#c8f04e18" stroke="#c8f04e44" stroke-width="1.2"/>
        <text x="${W+12}" y="${H+4}" text-anchor="middle" dominant-baseline="middle" fill="#c8f04e" font-size="13" style="pointer-events:none">+</text>
      </g>`:"";
    return`<g class="flow-node${isRootNode?" flow-root-node":""}" data-node-id="${n.id}" data-area-id="${areaIdList[0]||""}" transform="translate(${n.x},${n.y})" style="cursor:${hasArea&&!connecting?"pointer":"grab"}">
      ${shape}
      <text x="${W/2}" y="${textY}" text-anchor="middle" dominant-baseline="middle" fill="#f0eff5" font-size="${fsize}" font-weight="700" font-family="${ffam},sans-serif" style="pointer-events:none;user-select:none">${esc(lbl)}</text>
      ${detail?`<text x="${W/2}" y="${textY+fsize+4}" text-anchor="middle" dominant-baseline="middle" fill="${bc}" font-size="${Math.max(9,fsize-4)}" font-weight="400" font-family="DM Sans,sans-serif" style="pointer-events:none;opacity:.85">${esc(detail.slice(0,28)+(detail.length>28?"…":""))}</text>`:""}
      ${hasArea?`<text x="${W/2}" y="${H-6}" text-anchor="middle" dominant-baseline="middle" fill="#f0eff5" font-size="9" font-weight="400" style="pointer-events:none;opacity:.7">↗ ${esc(areaLabel)}</text>`:""}
      ${expandBtnFlow}
      ${addChildBtnFlow}
      <!-- 4-side connection handles -->
      <circle cx="${W/2}" cy="0" r="6" fill="${connecting?.fromId===n.id?"#c8f04e":"#16161e"}" stroke="${bc}" stroke-width="1.5" class="conn-handle" data-node-id="${n.id}" data-side="top" style="cursor:crosshair"/>
      <circle cx="${W}" cy="${H/2}" r="6" fill="${connecting?.fromId===n.id?"#c8f04e":"#16161e"}" stroke="${bc}" stroke-width="1.5" class="conn-handle" data-node-id="${n.id}" data-side="right" style="cursor:crosshair"/>
      <circle cx="${W/2}" cy="${H}" r="6" fill="${connecting?.fromId===n.id?"#c8f04e":"#16161e"}" stroke="${bc}" stroke-width="1.5" class="conn-handle" data-node-id="${n.id}" data-side="bottom" style="cursor:crosshair"/>
      <circle cx="0" cy="${H/2}" r="6" fill="${connecting?.fromId===n.id?"#c8f04e":"#16161e"}" stroke="${bc}" stroke-width="1.5" class="conn-handle" data-node-id="${n.id}" data-side="left" style="cursor:crosshair"/>
      ${isAdmin1?`<circle cx="${W+4}" cy="-4" r="8" fill="#ff6b6b1a" stroke="#ff6b6b" stroke-width="1.2" class="del-node" data-node-id="${n.id}" style="cursor:pointer"/><text x="${W+4}" y="-4" text-anchor="middle" dominant-baseline="middle" fill="#ff6b6b" font-size="11" style="pointer-events:none">✕</text>`:""}
      ${isAdmin1?`<circle cx="-4" cy="${H+4}" r="8" fill="#7c6eff1a" stroke="#7c6eff" stroke-width="1.2" class="edit-flow-node" data-node-id="${n.id}" style="cursor:pointer"/><text x="-4" y="${H+4}" text-anchor="middle" dominant-baseline="middle" fill="#9d93ff" font-size="10" style="pointer-events:none">✏</text>`:""}
      <rect x="${W-6}" y="${H-6}" width="10" height="10" rx="2" fill="${bc}44" stroke="${bc}" stroke-width="1" class="flow-resize-handle" data-node-id="${n.id}" style="cursor:se-resize"/>
    </g>`;}).join("");

  const areaButtons=myAreas.map(a=>`<button class="btn-small btn-add-area-node" data-area-id="${a.id}" style="background:${a.color}22;color:${a.color};border:1px solid ${a.color}44;white-space:nowrap">+ ${esc(a.name)}</button>`).join("");

  const limitWarn=nodeCount>=LIMITS.MAX_FLOW_NODES?`<div style="background:rgba(240,168,50,.12);border:1px solid rgba(240,168,50,.3);color:#f0a832;padding:8px 14px;border-radius:8px;font-size:12px">⚠️ Limite de ${LIMITS.MAX_FLOW_NODES} blocos atingido.</div>`:"";

  return`
    <div class="page-header">
      <div><div class="page-title">Fluxograma</div><div class="page-sub">Conecte áreas e processos — clique num bloco de área para abrí-la</div></div>
      ${connecting?`<div class="connecting-hint">Clique em outro bloco para conectar <span id="cancel-connect" style="cursor:pointer;text-decoration:underline;margin-left:8px">cancelar</span></div>`:""}
    </div>
    ${limitWarn}
    ${isAdmin1?`
    <div style="display:flex;gap:10px;margin-bottom:14px;flex-wrap:wrap;align-items:flex-end">
      <div class="flow-toolbar">
        <input id="node-label" placeholder="Nome do bloco…" style="flex:1;min-width:120px;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none"/>
        <select id="node-shape" style="background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:12px;outline:none;width:116px">
          <option value="rect">Retângulo</option><option value="diamond">Decisão ◇</option><option value="pill">Pílula</option>
        </select>
        <input type="color" id="node-color" value="#c8f04e" style="width:32px;height:32px;border:none;background:none;cursor:pointer;border-radius:6px"/>
        <button class="btn-primary" id="btn-add-node" ${nodeCount>=LIMITS.MAX_FLOW_NODES?"disabled":""}>+ Bloco</button>
        <button class="btn-small" id="btn-add-sticky" style="border:1px solid #f0a83244;color:#f0a832;background:#f0a83212">📝 Nota</button>
        <button class="btn-small" id="btn-add-root-node" style="border:1px solid #7c6eff44;color:#9d93ff;background:#7c6eff12">🌿 Bloco Raiz</button>
        <button class="btn-small" id="btn-flow-select-mode" style="border:1px solid ${flowSelectMode?"#c8f04e":"#2e2e3a"};color:${flowSelectMode?"#c8f04e":"#7a7a8a"};background:${flowSelectMode?"#c8f04e12":"transparent"}">${flowSelectMode?"✅ Selecionar":"⬜ Selecionar"}</button>
      </div>
      ${areaButtons?`<div style="display:flex;gap:6px;flex-wrap:wrap">${areaButtons}</div>`:""}
    </div>`:""}
    <div class="flow-canvas" style="position:relative">
      <div id="stickies-layer" style="position:absolute;inset:0;pointer-events:none;z-index:10;overflow:hidden"></div>
      <svg id="flow-svg" width="100%" height="560" style="display:block;cursor:${connecting?"crosshair":flowSelectMode?"crosshair":"grab"}">
        <defs>
          ${flowGradDefs}
        <pattern id="grid" width="28" height="28" patternUnits="userSpaceOnUse">
            <path d="M28 0 L0 0 0 28" fill="none" stroke="#18182a" stroke-width="1"/>
          </pattern>
          <marker id="arrow" markerWidth="9" markerHeight="9" refX="7" refY="3.5" orient="auto">
            <path d="M0,0 L0,7 L9,3.5 z" fill="#5a5a6e"/>
          </marker>
          <marker id="arrowSel" markerWidth="9" markerHeight="9" refX="7" refY="3.5" orient="auto">
            <path d="M0,0 L0,7 L9,3.5 z" fill="#c8f04e"/>
          </marker>
          <marker id="arrowDet" markerWidth="9" markerHeight="9" refX="7" refY="3.5" orient="auto">
            <path d="M0,0 L0,7 L9,3.5 z" fill="#7c6eff"/>
          </marker>
        </defs>
        <rect width="100%" height="100%" fill="url(#grid)"/>
        <g id="flow-zoom-group" transform="translate(${flowPan.x},${flowPan.y}) scale(${flowZoom})">${svgContainers}${svgGroups}${svgEdges}${liveEdge}${svgNodes}${selBox?`<rect x="${Math.min(selBox.x1,selBox.x2)}" y="${Math.min(selBox.y1,selBox.y2)}" width="${Math.abs(selBox.x2-selBox.x1)}" height="${Math.abs(selBox.y2-selBox.y1)}" fill="#c8f04e08" stroke="#c8f04e" stroke-width="1" stroke-dasharray="5,3" style="pointer-events:none"/>`:""}</g>
        ${nodes.length===0?`<text x="50%" y="50%" text-anchor="middle" dominant-baseline="middle" fill="#2e2e42" font-size="15" font-family="DM Sans,sans-serif">Use os botões acima para adicionar blocos e conectar áreas</text>`:""}
      </svg>
    </div>
    ${selectedNodes.size>1?`
    <div id="flow-group-bar" style="margin-top:10px;background:#1a1a22;border:1px solid #c8f04e33;border-radius:10px;padding:10px 14px;display:flex;align-items:center;gap:12px;flex-wrap:wrap">
      <span style="font-size:12px;color:#c8f04e;font-weight:700">${selectedNodes.size} blocos selecionados</span>
      <span style="font-size:12px;color:#7a7a8a">Adicionar ao bloco raiz:</span>
      <select id="flow-group-parent" style="background:#13131a;border:1px solid #2e2e3a;border-radius:7px;padding:6px 10px;color:#f0eff5;font-family:inherit;font-size:12px;outline:none;min-width:160px">
        <option value="">— Escolher bloco raiz —</option>
        <option value="__remove__">✕ Remover de bloco raiz</option>
        ${nodes.filter(n=>n.type==="root"&&!selectedNodes.has(n.id)).map(n=>`<option value="${n.id}">🌿 ${esc(n.label||"?")}</option>`).join("")}
      </select>
      <button id="flow-group-apply" class="btn-primary" style="font-size:12px;padding:6px 14px">Aplicar</button>
      <button id="flow-group-clear" class="btn-ghost" style="font-size:12px;padding:6px 10px">Limpar seleção</button>
    </div>`:""}
    <div style="font-size:11px;color:#4a4a5a;margin-top:8px;display:flex;gap:20px;flex-wrap:wrap">
      <span>🖱 Arraste no fundo para mover a tela</span>
      <span>⬜ Botão "Selecionar" para selecionar vários blocos</span>
      <span>⭕ Círculo nas bordas para conectar blocos</span>
      <span>🔗 Clique na seta para editar/excluir</span>
      <span>📁 Blocos de área redirecionam ao clicar</span>
    </div>`;
}

// ── NOTES ─────────────────────────────────────────────────────────────────────
function renderNotesPage(){
  const noteList=Object.entries(notes).map(([id,n])=>({id,...n})).sort((a,b)=>new Date(b.createdAt)-new Date(a.createdAt));
  return`<div class="page-header"><div><div class="page-title">Notas</div><div class="page-sub">Referências para toda a equipe</div></div><button class="btn-primary" id="btn-add-note">+ Nova nota</button></div>
    ${noteList.length===0?`<div class="empty-state"><div style="font-size:40px;margin-bottom:12px">📌</div><div class="empty-title">Nenhuma nota ainda</div></div>`
    :`<div class="notes-grid">${noteList.map(n=>{
      const links=(n.links||[]).map(l=>`<a class="note-link" href="${esc(l.url)}" target="_blank" rel="noopener">🔗 ${esc(l.label||l.url)}</a>`).join("");
      const uColor=Object.values(users).find(u=>u.name===n.authorName)?.color||"#7c6eff";
      const avatar=n.authorName?`<div title="${esc(n.authorName)}" style="width:22px;height:22px;border-radius:50%;background:${uColor};display:flex;align-items:center;justify-content:center;font-size:9px;font-weight:700;color:#0c0c0f;flex-shrink:0">${initials(n.authorName)}</div>`:"";
      return`<div class="note-card">${n.tag?`<span class="note-tag" style="background:${n.color||"#c8f04e"}18;color:${n.color||"#c8f04e"};border:1px solid ${n.color||"#c8f04e"}30">${esc(n.tag)}</span>`:""}
        <div style="display:flex;align-items:flex-start;justify-content:space-between;gap:8px;margin-bottom:8px"><div class="note-title">${esc(n.title)}</div><div style="display:flex;align-items:center;gap:6px">${avatar}${isAdmin()||n.authorId===currentUser?.uid?`<button class="icon-btn btn-edit-note" data-id="${n.id}">✏</button><button class="icon-btn btn-del-note" data-id="${n.id}">✕</button>`:""}</div></div>
        ${n.body?`<div class="note-body">${esc(n.body)}</div>`:""}${links?`<div class="note-links">${links}</div>`:""}
      </div>`;}).join("")}</div>`}`;
}

function renderPersonalNotesPage(){
  return`<div class="page-header"><div><div class="page-title">Rascunhos Pessoais</div><div class="page-sub">🔒 Privado — só você vê</div></div></div>
    ${renderPersonalNotesEditor()}`;
}

function renderPersonalNotesEditor(){
  const uid2=currentUser?.uid; if(!uid2)return"";
  const doc=Object.values(personalNotes)[0];
  const docId=doc?.id||null;
  const blocks=doc?.blocks||[];

  function renderBlock(b){
    const color=b.color||"#d0d0e0";
    if(b.type==="image"){
      return`<div class="note-block pnote-block" data-bid="${b.id}" style="display:flex;align-items:flex-start;gap:8px;padding:4px 0">
        <div class="block-handle pblock-handle" data-bid="${b.id}" title="Opções" style="width:18px;height:18px;display:flex;align-items:center;justify-content:center;border-radius:4px;cursor:pointer;color:#3a3a4a;font-size:14px;flex-shrink:0;margin-top:4px">⋮</div>
        <img src="${b.data}" style="max-width:${b.w||220}px;max-height:200px;border-radius:6px;border:1px solid #2e2e3a;cursor:pointer" onclick="openImgModal(this.src)"/>
        <button class="pblock-del" data-bid="${b.id}" style="opacity:0;width:18px;height:18px;border:none;background:none;color:#ff6b6b;cursor:pointer;font-size:14px;padding:0;flex-shrink:0;margin-top:4px;transition:opacity .15s">✕</button>
      </div>`;
    }
    if(b.type==="toggle"){
      const isOpen=b.open!==false;
      const children=(b.children||[]);
      const childrenHtml=children.map(c=>`<div style="display:flex;align-items:center;gap:8px;padding:3px 0;margin-left:28px">
        <span contenteditable="true" data-bid="${b.id}" data-cid="${c.id}" class="ptoggle-child-text" spellcheck="false" style="flex:1;font-size:13px;color:${c.color||"#a0a0b0"};outline:none;word-break:break-word;line-height:1.6;min-height:16px">${esc(c.text||"")}</span>
        <button class="ptoggle-child-del" data-bid="${b.id}" data-cid="${c.id}" style="opacity:0;background:none;border:none;color:#ff6b6b;cursor:pointer;font-size:13px;padding:0;transition:opacity .15s">✕</button>
      </div>`).join("");
      const childInput=isOpen?`<div style="margin-left:28px;margin-top:4px">
        <input class="ptoggle-add-child" data-bid="${b.id}" placeholder="Adicionar item…" style="width:100%;box-sizing:border-box;background:transparent;border:none;border-bottom:1px dashed #2e2e3a;color:#7a7a8a;font-family:'DM Sans',sans-serif;font-size:12px;padding:4px 2px;outline:none"/>
      </div>`:"";
      return`<div class="note-block pnote-block" data-bid="${b.id}" style="padding:4px 0;border-radius:6px">
        <div style="display:flex;align-items:center;gap:6px">
          <div class="block-handle pblock-handle" data-bid="${b.id}" style="width:20px;min-width:20px;height:20px;display:flex;align-items:center;justify-content:center;border-radius:4px;cursor:pointer;color:#3a3a4a;font-size:15px">⋮</div>
          <span class="ptoggle-arrow" data-bid="${b.id}" style="font-size:11px;color:#7a7a8a;cursor:pointer;user-select:none;display:inline-block;transform:${isOpen?"rotate(90deg)":"rotate(0deg)"};width:16px;text-align:center">▶</span>
          <span contenteditable="true" data-bid="${b.id}" class="pblock-text" spellcheck="false" style="flex:1;font-size:13px;font-weight:600;color:${color};outline:none;word-break:break-word;line-height:1.7;min-height:18px">${esc(b.text||"")}</span>
          <button class="pblock-del" data-bid="${b.id}" style="opacity:0;background:none;border:none;color:#ff6b6b;cursor:pointer;font-size:15px;padding:0;transition:opacity .15s">✕</button>
        </div>
        <div class="ptoggle-body" data-bid="${b.id}" style="display:${isOpen?"block":"none"};margin-top:4px;padding-left:4px;border-left:2px solid ${color}44">
          ${childrenHtml}
          ${childInput}
        </div>
      </div>`;
    }
    return`<div class="note-block pnote-block" data-bid="${b.id}" style="display:flex;align-items:center;gap:8px;padding:4px 0">
      <div class="block-handle pblock-handle" data-bid="${b.id}" title="Opções" style="width:18px;height:18px;display:flex;align-items:center;justify-content:center;border-radius:4px;cursor:pointer;color:#3a3a4a;font-size:14px;flex-shrink:0">⋮</div>
      <span contenteditable="true" data-bid="${b.id}" class="pblock-text" spellcheck="false" style="flex:1;font-size:13px;color:${color};outline:none;min-width:0;word-break:break-word;line-height:1.6">${esc(b.text||"")}</span>
      <button class="pblock-del" data-bid="${b.id}" style="opacity:0;width:18px;height:18px;border:none;background:none;color:#ff6b6b;cursor:pointer;font-size:14px;padding:0;flex-shrink:0;transition:opacity .15s">✕</button>
    </div>`;
  }

  const blocksHtml=blocks.length
    ?blocks.map(b=>renderBlock(b)).join("")
    :`<div style="font-size:13px;color:#3a3a4a;padding:8px 0">Nenhuma linha ainda. Digite abaixo para começar…</div>`;

  return`<div style="background:#13131a;border:1px solid #1e1e28;border-radius:12px;padding:18px 20px" id="pnotes-editor-wrap">
    <div style="font-size:11px;color:#4a4a5a;margin-bottom:10px">Botão <strong style="color:#6a6a7a">⋮</strong> para toggle, cor e excluir · Cole imagem com Ctrl+V</div>
    <div id="pblocks-list">${blocksHtml}</div>
    <div style="display:flex;gap:8px;margin-top:12px;padding-top:10px;border-top:1px solid #1a1a22">
      <input id="pnew-block-input" placeholder="Nova linha… (Enter para adicionar)" style="width:100%;box-sizing:border-box;background:#0e0e14;border:1px solid #1e1e28;border-radius:7px;padding:8px 12px;color:#d0d0e0;font-family:'DM Sans',sans-serif;font-size:13px;outline:none;transition:border-color .15s"/>
    </div>
  </div>`;
}

// ── ALERTS ────────────────────────────────────────────────────────────────────
// ── FYI PAGE ──────────────────────────────────────────────────────────────────
function renderFYIPage(){
  const notes=Object.entries(fyiNotes).map(([id,n])=>({id,...n}))
    .filter(n=>!n.areaId) // global FYI only (area FYIs have areaId)
    .sort((a,b)=>(a.order||0)-(b.order||0)||(new Date(b.createdAt)-new Date(a.createdAt)));
  const noteCards=notes.map(n=>{
    const color=n.color||"#c8f04e";
    const syncBadge=n.syncCal?`<span style="font-size:10px;background:#7c6eff22;color:#9d93ff;border:1px solid #7c6eff44;border-radius:10px;padding:1px 7px">📅 no calendário</span>`:"";
    return`<div class="fyi-card" draggable="true" data-fyi-id="${n.id}" style="background:${color}10;border:1.5px solid ${color}33;border-radius:10px;padding:14px 16px;margin-bottom:12px;position:relative;cursor:grab" data-fyi-open="${n.id}">
      <div style="display:flex;align-items:flex-start;justify-content:space-between;gap:8px;margin-bottom:8px">
        <div style="font-size:14px;font-weight:700;color:#f0eff5;font-family:'Syne',sans-serif">${esc(n.title||"")}</div>
        <div style="display:flex;gap:6px;flex-shrink:0">
          ${syncBadge}
          ${n.authorId===currentUser?.uid||isAdmin1?`<button class="btn-fyi-edit" data-id="${n.id}" style="background:none;border:none;color:#7a7a8a;cursor:pointer;font-size:13px;padding:2px 5px">✏</button><button class="btn-fyi-del" data-id="${n.id}" style="background:none;border:none;color:#ff6b6b;cursor:pointer;font-size:13px;padding:2px 5px">✕</button>`:""}
        </div>
      </div>
      ${n.body?`<div style="font-size:13px;color:#a0a0b0;line-height:1.7;white-space:pre-wrap">${esc(n.body)}</div>`:""}
      ${n.syncCal&&n.date?`<div style="margin-top:8px;font-size:11px;color:#7c6eff">📅 ${fmtDate(n.date)}</div>`:""}
      <div style="margin-top:8px;font-size:10px;color:#3a3a4a">${n.authorName||""} · ${fmtDate(n.createdAt?.slice(0,10)||"")}</div>
    </div>`;
  }).join("");

  return`<div class="page-header">
    <div><div class="page-title">💡 FYI</div><div class="page-sub">Para sua informação — notas rápidas de referência da equipe</div></div>
    <button class="btn-primary" id="btn-add-fyi">+ Nova nota FYI</button>
  </div>
  ${notes.length===0?`<div class="empty-state"><div style="font-size:40px;margin-bottom:12px">💡</div><div class="empty-title">Nenhuma nota FYI</div><div class="empty-sub">Use para registrar informações importantes sem criar uma tarefa</div></div>`:noteCards}`;
}

function openFYIModal(noteId, readOnly=false){
  const n=noteId?fyiNotes[noteId]:{};
  if(readOnly&&noteId){
    const color=n.color||"#c8f04e";
    openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:500px">
      <div class="modal-header"><div class="modal-title" style="color:${color}">${esc(n.title||"Nota FYI")}</div><button class="icon-btn" id="m-x">✕</button></div>
      <div class="modal-body">
        ${n.body?`<div style="font-size:14px;color:#c0c0d0;line-height:1.7;white-space:pre-wrap">${linkify(n.body)}</div>`:"<div style='color:#5a5a6a;font-size:13px'>Sem conteúdo.</div>"}
        ${n.syncCal&&n.date?`<div style="margin-top:14px;font-size:12px;color:#7c6eff">📅 Calendário: ${fmtDate(n.date)}</div>`:""}
        <div style="margin-top:14px;font-size:11px;color:#5a5a6a">Por: ${esc(n.authorName||"—")}</div>
      </div>
      <div class="modal-footer"><button class="btn-ghost" id="m-cancel">Fechar</button></div>
    </div></div>`);
    document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;
    overlayClose("ov"); return;
  }
  openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:500px">
    <div class="modal-header"><div class="modal-title">${noteId?"Editar":"Nova"} nota FYI</div><button class="icon-btn" id="m-x">✕</button></div>
    <div class="modal-body">
      <div class="field"><label>Título *</label><input id="m-ftitle" value="${esc(n.title||"")}" placeholder="Assunto da nota…" autofocus/></div>
      <div class="field"><label>Conteúdo</label><textarea id="m-fbody" rows="5" placeholder="Detalhes, links, referências…">${esc(n.body||"")}</textarea></div>
      <div class="field-row">
        <div class="field"><label>Cor</label><input type="color" id="m-fcolor" value="${n.color||"#c8f04e"}" style="width:100%;height:38px;border:none;background:none;cursor:pointer;border-radius:6px"/></div>
        <div class="field" style="display:flex;align-items:flex-end;gap:10px;padding-bottom:6px">
          <label style="display:flex;align-items:center;gap:8px;cursor:pointer">
            <input type="checkbox" id="m-fsynccal" ${n.syncCal?"checked":""} style="width:15px;height:15px;accent-color:#7c6eff"/>
            <span style="font-size:13px;color:#d0d0e0">Sincronizar com Calendário</span>
          </label>
        </div>
      </div>
      <div id="m-fdate-wrap" style="display:${n.syncCal?"block":"none"}">
        <div class="field"><label>Data no calendário</label><input type="date" id="m-fdate" value="${n.date||""}"/></div>
      </div>
    </div>
    <div class="modal-footer">
      ${noteId?`<button class="btn-danger" id="m-fdel">Excluir</button>`:""}
      <button class="btn-ghost" id="m-cancel">Cancelar</button>
      <button class="btn-primary" id="m-save">Salvar</button>
    </div>
  </div></div>`);
  document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;
  document.getElementById("m-fsynccal")?.addEventListener("change",e=>{
    document.getElementById("m-fdate-wrap").style.display=e.target.checked?"block":"none";
  });
  document.getElementById("m-fdel")?.addEventListener("click",async()=>{
    if(confirm("Excluir nota FYI?")){
      await dbRemove(`fyi_notes/${noteId}`);
      // also remove from cal_events if synced
      if(n.calEventId) await dbRemove(`cal_events/${n.calEventId}`);
      closeModal(); toast("Nota removida","warning");
    }
  });
  document.getElementById("m-save").onclick=async()=>{
    const title=document.getElementById("m-ftitle").value.trim(); if(!title){toast("Digite um título","error");return;}
    const syncCal=document.getElementById("m-fsynccal").checked;
    const date=document.getElementById("m-fdate")?.value||"";
    const body=document.getElementById("m-fbody").value.trim();
    const color=document.getElementById("m-fcolor").value;
    let calEventId=n.calEventId||null;
    if(syncCal&&date){
      const calData={title:"[FYI] "+title,dateStart:date,priority:null,note:body||null,creatorId:currentUser.uid,creatorName:currentProfile.name,createdAt:n.calEventCreatedAt||new Date().toISOString()};
      calEventId=calEventId||uid();
      await dbSet(`cal_events/${calEventId}`,calData);
    } else if(!syncCal&&calEventId){
      await dbRemove(`cal_events/${calEventId}`); calEventId=null;
    }
    const data={title,body,color,syncCal,date:date||null,calEventId,authorId:currentUser.uid,authorName:currentProfile.name,createdAt:n.createdAt||new Date().toISOString()};
    await dbSet(`fyi_notes/${noteId||uid()}`,data);
    toast(noteId?"Nota atualizada!":"Nota criada!","success"); closeModal();
  };
  overlayClose("ov");
}

function openAreaFYIModal(noteId, areaId, readOnly=false){
  const n=noteId?fyiNotes[noteId]:{};
  if(readOnly&&noteId){
    const color=n.color||"#c8f04e";
    openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:500px">
      <div class="modal-header"><div class="modal-title" style="color:${color}">${esc(n.title||"Nota FYI")}</div><button class="icon-btn" id="m-x">✕</button></div>
      <div class="modal-body">
        ${n.body?`<div style="font-size:14px;color:#c0c0d0;line-height:1.7;white-space:pre-wrap">${linkify(n.body)}</div>`:"<div style='color:#5a5a6a;font-size:13px'>Sem conteúdo.</div>"}
        ${n.syncCal&&n.date?`<div style="margin-top:14px;font-size:12px;color:#7c6eff">📅 ${fmtDate(n.date)}</div>`:""}
        <div style="margin-top:14px;font-size:11px;color:#5a5a6a">Por: ${esc(n.authorName||"—")}</div>
      </div>
      <div class="modal-footer"><button class="btn-ghost" id="m-cancel">Fechar</button></div>
    </div></div>`);
    document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;
    overlayClose("ov"); return;
  }
  openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:500px">
    <div class="modal-header"><div class="modal-title">${noteId?"Editar":"Nova"} nota FYI</div><button class="icon-btn" id="m-x">✕</button></div>
    <div class="modal-body">
      <div class="field"><label>Título *</label><input id="m-ftitle" value="${esc(n.title||"")}" placeholder="Assunto da nota…" autofocus/></div>
      <div class="field"><label>Conteúdo</label><textarea id="m-fbody" rows="5" placeholder="Detalhes, links, referências…">${esc(n.body||"")}</textarea></div>
      <div class="field-row">
        <div class="field"><label>Cor</label><input type="color" id="m-fcolor" value="${n.color||"#c8f04e"}" style="width:100%;height:38px;border:none;background:none;cursor:pointer;border-radius:6px"/></div>
        <div class="field" style="display:flex;align-items:flex-end;gap:10px;padding-bottom:6px">
          <label style="display:flex;align-items:center;gap:8px;cursor:pointer">
            <input type="checkbox" id="m-fsynccal" ${n.syncCal?"checked":""} style="width:15px;height:15px;accent-color:#7c6eff"/>
            <span style="font-size:13px;color:#d0d0e0">Sincronizar com Calendário</span>
          </label>
        </div>
      </div>
      <div id="m-fdate-wrap" style="display:${n.syncCal?"block":"none"}">
        <div class="field"><label>Data no calendário</label><input type="date" id="m-fdate" value="${n.date||""}"/></div>
      </div>
    </div>
    <div class="modal-footer">
      ${noteId?`<button class="btn-danger" id="m-fdel">Excluir</button>`:""}
      <button class="btn-ghost" id="m-cancel">Cancelar</button>
      <button class="btn-primary" id="m-save">Salvar</button>
    </div>
  </div></div>`);
  document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;
  document.getElementById("m-fsynccal")?.addEventListener("change",e=>{
    document.getElementById("m-fdate-wrap").style.display=e.target.checked?"block":"none";
  });
  document.getElementById("m-fdel")?.addEventListener("click",async()=>{
    if(confirm("Excluir nota FYI?")){
      await dbRemove(`fyi_notes/${noteId}`);
      if(n.calEventId)await dbRemove(`cal_events/${n.calEventId}`);
      closeModal(); toast("Nota removida","warning");
    }
  });
  document.getElementById("m-save").onclick=async()=>{
    const title=document.getElementById("m-ftitle").value.trim(); if(!title){toast("Digite um título","error");return;}
    const syncCal=document.getElementById("m-fsynccal").checked;
    const date=document.getElementById("m-fdate")?.value||"";
    const body=document.getElementById("m-fbody").value.trim();
    const color=document.getElementById("m-fcolor").value;
    let calEventId=n.calEventId||null;
    if(syncCal&&date){
      const calData={title:"[FYI] "+title,dateStart:date,priority:null,note:body||null,creatorId:currentUser.uid,creatorName:currentProfile.name,createdAt:n.calEventCreatedAt||new Date().toISOString()};
      calEventId=calEventId||uid();
      await dbSet(`cal_events/${calEventId}`,calData);
    } else if(!syncCal&&calEventId){
      await dbRemove(`cal_events/${calEventId}`); calEventId=null;
    }
    const data={title,body,color,syncCal,date:date||null,calEventId,areaId:areaId||null,authorId:currentUser.uid,authorName:currentProfile.name,createdAt:n.createdAt||new Date().toISOString()};
    await dbSet(`fyi_notes/${noteId||uid()}`,data);
    toast(noteId?"Nota atualizada!":"Nota criada!","success"); closeModal();
  };
  overlayClose("ov");
}


function renderAlertsPage(){
  const myAreas=visibleAreas().map(a=>a.id);
  const urgent=Object.entries(tasks).map(([id,t])=>({id,...t})).filter(t=>myAreas.includes(t.areaId)&&t.date&&t.status!=="concluido"&&deadlineClass(t.date)).sort((a,b)=>new Date(a.date)-new Date(b.date));
  const cc={"warn-now":"#ff2020","warn-1":"#e85030","warn-2":"#f09030","warn-3":"#e8c84a"};
  const cl={"warn-now":"\u26a0\ufe0f Menos de 3h","warn-1":"\ud83d\udd34 Amanh\u00e3","warn-2":"\ud83d\udfe0 Em 2 dias","warn-3":"\ud83d\udfe1 Em 3 dias"};
  const bm={"warn-now":"wnow","warn-1":"w1","warn-2":"w2","warn-3":"w3"};
  const myNotifs=Object.entries((typeof window!=="undefined"&&window._myNotifs)||{}).map(([id,n])=>({id,...n})).filter(n=>n&&(n.type==="new_comment"||n.type==="manual_alert")).sort((a,b)=>new Date(b.ts||0)-new Date(a.ts||0));
  const notifsHtml=myNotifs.length?`
    <div style="margin-bottom:20px">
      <div style="font-size:11px;color:#7a7a8a;text-transform:uppercase;letter-spacing:1px;margin-bottom:10px;display:flex;align-items:center;justify-content:space-between">
        <span>\ud83d\udcac Notifica\u00e7\u00f5es (${myNotifs.length})</span>
        <button id="btn-clear-notifs" style="background:none;border:1px solid #2e2e3a;color:#7a7a8a;cursor:pointer;font-size:11px;padding:3px 10px;border-radius:5px">Limpar todas</button>
      </div>
      ${myNotifs.map(n=>{
        const isComment=n.type==="new_comment";
        const borderColor=isComment?"#7c6eff":"#f0a832";
        const task=n.taskId?tasks[n.taskId]:null;
        return`<div class="alert-card" style="border-left:3px solid ${borderColor};margin-bottom:8px">
          <div style="font-size:18px;width:28px;text-align:center;flex-shrink:0">${isComment?"\ud83d\udcac":"\ud83d\udd14"}</div>
          <div style="flex:1">
            <div style="font-size:13px;color:#d0d0e0;line-height:1.4">${esc(n.msg||"")}</div>
            <div style="font-size:11px;color:#5a5a6a;margin-top:3px">${fmtTs(n.ts)}</div>
          </div>
          <div style="display:flex;gap:6px;flex-shrink:0;align-items:center">
            ${n.taskId&&task?`<button class="btn-small btn-detail-alert" data-id="${n.taskId}" style="border:1px solid #2e2e3a;color:#7a7a8a">Ver tarefa</button>`:""}
            <button class="btn-del-notif" data-nid="${n.id}" style="background:none;border:none;color:#5a5a6a;cursor:pointer;font-size:14px;padding:2px 4px">\u2715</button>
          </div>
        </div>`;
      }).join("")}
    </div>`:"";
  const deadlineHtml=urgent.length?`
    <div>
      <div style="font-size:11px;color:#7a7a8a;text-transform:uppercase;letter-spacing:1px;margin-bottom:10px">\u23f0 Prazos pr\u00f3ximos (${urgent.length})</div>
      ${urgent.map(t=>{const c=deadlineClass(t.date),ar=areas[t.areaId];return`<div class="alert-card" style="border-left:3px solid ${cc[c]};margin-bottom:8px"><div class="alert-dot" style="background:${cc[c]}"></div><div style="flex:1"><div style="font-size:14px;font-weight:500;margin-bottom:4px">${esc(t.title)}</div><div style="display:flex;gap:10px;flex-wrap:wrap;font-size:12px;color:#7a7a8a">${ar?`<span>\ud83d\udcc1 ${esc(ar.name)}</span>`:""}${t.resp?`<span>\ud83d\udc64 ${esc(t.resp)}</span>`:""}<span>\ud83d\udcc5 ${fmtDate(t.date)}</span></div></div><span class="deadline-badge ${bm[c]}">${cl[c]}</span><button class="btn-small btn-detail-alert" data-id="${t.id}" style="border:1px solid #2e2e3a;color:#7a7a8a">Ver</button></div>`;}).join("")}
    </div>`:"";
  const empty=!urgent.length&&!myNotifs.length;
  return`<div class="page-header"><div><div class="page-title">Alertas</div><div class="page-sub">${urgent.length} prazo${urgent.length!==1?"s":""} \u00b7 ${myNotifs.length} notifica\u00e7${myNotifs.length!==1?"\u00f5es":"\u00e3o"}</div></div></div>
    ${empty?`<div class="empty-state" style="padding:60px 20px"><div style="font-size:40px;margin-bottom:12px">\u2705</div><div class="empty-title">Tudo em dia!</div></div>`:`${notifsHtml}${deadlineHtml}`}`;
}


// ── HISTÓRICO ─────────────────────────────────────────────────────────────────
function renderHistoricoPage(){

  const logs=Object.entries(auditLog).map(([id,l])=>({id,...l})).sort((a,b)=>new Date(b.ts)-new Date(a.ts));
  const icons={"criar_tarefa":"✏️","editar_tarefa":"🔄","excluir_tarefa":"🗑️","criar_area":"📁","excluir_area":"🗑️","criar_nota":"📌","excluir_nota":"🗑️","aprovar_usuario":"✅","rejeitar_usuario":"❌","alterar_role":"⚙️","excluir_usuario":"👤"};
  return`<div class="page-header"><div><div class="page-title">Histórico de Ações</div><div class="page-sub">👑 Visível apenas para o Super Admin · Últimos ${LIMITS.AUDIT_PURGE_KEEP} registros</div></div></div>
    ${logs.length===0?`<div class="empty-state"><div style="font-size:40px;margin-bottom:12px">📋</div><div class="empty-title">Nenhuma ação registrada</div></div>`
    :`<div style="display:flex;flex-direction:column;gap:8px">${logs.map(l=>`<div class="alert-card"><div style="font-size:20px;width:32px;text-align:center;flex-shrink:0">${icons[l.action]||"📋"}</div><div style="flex:1"><div style="font-size:13px;font-weight:500">${esc(l.detail)}</div><div style="font-size:11px;color:#7a7a8a;margin-top:3px">👤 ${esc(l.userName)} · ${esc(l.userEmail)}</div></div><div style="font-size:11px;color:#5a5a6a;text-align:right;flex-shrink:0;min-width:120px">${fmtTs(l.ts)}</div></div>`).join("")}</div>`}`;
}

// ── ADMIN ─────────────────────────────────────────────────────────────────────
function renderAdminPage(){
  if(!isAdmin()&&!currentProfile?.manageAreas)return"";
  const userList=Object.entries(users).map(([id,u])=>({id,...u}));
  const areaList=Object.entries(areas).map(([id,a])=>({id,...a})).filter(a=>!a.parentId).sort((a,b)=>(a.order||0)-(b.order||0));
  const pendList=Object.entries(pendingUsers).map(([id,p])=>({id,...p})).filter(p=>p.status==="pending");

  const usageBar=(cur,max,color)=>{const pct=Math.min(100,Math.round(cur/max*100));return`<div style="display:flex;align-items:center;gap:10px;margin-bottom:6px"><div style="flex:1;height:6px;background:#1e1e28;border-radius:3px;overflow:hidden"><div style="height:100%;width:${pct}%;background:${pct>85?"#ff6b6b":pct>60?"#f0a832":color};border-radius:3px;transition:width .3s"></div></div><span style="font-size:11px;color:#7a7a8a;min-width:60px">${cur}/${max}</span></div>`;};

  // manageAreas users only see the permissions section
  if(!isAdmin()&&currentProfile?.manageAreas){
    return`<div class="page-header"><div><div class="page-title">Permissões de Área</div><div class="page-sub">Você pode adicionar e remover usuários das áreas</div></div></div>
    <div class="admin-section">
      <div class="admin-section-title">👥 Usuários & Áreas</div>
      <div style="font-size:12px;color:#7a7a8a;margin-bottom:16px">Clique nos chips coloridos para liberar ou restringir o acesso de cada usuário às áreas.</div>
      ${userList.filter(u=>u.role!=="admin1").map(u=>`<div class="user-row" style="flex-wrap:wrap;gap:12px">
        <div class="user-row-avatar" style="background:${u.color||"linear-gradient(135deg,#7c6eff,#4ac8e8)"}">${initials(u.name)}</div>
        <div class="user-row-info" style="flex:1;min-width:200px">
          <div class="user-row-name">${esc(u.name)}</div>
          <div class="user-row-email">${esc(u.email)}</div>
          <div class="permission-grid">
            ${areaList.map(a=>{const on=(u.permissions||[]).includes(a.id);return`<button class="perm-chip ${on?"on":""} perm-toggle" data-uid="${u.id}" data-area="${a.id}" style="${on?`border-color:${a.color};color:${a.color};background:${a.color}12`:""}">${esc(a.name)}</button>`;}).join("")}
          </div>
        </div>
      </div>`).join("")}
    </div>`;
  }

  const backupBtn=isAdmin1?`<button class="btn-primary" id="btn-full-backup" style="background:#7c6eff">⬇ Backup completo</button>`:"";
  return`<div class="page-header"><div><div class="page-title">Administração</div></div>${backupBtn}</div>

    <!-- Firebase Usage Monitor -->
    <div class="admin-section">
      <div class="admin-section-title">📊 Uso do Sistema (Plano Gratuito)</div>
      <div style="font-size:12px;color:#7a7a8a;margin-bottom:14px">Monitoramento para evitar cobranças. Limites do plano gratuito: 1 GB de dados, 10 GB/mês de download, 100 conexões simultâneas.</div>
      <div style="display:grid;grid-template-columns:1fr 1fr;gap:8px 24px">
        <div><div style="font-size:11px;color:#7a7a8a;margin-bottom:3px">Tarefas (máx ${LIMITS.MAX_TASKS})</div>${usageBar(Object.keys(tasks).length,LIMITS.MAX_TASKS,"#c8f04e")}</div>
        <div><div style="font-size:11px;color:#7a7a8a;margin-bottom:3px">Áreas (máx ${LIMITS.MAX_AREAS})</div>${usageBar(Object.keys(areas).length,LIMITS.MAX_AREAS,"#4ac8e8")}</div>
        <div><div style="font-size:11px;color:#7a7a8a;margin-bottom:3px">Notas (máx ${LIMITS.MAX_NOTES})</div>${usageBar(Object.keys(notes).length,LIMITS.MAX_NOTES,"#7c6eff")}</div>
        <div><div style="font-size:11px;color:#7a7a8a;margin-bottom:3px">Blocos fluxograma (máx ${LIMITS.MAX_FLOW_NODES})</div>${usageBar(Object.keys(flowData.nodes||{}).length,LIMITS.MAX_FLOW_NODES,"#f0a832")}</div>
        <div><div style="font-size:11px;color:#7a7a8a;margin-bottom:3px">Usuários (máx 100 simultâneos)</div>${usageBar(userList.length,100,"#4ae89c")}</div>
        <div><div style="font-size:11px;color:#7a7a8a;margin-bottom:3px">Histórico (auto-purga em ${LIMITS.MAX_AUDIT_LOGS})</div>${usageBar(Object.keys(auditLog).length,LIMITS.MAX_AUDIT_LOGS,"#a84ae8")}</div>
      </div>
      <div style="margin-top:12px;font-size:12px;color:#5a5a6a">✅ O sistema nunca excede esses limites automaticamente — ele bloqueia novos itens quando o limite é atingido.</div>
    </div>

    <!-- Pending users -->
    <div class="admin-section">
      <div class="admin-section-title">⏳ Aguardando aprovação ${pendList.length>0?`(${pendList.length})`:""}</div>
      ${pendList.length?pendList.map(p=>`<div class="user-row"><div class="user-row-avatar" style="background:linear-gradient(135deg,#f0a832,#e88030)">${initials(p.name)}</div><div class="user-row-info"><div class="user-row-name">${esc(p.name)}</div><div class="user-row-email">${esc(p.email)}</div></div><div style="display:flex;gap:8px"><button class="btn-primary btn-approve-user" data-id="${p.id}" style="padding:6px 14px;font-size:12px">✓ Aprovar</button><button class="btn-danger btn-reject-user" data-id="${p.id}" style="padding:6px 14px;font-size:12px">✕ Rejeitar</button></div></div>`).join(""):`<div style="font-size:13px;color:#5a5a6a">Nenhum usuário pendente.</div>`}
    </div>

    <!-- Users -->
    <div class="admin-section">
      <div class="admin-section-title">👥 Usuários & Permissões</div>
      <div style="font-size:12px;color:#7a7a8a;margin-bottom:16px">Clique nas áreas para liberar/restringir. Só o 👑 Super Admin pode promover a administrador.</div>
      ${userList.map(u=>{
        const manageOn=!!u.manageAreas;
        const canEditName=isAdmin1; // only super admin can rename
        return`<div class="user-row" style="flex-wrap:wrap;gap:12px">
          <div style="position:relative">
            <div class="user-row-avatar" style="background:${u.color||"linear-gradient(135deg,#7c6eff,#4ac8e8)"}">${initials(u.name)}</div>
            ${isAdmin1?`<input type="color" class="user-color-pick" data-uid="${u.id}" value="${u.color||"#7c6eff"}" title="Cor do usuário" style="position:absolute;bottom:-4px;right:-4px;width:16px;height:16px;border:none;border-radius:50%;cursor:pointer;padding:0;background:none"/>`:``}
          </div>
          <div class="user-row-info" style="flex:1;min-width:200px">
            <div style="display:flex;align-items:center;gap:8px;flex-wrap:wrap">
              ${canEditName
                ?`<input class="user-name-input" data-uid="${u.id}" value="${esc(u.name)}" style="font-weight:600;font-size:14px;background:transparent;border:none;border-bottom:1px solid #2e2e3a;color:#f0eff5;font-family:inherit;outline:none;width:150px"/>`
                :`<div class="user-row-name">${esc(u.name)}</div>`}
              ${u.role==="admin1"?"👑":""}
              ${canEditName?`<button class="btn-small save-user-name" data-uid="${u.id}" style="border:1px solid #c8f04e44;color:#c8f04e;font-size:10px">Salvar nome</button>`:""}
            </div>
            <div class="user-row-email">${esc(u.email)}</div>
            <div class="permission-grid">
              ${areaList.map(a=>{const on=u.role==="admin1"||(u.permissions||[]).includes(a.id);return`<button class="perm-chip ${on?"on":""} perm-toggle" data-uid="${u.id}" data-area="${a.id}" ${u.role==="admin1"?"disabled":""}style="${on?`border-color:${a.color};color:${a.color};background:${a.color}12`:""}">${esc(a.name)}</button>`;}).join("")}
              ${!areaList.length?`<span style="font-size:12px;color:#5a5a6a">Nenhuma área</span>`:""}
            </div>
          </div>
          <div style="display:flex;flex-direction:column;align-items:flex-end;gap:8px">
            <span class="role-badge ${u.role}">${{"admin1":"👑 Super","admin":"Admin","user":"Usuário"}[u.role]||u.role}</span>
            ${u.id!==currentUser?.uid&&u.role!=="admin1"?`
              ${isAdmin1?`<button class="btn-small toggle-role" data-uid="${u.id}" data-role="${u.role}" style="border:1px solid #2e2e3a;color:#7a7a8a;font-size:11px">${u.role==="admin"?"→ Usuário":"→ Admin"}</button>`:""}
              ${isAdmin1?`<button class="btn-small btn-ghost-link" data-uid="${u.id}" data-name="${esc(u.name||"")}" style="border:1px solid #4ac8e844;color:#4ac8e8;font-size:11px" title="Vincular tarefas de usuário fantasma">🔗 Vincular tarefas</button>`:""}
              ${isAdmin1?`<button class="btn-small toggle-manage-areas" data-uid="${u.id}" style="border:1px solid ${manageOn?"#c8f04e":"#2e2e3a"};color:${manageOn?"#c8f04e":"#7a7a8a"};font-size:10px" title="Permite que este usuário adicione/remova outros das áreas">${manageOn?"✅ Gerencia áreas":"⬜ Gerencia áreas"}</button>`:""}
              <button class="btn-small del-user" data-uid="${u.id}" style="border:1px solid rgba(255,107,107,.25);color:#ff8080;font-size:11px">Remover</button>
            `:`<span style="font-size:11px;color:#5a5a6a">Você</span>`}
          </div>
        </div>`;}).join("")}
    </div>`;
}

// ── EVENT HANDLERS ────────────────────────────────────────────────────────────
function attachContentEvents(){
  document.querySelectorAll(".btn-open-area").forEach(b=>b.addEventListener("click",e=>{e.stopPropagation();nav("area",b.dataset.id);}));
  document.querySelectorAll(".btn-add-task-area").forEach(b=>b.addEventListener("click",()=>{activeAreaId=b.dataset.id;openTaskModal({areaId:b.dataset.id,status:"a-fazer",priority:"media"});}));
  document.querySelectorAll(".btn-del-area").forEach(b=>b.addEventListener("click",e=>{e.stopPropagation();if(confirm("Excluir área e todas as suas tarefas?"))deleteArea(b.dataset.id);}));
  document.querySelectorAll(".btn-edit-area").forEach(b=>b.addEventListener("click",e=>{e.stopPropagation();openEditAreaModal(b.dataset.id);}));
  document.getElementById("btn-add-task")?.addEventListener("click",()=>openTaskModal({areaId:activeAreaId,status:"a-fazer",priority:"media"}));
  document.querySelectorAll(".btn-toggle-col").forEach(btn=>{
    btn.addEventListener("click",e=>{
      e.stopPropagation();
      const key=btn.dataset.colkey;
      if(!areaCalCollapsed[activeAreaId]) areaCalCollapsed[activeAreaId]={};
      areaCalCollapsed[activeAreaId][key]=!areaCalCollapsed[activeAreaId][key];
      render();
    });
  });
  document.getElementById("btn-save-area-detail")?.addEventListener("click",async()=>{
    if(!isAdmin1){toast("Apenas o Super Admin pode editar os detalhes","error");return;}
    const val=document.getElementById("area-detail-text")?.value||"";
    await dbSet(`areas/${activeAreaId}/detail`,val||null);
    await logAction("editar_area","Detalhes atualizados: "+areas[activeAreaId]?.name);
    toast("Detalhes salvos!","success");
  });
  document.getElementById("area-detail-text")?.addEventListener("focus",e=>{e.target.style.borderColor=areas[activeAreaId]?.color||"#c8f04e";});
  document.getElementById("area-detail-text")?.addEventListener("blur",e=>{e.target.style.borderColor="#1e1e28";});
  document.querySelectorAll(".btn-add-task-col").forEach(b=>b.addEventListener("click",()=>openTaskModal({areaId:activeAreaId,status:b.dataset.status,priority:"media"})));
  document.querySelectorAll(".card[data-detail]").forEach(c=>c.addEventListener("click",()=>openDetailModal(c.dataset.detail)));
  document.querySelectorAll(".btn-detail-alert").forEach(b=>b.addEventListener("click",()=>openDetailModal(b.dataset.id)));
  document.querySelectorAll(".btn-del-notif").forEach(b=>b.addEventListener("click",async()=>{
    await dbRemove(`user_notifs/${currentUser.uid}/${b.dataset.nid}`);
  }));
  document.getElementById("btn-clear-notifs")?.addEventListener("click",async()=>{
    const notifs=window._myNotifs||{};
    const commentAlerts=Object.keys(notifs).filter(k=>notifs[k].type==="new_comment"||notifs[k].type==="manual_alert");
    for(const k of commentAlerts) await dbRemove(`user_notifs/${currentUser.uid}/${k}`);
    toast("Notificações limpas","success");
  });
  document.getElementById("btn-export-area")?.addEventListener("click",()=>exportAreaTasks(activeAreaId));
  document.getElementById("btn-full-backup")?.addEventListener("click",exportFullBackup);
  document.querySelectorAll(".btn-detail-task").forEach(b=>b.addEventListener("click",()=>openDetailModal(b.dataset.id)));
  document.getElementById("btn-add-note")?.addEventListener("click",()=>openNoteModal(null,false));
  document.querySelectorAll(".btn-edit-note").forEach(b=>b.addEventListener("click",()=>openNoteModal(b.dataset.id,false)));
  document.querySelectorAll(".btn-del-note").forEach(b=>b.addEventListener("click",async()=>{if(confirm("Excluir nota?")){await dbRemove(`notes/${b.dataset.id}`);await logAction("excluir_nota","Nota excluída");toast("Nota excluída","warning");}}));
  // ── Area notes block editor ──
  if(page==="area") attachAreaNotesEditorEvents(activeAreaId);
  // ── Personal notes block editor ──
  if(page==="notas-pessoais") attachPersonalNotesEditorEvents();
  document.querySelectorAll(".btn-publish-pnote").forEach(b=>b.addEventListener("click",async()=>{
    if(!confirm("Publicar para toda a equipe?"))return;
    const n=personalNotes[b.dataset.id];if(!n)return;
    if(Object.keys(notes).length>=LIMITS.MAX_NOTES){toast(`Limite de ${LIMITS.MAX_NOTES} notas atingido`,"error");return;}
    const id=uid();await dbSet(`notes/${id}`,{...n,id,authorId:currentUser.uid,createdAt:new Date().toISOString()});
    await dbRemove(`personal_notes/${currentUser.uid}/${b.dataset.id}`);
    await logAction("criar_nota",`Nota publicada: ${n.title}`);toast("Nota publicada!","success");
  }));
  attachFlowEvents();
  attachOrgEvents();
  attachCalEvents();
  attachFreelaEvents();
  if(page==="prospecção") attachProspEvents();
  document.querySelectorAll(".btn-ghost-link").forEach(b=>b.addEventListener("click",()=>openGhostLinkModal(b.dataset.uid,b.dataset.name)));
  document.querySelectorAll(".btn-approve-user").forEach(b=>b.addEventListener("click",async()=>{const p=pendingUsers[b.dataset.id];if(!p)return;await dbSet(`users/${b.dataset.id}`,{name:p.name,email:p.email,role:"user",permissions:[],createdAt:new Date().toISOString()});await dbSet(`pending_users/${b.dataset.id}/status`,"approved");await logAction("aprovar_usuario",`Aprovado: ${p.name}`);toast(`${p.name} aprovado!`,"success");}));
  document.querySelectorAll(".btn-reject-user").forEach(b=>b.addEventListener("click",async()=>{const p=pendingUsers[b.dataset.id];if(!p)return;await dbSet(`pending_users/${b.dataset.id}/status`,"rejected");await logAction("rejeitar_usuario",`Rejeitado: ${p.name}`);toast(`${p.name} rejeitado`,"warning");}));
  document.querySelectorAll(".perm-toggle").forEach(b=>b.addEventListener("click",async()=>{
    const u=users[b.dataset.uid];if(!u||u.role==="admin1")return;
    // only admin OR admin1 can toggle area permissions
    if(!isAdmin()){toast("Apenas admin pode alterar áreas de usuários","error");return;}
    const perms=u.permissions||[];await dbSet(`users/${b.dataset.uid}/permissions`,perms.includes(b.dataset.area)?perms.filter(p=>p!==b.dataset.area):[...perms,b.dataset.area]);toast("Permissão atualizada","success");
  }));
  document.querySelectorAll(".toggle-role").forEach(b=>b.addEventListener("click",async()=>{if(!isAdmin1){toast("Apenas o Super Admin pode alterar funções","error");return;}const nr=b.dataset.role==="admin"?"user":"admin";await dbSet(`users/${b.dataset.uid}/role`,nr);await logAction("alterar_role",`Função → ${nr}: ${users[b.dataset.uid]?.name}`);toast("Função atualizada","success");}));
  document.querySelectorAll(".user-color-pick").forEach(inp=>inp.addEventListener("change",async()=>{
    if(!isAdmin1)return;
    await dbSet(`users/${inp.dataset.uid}/color`,inp.value);
    toast("Cor atualizada!","success");
  }));
  document.querySelectorAll(".save-user-name").forEach(b=>b.addEventListener("click",async()=>{
    if(!isAdmin1){toast("Apenas o Super Admin pode renomear","error");return;}
    const inp=document.querySelector(`.user-name-input[data-uid="${b.dataset.uid}"]`);
    const name=inp?.value.trim(); if(!name)return;
    await dbSet(`users/${b.dataset.uid}/name`,name);
    await logAction("renomear_usuario",`Renomeado: ${name}`);
    toast("Nome atualizado!","success");
  }));
  document.querySelectorAll(".toggle-manage-areas").forEach(b=>b.addEventListener("click",async()=>{
    if(!isAdmin1){toast("Apenas o Super Admin pode conceder esta permissão","error");return;}
    const u=users[b.dataset.uid]; if(!u||u.role==="admin1")return;
    const newVal=!u.manageAreas;
    await dbSet(`users/${b.dataset.uid}/manageAreas`,newVal);
    toast(newVal?'✅ Acesso de gerência concedido — aba ADM aparecerá para o usuário':'❌ Acesso de gerência removido','success');
    await logAction("permissao_areas",`${newVal?"Concedida":"Removida"} permissão de gerenciar áreas: ${u.name}`);
    toast(newVal?"Permissão concedida!":"Permissão removida","success");
  }));
  document.querySelectorAll(".del-user").forEach(b=>b.addEventListener("click",async()=>{if(!confirm("Remover usuário?"))return;const name=users[b.dataset.uid]?.name||"";await dbRemove(`users/${b.dataset.uid}`);await logAction("excluir_usuario",`Removido: ${name}`);toast("Usuário removido","warning");}));

  // FYI page handlers
  document.getElementById("btn-add-fyi")?.addEventListener("click",()=>openFYIModal(null));
  document.querySelectorAll(".fyi-card[data-fyi-open]").forEach(card=>{
    card.addEventListener("click",e=>{
      if(e.target.classList.contains("btn-fyi-edit")||e.target.classList.contains("btn-fyi-del"))return;
      const canEdit=fyiNotes[card.dataset.fyiOpen]?.authorId===currentUser?.uid||isAdmin1;
      openFYIModal(card.dataset.fyiOpen, !canEdit);
    });
    // Drag to reorder
    card.addEventListener("dragstart",e=>{e.dataTransfer.setData("text/plain",card.dataset.fyiId);card.style.opacity="0.5";});
    card.addEventListener("dragend",()=>card.style.opacity="1");
    card.addEventListener("dragover",e=>{e.preventDefault();card.style.outline="2px solid #c8f04e44";});
    card.addEventListener("dragleave",()=>card.style.outline="");
    card.addEventListener("drop",async e=>{
      e.preventDefault();card.style.outline="";
      const srcId=e.dataTransfer.getData("text/plain");
      if(!srcId||srcId===card.dataset.fyiId)return;
      const list=Object.values(fyiNotes).filter(n=>!n.areaId).sort((a,b)=>(a.order||0)-(b.order||0));
      const si=list.findIndex(n=>n.id===srcId), ti=list.findIndex(n=>n.id===card.dataset.fyiId);
      if(si<0||ti<0)return;
      const [moved]=list.splice(si,1); list.splice(ti,0,moved);
      for(let i=0;i<list.length;i++) await dbSet(`fyi_notes/${list[i].id}/order`,i);
    });
  });
  document.querySelectorAll(".btn-fyi-edit").forEach(b=>b.addEventListener("click",()=>openFYIModal(b.dataset.id)));
  document.querySelectorAll(".btn-fyi-del").forEach(b=>b.addEventListener("click",async()=>{
    if(!confirm("Excluir nota FYI?"))return;
    const n=fyiNotes[b.dataset.id];
    await dbRemove(`fyi_notes/${b.dataset.id}`);
    if(n?.calEventId)await dbRemove(`cal_events/${n.calEventId}`);
    toast("Nota removida","warning");
  }));

  // Ghost user link
  document.querySelectorAll(".btn-ghost-link").forEach(b=>b.addEventListener("click",()=>openGhostLinkModal(b.dataset.uid, b.dataset.uname)));
}

// ── GHOST USER LINK ───────────────────────────────────────────────────────────
function openGhostLinkModal(targetUid, targetName){
  // Find all unique "ghost" names in tasks — names that don't match any live user
  const liveNames=new Set(Object.values(users).map(u=>u.name?.trim()).filter(Boolean));
  const ghostNames=new Set();
  Object.values(tasks).forEach(t=>{
    const resps=Array.isArray(t.resps)?t.resps:(t.resp?[t.resp]:[]);
    resps.forEach(r=>{if(r&&!liveNames.has(r))ghostNames.add(r);});
    if(t.creatorName&&!liveNames.has(t.creatorName))ghostNames.add(t.creatorName);
  });
  const ghosts=[...ghostNames];
  if(!ghosts.length){toast("Nenhum nome fantasma encontrado nas tarefas","info");return;}
  openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:460px">
    <div class="modal-header"><div class="modal-title">👻 Vincular nome fantasma a ${esc(targetName)}</div><button class="icon-btn" id="m-x">✕</button></div>
    <div class="modal-body">
      <div style="font-size:13px;color:#a0a0b0;margin-bottom:14px">Selecione um nome antigo nas tarefas para ser substituído pelo nome atual de <strong style="color:#c8f04e">${esc(targetName)}</strong>. Isso atualizará todas as tarefas que contenham esse nome nos responsáveis.</div>
      <div class="field"><label>Nome fantasma a substituir</label>
        <select id="m-ghostname" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none">
          <option value="">Selecione…</option>
          ${ghosts.map(g=>`<option value="${esc(g)}">${esc(g)}</option>`).join("")}
        </select>
      </div>
      <div style="background:#1a1a2e;border:1px solid #2e2e44;border-radius:8px;padding:10px 14px;font-size:11px;color:#7a7a8a">
        ⚠️ Esta ação atualizará os campos <em>responsáveis</em> em todas as tarefas que contenham o nome selecionado. Não pode ser desfeita.
      </div>
    </div>
    <div class="modal-footer">
      <button class="btn-ghost" id="m-cancel">Cancelar</button>
      <button class="btn-primary" id="m-save">Vincular</button>
    </div>
  </div></div>`);
  document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;
  document.getElementById("m-save").onclick=async()=>{
    const ghostName=document.getElementById("m-ghostname").value; if(!ghostName){toast("Selecione um nome","error");return;}
    let count=0;
    const updates={};
    Object.entries(tasks).forEach(([tid,t])=>{
      const resps=Array.isArray(t.resps)?t.resps:(t.resp?[t.resp]:[]);
      const newResps=resps.map(r=>r===ghostName?targetName:r);
      if(JSON.stringify(resps)!==JSON.stringify(newResps)){updates[`tasks/${tid}/resps`]=newResps;count++;}
    });
    if(!count){toast("Nenhuma tarefa encontrada com esse nome","info");closeModal();return;}
    for(const [path,val] of Object.entries(updates)) await dbSet(path,val);
    await logAction("vincular_fantasma",`"${ghostName}" → "${targetName}" em ${count} tarefa(s)`);
    toast(`${count} tarefa(s) atualizadas!`,"success"); closeModal();
  };
  overlayClose("ov");
}


function attachFlowEvents(){
  const svg=document.getElementById("flow-svg");if(!svg)return;
  document.getElementById("btn-add-node")?.addEventListener("click",addFlowNode);
  document.getElementById("node-label")?.addEventListener("keydown",e=>{if(e.key==="Enter")addFlowNode();});
  document.getElementById("cancel-connect")?.addEventListener("click",()=>{connecting=null;render();});
  document.querySelectorAll(".btn-add-area-node").forEach(b=>b.addEventListener("click",()=>{
    if(Object.keys(flowData.nodes||{}).length>=LIMITS.MAX_FLOW_NODES){toast(`Limite de ${LIMITS.MAX_FLOW_NODES} blocos atingido`,"error");return;}
    const a=areas[b.dataset.areaId];if(a)dbSet(`flow/nodes/${uid()}`,{label:a.name,color:a.color,shape:"rect",areaId:a.id,x:60+Math.random()*380,y:60+Math.random()*280});
  }));
  document.querySelectorAll(".del-node").forEach(el=>el.addEventListener("click",e=>{e.stopPropagation();const id=el.dataset.nodeId,nn={...flowData.nodes};delete nn[id];const ne=Object.fromEntries(Object.entries(flowData.edges||{}).filter(([,e])=>e.from!==id&&e.to!==id));dbSet("flow/nodes",Object.keys(nn).length?nn:null);dbSet("flow/edges",Object.keys(ne).length?ne:null);}));
  document.querySelectorAll(".edit-flow-node").forEach(el=>el.addEventListener("click",e=>{e.stopPropagation();openFlowNodeEditModal(el.dataset.nodeId);}));
  document.querySelectorAll(".del-edge").forEach(el=>el.addEventListener("click",e=>{e.stopPropagation();if(confirm("Excluir esta conexao?")){dbRemove(`flow/edges/${el.dataset.edgeId}`);selEdge=null;render();}}));
  document.querySelectorAll(".edit-edge").forEach(el=>el.addEventListener("click",e=>{e.stopPropagation();openEdgeModal(el.dataset.edgeId);}));
  document.querySelectorAll(".edge-hit").forEach(el=>el.addEventListener("click",e=>{e.stopPropagation();selEdge=selEdge===el.dataset.edgeId?null:el.dataset.edgeId;render();}));
  document.querySelectorAll(".conn-handle").forEach(el=>el.addEventListener("mousedown",e=>{e.stopPropagation();connecting={fromId:el.dataset.nodeId,side:el.dataset.side||"right"};render();}));
  document.querySelectorAll(".flow-node").forEach(el=>{
    el.addEventListener("click",e=>{if(e.target.classList.contains("conn-handle")||e.target.classList.contains("del-node"))return;const aId=el.dataset.areaId;if(aId&&areas[aId]&&!connecting&&!dragging)nav("area",aId);});
    el.addEventListener("mousedown",e=>{
      if(e.target.classList.contains("conn-handle")||e.target.classList.contains("del-node")||e.target.classList.contains("edit-flow-node"))return;
      if(e.target.classList.contains("flow-resize-handle"))return;
      // Ignorar cliques em controles de bloco-raiz (toggle e add-child) — usar closest para pegar filhos
      if(e.target.closest?.(".flow-root-toggle")||e.target.closest?.(".flow-add-child"))return;
      e.stopPropagation();
      const nid=el.dataset.nodeId;
      if(connecting){const toId=nid;if(connecting.fromId!==toId)dbSet(`flow/edges/${uid()}`,{from:connecting.fromId,to:toId,fromSide:connecting.side||"right",toSide:"left",label:"",detail:""});connecting=null;render();return;}
      if(e.shiftKey){
        if(selectedNodes.has(nid))selectedNodes.delete(nid);else selectedNodes.add(nid);
        render();return;
      }
      const r=svg.getBoundingClientRect();
      const allNodes2=Object.entries(flowData.nodes||{}).map(([id,n])=>({id,...n}));
      const n=allNodes2.find(n=>n.id===nid);if(!n)return;
      if(selectedNodes.size>1&&selectedNodes.has(nid)){
        groupDragging={startX:e.clientX,startY:e.clientY,nodes:Object.fromEntries([...selectedNodes].map(sid=>{const sn=allNodes2.find(x=>x.id===sid);return[sid,{x:sn.x,y:sn.y}];}))};
      } else {
        selectedNodes.clear();render();
        // ox/oy com zoom e pan — igual ao organograma
        dragging={id:nid,ox:(e.clientX-r.left-flowPan.x)/flowZoom-n.x,oy:(e.clientY-r.top-flowPan.y)/flowZoom-n.y};
      }
    });
  });
  svg.addEventListener("mousemove",e=>{
    const r=svg.getBoundingClientRect();
    const cx=(e.clientX-r.left-flowPan.x)/flowZoom;
    const cy=(e.clientY-r.top-flowPan.y)/flowZoom;
    mousePos={x:cx,y:cy};
    if(connecting){render();return;}
    if(flowResizing){
      const dx=(e.clientX-flowResizing.startX)/flowZoom;
      const dy=(e.clientY-flowResizing.startY)/flowZoom;
      flowResizing.curW=Math.max(60,Math.round(flowResizing.startW+dx));
      flowResizing.curH=Math.max(30,Math.round(flowResizing.startH+dy));
      // Update local render only (no Firebase during drag)
      if(flowData.nodes[flowResizing.id]){
        flowData.nodes[flowResizing.id].w=flowResizing.curW;
        flowData.nodes[flowResizing.id].h=flowResizing.curH;
      }
      render(); return;
    }
    if(flowPanning){
      flowPan.x=e.clientX-flowPanStart.x;
      flowPan.y=e.clientY-flowPanStart.y;
      render(); return;
    }
    if(flowSelecting&&selBox){
      selBox.x2=cx; selBox.y2=cy;
      render(); return;
    }
    if(groupDragging){
      const dx=(e.clientX-groupDragging.startX)/flowZoom;
      const dy=(e.clientY-groupDragging.startY)/flowZoom;
      // Update local state only during drag
      Object.entries(groupDragging.nodes).forEach(([sid,orig])=>{
        if(flowData.nodes[sid]){
          flowData.nodes[sid].x=Math.max(0,orig.x+dx);
          flowData.nodes[sid].y=Math.max(0,orig.y+dy);
        }
      });
      groupDragging.lastDx=dx; groupDragging.lastDy=dy;
      render(); return;
    }
    if(!dragging)return;
    // Update local state only during drag
    if(flowData.nodes[dragging.id]){
      flowData.nodes[dragging.id].x=Math.max(0,cx-dragging.ox);
      flowData.nodes[dragging.id].y=Math.max(0,cy-dragging.oy);
    }
    render();
  });
  svg.addEventListener("mouseup",()=>{
    if(flowSelecting&&selBox){
      const x1=Math.min(selBox.x1,selBox.x2), x2=Math.max(selBox.x1,selBox.x2);
      const y1=Math.min(selBox.y1,selBox.y2), y2=Math.max(selBox.y1,selBox.y2);
      if(Math.abs(x2-x1)>8||Math.abs(y2-y1)>8){
        const allNds=Object.entries(flowData.nodes||{}).map(([id,n])=>({id,...n}));
        allNds.forEach(n=>{
          const W=n.w||150,H=n.h||48;
          const cx2=n.x+W/2, cy2=n.y+H/2;
          if(cx2>=x1&&cx2<=x2&&cy2>=y1&&cy2<=y2)selectedNodes.add(n.id);
        });
      }
      selBox=null; flowSelecting=false;
      render(); return;
    }
    // Save final positions to Firebase (once on mouseup)
    if(flowResizing){
      dbSet(`flow/nodes/${flowResizing.id}/w`,flowResizing.curW||flowResizing.startW);
      dbSet(`flow/nodes/${flowResizing.id}/h`,flowResizing.curH||flowResizing.startH);
    }
    if(groupDragging&&groupDragging.lastDx!=null){
      Object.entries(groupDragging.nodes).forEach(([sid,orig])=>{
        dbSet(`flow/nodes/${sid}/x`,Math.max(0,orig.x+groupDragging.lastDx));
        dbSet(`flow/nodes/${sid}/y`,Math.max(0,orig.y+groupDragging.lastDy));
      });
      // Verificar se o grupo foi solto sobre um bloco-raiz expandido
      const roots=Object.entries(flowData.nodes||{}).filter(([,n])=>n.type==="root"&&flowContainerExpanded[n.id]===true);
      if(roots.length){
        let anyAdopted=false;
        Object.entries(groupDragging.nodes).forEach(([sid])=>{
          const sn=flowData.nodes?.[sid]; if(!sn||sn.type==="root")return;
          const cx2=Math.max(0,sn.x)+(sn.w||150)/2;
          const cy2=Math.max(0,sn.y)+(sn.h||48)/2;
          for(const [rid,rn] of roots){
            if(rid===sid)continue;
            // bounding box do raiz + filhos atuais
            const rChildren=Object.values(flowData.nodes||{}).filter(n=>n.flowParent===rid);
            const allX=[rn.x,...rChildren.map(n=>n.x)], allY=[rn.y,...rChildren.map(n=>n.y)];
            const allW=[rn.w||150,...rChildren.map(n=>n.w||150)], allH=[rn.h||48,...rChildren.map(n=>n.h||48)];
            const bx=Math.min(...allX)-30, by=Math.min(...allY)-30;
            const br=Math.max(...allX.map((x,i)=>x+allW[i]))+30;
            const bb=Math.max(...allY.map((y,i)=>y+allH[i]))+50;
            if(cx2>=bx&&cx2<=br&&cy2>=by&&cy2<=bb){
              if(sn.flowParent!==rid){ dbSet(`flow/nodes/${sid}/flowParent`,rid); anyAdopted=true; }
              break;
            }
          }
        });
        if(anyAdopted) toast("Blocos adicionados ao bloco raiz","success");
      }
    }
    if(dragging&&flowData.nodes[dragging.id]){
      const n=flowData.nodes[dragging.id];
      dbSet(`flow/nodes/${dragging.id}/x`,n.x);
      dbSet(`flow/nodes/${dragging.id}/y`,n.y);
    }
    if(flowPanning){flowPanning=false; return;}
    selBox=null; flowSelecting=false;
    dragging=null; groupDragging=null; flowResizing=null;
  });
  svg.addEventListener("click",e=>{if(connecting&&e.target===svg){connecting=null;render();return;}});
  svg.addEventListener("mousedown",e=>{
    // Resize handle
    if(e.target.classList.contains("flow-resize-handle")){
      e.stopPropagation();
      const nid=e.target.dataset.nodeId;
      const n=flowData.nodes?.[nid]; if(!n)return;
      const r=svg.getBoundingClientRect();
      flowResizing={id:nid,startX:e.clientX,startY:e.clientY,startW:n.w||150,startH:n.h||48};
      return;
    }
    // Background click only
    if(e.target!==svg&&e.target.getAttribute("fill")!=="url(#grid)")return;
    if(connecting)return;
    const r=svg.getBoundingClientRect();
    if(flowSelectMode){
      // Select mode: draw selection box
      if(!e.shiftKey)selectedNodes.clear();
      const cx=(e.clientX-r.left-flowPan.x)/flowZoom;
      const cy=(e.clientY-r.top-flowPan.y)/flowZoom;
      selBox={x1:cx,y1:cy,x2:cx,y2:cy};
      flowSelecting=true;
      render();
    } else {
      // Pan mode: drag to move canvas
      flowPanning=true;
      flowPanStart={x:e.clientX-flowPan.x, y:e.clientY-flowPan.y};
    }
  });
  // Zoom
  document.getElementById("flow-zoom-in")?.addEventListener("click",()=>{flowZoom=Math.min(2.5,+(flowZoom+0.15).toFixed(2));render();});
  document.getElementById("flow-zoom-out")?.addEventListener("click",()=>{flowZoom=Math.max(0.25,+(flowZoom-0.15).toFixed(2));render();});
  document.getElementById("flow-zoom-reset")?.addEventListener("click",()=>{flowZoom=1;flowPan={x:0,y:0};render();});
  svg.addEventListener("wheel",e=>{
    e.preventDefault();
    const r=svg.getBoundingClientRect();
    const mx=e.clientX-r.left, my=e.clientY-r.top;
    const delta=e.deltaY>0?-0.1:0.1;
    const newZoom=Math.min(2.5,Math.max(0.25,+(flowZoom+delta).toFixed(2)));
    // Adjust pan so the point under cursor stays fixed
    flowPan.x=mx-(mx-flowPan.x)*(newZoom/flowZoom);
    flowPan.y=my-(my-flowPan.y)*(newZoom/flowZoom);
    flowZoom=newZoom;
    render();
  },{passive:false});

  // ── Group bar ──
  document.getElementById("flow-group-apply")?.addEventListener("click",async()=>{
    const parentId=document.getElementById("flow-group-parent")?.value;
    if(!parentId)return;
    for(const id of selectedNodes){
      if(id===parentId)continue;
      if(parentId==="__remove__") await dbSet(`flow/nodes/${id}/flowParent`,null);
      else{ await dbSet(`flow/nodes/${id}/flowParent`,parentId); flowContainerExpanded[parentId]=true; }
    }
    toast(parentId==="__remove__"?"Blocos removidos do bloco raiz":`${selectedNodes.size} bloco(s) adicionado(s) ao raiz`,"success");
    selectedNodes.clear(); render();
  });
  document.getElementById("flow-group-clear")?.addEventListener("click",()=>{selectedNodes.clear();render();});

  // ── Container events ──
  document.getElementById("btn-flow-select-mode")?.addEventListener("click",()=>{
    flowSelectMode=!flowSelectMode;
    if(!flowSelectMode){selectedNodes.clear();}
    render();
  });
  // ── Bloco Raiz (substitui container) ──
  document.getElementById("btn-add-root-node")?.addEventListener("click",()=>{
    const label=document.getElementById("node-label")?.value.trim()||"Bloco Raiz";
    const color=document.getElementById("node-color")?.value||"#7c6eff";
    const id=uid();
    dbSet(`flow/nodes/${id}`,{label,color,shape:"rect",type:"root",x:80+Math.random()*200,y:60+Math.random()*150});
    if(document.getElementById("node-label"))document.getElementById("node-label").value="";
  });
  // Toggle expand/collapse do bloco raiz
  document.querySelectorAll(".flow-root-toggle").forEach(el=>{
    el.addEventListener("click",e=>{
      e.stopPropagation();
      const nid=el.dataset.nid;
      flowContainerExpanded[nid]=!flowContainerExpanded[nid];
      render();
    });
  });
  // Adicionar filho ao bloco raiz
  document.querySelectorAll(".flow-add-child").forEach(el=>{
    el.addEventListener("click",e=>{
      e.stopPropagation();
      const parentId=el.dataset.nid;
      const label=prompt("Nome do bloco filho:");
      if(!label)return;
      if(Object.keys(flowData.nodes||{}).length>=LIMITS.MAX_FLOW_NODES){toast("Limite de blocos atingido","error");return;}
      const pn=flowData.nodes[parentId];
      const nid=uid();
      dbSet(`flow/nodes/${nid}`,{
        label,color:pn?.color||"#c8f04e",shape:"rect",
        flowParent:parentId,
        x:(pn?.x||80)+80+Math.random()*100,
        y:(pn?.y||60)+80+Math.random()*80
      });
      flowContainerExpanded[parentId]=true;
      render();
    });
  });

  // ── Drop node onto container ──
  // When dragging ends, check if node center is over a container
  // This is handled in mouseup after dragging

  // ── Sticky notes ──
  document.getElementById("btn-add-sticky")?.addEventListener("click",()=>{
    const id=uid();
    dbSet(`flow/stickies/${id}`,{id,text:"",color:"#f0a832",x:80+Math.random()*300,y:60+Math.random()*200,expanded:true,createdAt:new Date().toISOString()});
  });
  // ── Touch events mobile — Fluxograma (só visualização + clique nos blocos) ──
  (function attachFlowTouch(){
    const svg=document.getElementById("flow-svg"); if(!svg)return;
    let lastDist=0, touchStartX=0, touchStartY=0, panStartX=0, panStartY=0;
    svg.addEventListener("touchstart",e=>{
      if(e.touches.length===2){
        // Pinch zoom
        const dx=e.touches[0].clientX-e.touches[1].clientX;
        const dy=e.touches[0].clientY-e.touches[1].clientY;
        lastDist=Math.sqrt(dx*dx+dy*dy);
      } else if(e.touches.length===1){
        touchStartX=e.touches[0].clientX;
        touchStartY=e.touches[0].clientY;
        panStartX=flowPan.x;
        panStartY=flowPan.y;
      }
    },{passive:true});
    svg.addEventListener("touchmove",e=>{
      e.preventDefault();
      if(e.touches.length===2){
        const dx=e.touches[0].clientX-e.touches[1].clientX;
        const dy=e.touches[0].clientY-e.touches[1].clientY;
        const dist=Math.sqrt(dx*dx+dy*dy);
        if(lastDist>0){
          const scale=dist/lastDist;
          flowZoom=Math.min(2.5,Math.max(0.25,+(flowZoom*scale).toFixed(2)));
          render();
        }
        lastDist=dist;
      } else if(e.touches.length===1){
        flowPan.x=panStartX+(e.touches[0].clientX-touchStartX);
        flowPan.y=panStartY+(e.touches[0].clientY-touchStartY);
        render();
      }
    },{passive:false});
    svg.addEventListener("touchend",()=>{lastDist=0;},{passive:true});
  })();
} // fim attachFlowEvents

// ── Container Drawer — painel lateral com mini-canvas do container ────────────
function openContainerDrawer(cid){
  const c=flowData.nodes?.[cid]; if(!c)return;
  const cColor=c.color||"#7c6eff";
  const allChildren=Object.entries(flowData.nodes||{})
    .filter(([,n])=>n.containerParent===cid).map(([id,n])=>({id,...n}));
  const innerEdges=Object.entries(flowData.edges||{})
    .map(([id,e])=>({id,...e}))
    .filter(e=>allChildren.some(n=>n.id===e.from)&&allChildren.some(n=>n.id===e.to));

  // Posições relativas ao container (offset pelo mínimo para normalizar)
  const minX=allChildren.length?Math.min(...allChildren.map(n=>n.x))-20:0;
  const minY=allChildren.length?Math.min(...allChildren.map(n=>n.y))-20:0;

  // Estado local do mini-canvas
  let dZoom=1, dPan={x:30,y:30};
  let dDragging=null, dPanning=false, dPanStart={x:0,y:0};
  // Cópia local dos nós com coordenadas normalizadas
  let dNodes=allChildren.map(n=>({...n,x:n.x-minX,y:n.y-minY}));
  const dEdges=innerEdges.map(e=>({...e}));

  function buildInnerSVG(){
    const svgNodes=dNodes.map(n=>{
      const W=n.w||150, H=n.h||48;
      const bc=n.areaId&&areas[n.areaId]?areas[n.areaId].color:(n.color||"#c8f04e");
      return`<g class="dn-node" data-nid="${n.id}" transform="translate(${n.x},${n.y})" style="cursor:grab">
        <rect x="0" y="0" width="${W}" height="${H}" rx="10" fill="${bc}18" stroke="${bc}88" stroke-width="1.5"/>
        <text x="${W/2}" y="${H/2}" text-anchor="middle" dominant-baseline="middle" fill="#d0d0e0" font-size="12" font-family="DM Sans,sans-serif" style="pointer-events:none;user-select:none">${esc(n.label||"")}</text>
        <circle cx="${W}" cy="${H/2}" r="5" fill="#16161e" stroke="${bc}" stroke-width="1.2" class="dn-conn" data-nid="${n.id}" style="cursor:crosshair"/>
        <rect x="${W-6}" y="${H-6}" width="10" height="10" rx="2" fill="${bc}44" stroke="${bc}" stroke-width="1" class="dn-resize" data-nid="${n.id}" style="cursor:se-resize"/>
        ${isAdmin1?`<circle cx="${W}" cy="0" r="7" fill="#ff6b6b1a" stroke="#ff6b6b" stroke-width="1" class="dn-del" data-nid="${n.id}" style="cursor:pointer"/><text x="${W}" y="0" text-anchor="middle" dominant-baseline="middle" fill="#ff6b6b" font-size="9" style="pointer-events:none">✕</text>`:""}
      </g>`;
    }).join("");
    const svgEdges2=dEdges.map(e=>{
      const fn=dNodes.find(n=>n.id===e.from),tn=dNodes.find(n=>n.id===e.to);if(!fn||!tn)return"";
      const fx=fn.x+(fn.w||150), fy=fn.y+(fn.h||48)/2;
      const tx=tn.x, ty=tn.y+(tn.h||48)/2;
      return`<path d="M${fx},${fy} C${fx+50},${fy} ${tx-50},${ty} ${tx},${ty}" fill="none" stroke="#5a5a6e" stroke-width="1.5" marker-end="url(#darrow)"/>`;
    }).join("");
    const g=document.getElementById("dn-canvas-g"); if(!g)return;
    g.setAttribute("transform",`translate(${dPan.x},${dPan.y}) scale(${dZoom})`);
    g.innerHTML=svgEdges2+svgNodes;
    // Re-attach events
    g.querySelectorAll(".dn-node").forEach(el=>{
      el.addEventListener("mousedown",ev=>{
        if(ev.target.classList.contains("dn-conn")||ev.target.classList.contains("dn-resize")||ev.target.classList.contains("dn-del"))return;
        ev.stopPropagation();
        const dsvg=document.getElementById("dn-svg");
        const r2=dsvg.getBoundingClientRect();
        const n=dNodes.find(n=>n.id===el.dataset.nid);
        if(n) dDragging={id:n.id,ox:(ev.clientX-r2.left-dPan.x)/dZoom-n.x,oy:(ev.clientY-r2.top-dPan.y)/dZoom-n.y};
      });
    });
    g.querySelectorAll(".dn-del").forEach(el=>{
      el.addEventListener("click",async ev=>{
        ev.stopPropagation();
        if(!confirm("Remover bloco do container?"))return;
        await dbRemove(`flow/nodes/${el.dataset.nid}`);
        dNodes=dNodes.filter(n=>n.id!==el.dataset.nid);
        buildInnerSVG();
      });
    });
  }

  // Remover drawer anterior se existir
  document.getElementById("container-drawer")?.remove();

  const drawer=document.createElement("div");
  drawer.id="container-drawer";
  drawer.style.cssText=`position:fixed;top:0;right:0;width:560px;max-width:96vw;height:100vh;background:#0e0e16;border-left:2px solid ${cColor}55;z-index:1500;display:flex;flex-direction:column;box-shadow:-8px 0 40px rgba(0,0,0,.65);`;
  drawer.innerHTML=`
    <div style="display:flex;align-items:center;gap:10px;padding:14px 18px;border-bottom:1px solid ${cColor}22;background:${cColor}0d;flex-shrink:0">
      <div style="width:10px;height:10px;border-radius:50%;background:${cColor}"></div>
      <div style="font-family:'Syne',sans-serif;font-size:15px;font-weight:700;color:${cColor};flex:1">${esc(c.label||"Container")}</div>
      <span style="font-size:11px;color:#7a7a8a">${allChildren.length} bloco${allChildren.length!==1?"s":""}</span>
      <button id="dn-expand" style="background:none;border:1px solid ${cColor}44;border-radius:7px;color:${cColor};cursor:pointer;padding:4px 10px;font-size:12px" title="Devolve blocos ao canvas principal">↗ Expandir no canvas</button>
      <button id="dn-close" style="background:none;border:1px solid #2e2e3a;border-radius:7px;color:#7a7a8a;cursor:pointer;padding:4px 10px;font-size:13px">✕</button>
    </div>
    <div style="display:flex;gap:8px;padding:10px 14px;border-bottom:1px solid #1a1a22;flex-shrink:0;flex-wrap:wrap;align-items:center">
      <input id="dn-label" placeholder="Nome do novo bloco…" style="flex:1;min-width:120px;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:6px 10px;color:#f0eff5;font-family:inherit;font-size:12px;outline:none"/>
      <input type="color" id="dn-color" value="#c8f04e" style="width:30px;height:30px;border:none;background:none;cursor:pointer;border-radius:6px"/>
      <button id="dn-add" class="btn-primary" style="font-size:12px;padding:6px 14px">+ Bloco</button>
    </div>
    <div style="flex:1;position:relative;overflow:hidden">
      <svg id="dn-svg" width="100%" height="100%" style="display:block;cursor:grab">
        <defs>
          <pattern id="dn-grid" width="28" height="28" patternUnits="userSpaceOnUse">
            <path d="M28 0 L0 0 0 28" fill="none" stroke="#18182a" stroke-width="1"/>
          </pattern>
          <marker id="darrow" markerWidth="9" markerHeight="9" refX="7" refY="3.5" orient="auto">
            <path d="M0,0 L0,7 L9,3.5 z" fill="#5a5a6e"/>
          </marker>
        </defs>
        <rect width="100%" height="100%" fill="url(#dn-grid)"/>
        <g id="dn-canvas-g"></g>
      </svg>
    </div>`;
  document.body.appendChild(drawer);
  buildInnerSVG();

  // ── Eventos do drawer ──
  document.getElementById("dn-close").onclick=()=>{
    drawer.remove();
    flowContainerExpanded[cid]=false;
    render();
  };
  document.getElementById("dn-expand").onclick=()=>{
    // Devolve posições locais ao Firebase e expande no canvas
    dNodes.forEach(n=>{
      dbSet(`flow/nodes/${n.id}/x`,n.x+minX);
      dbSet(`flow/nodes/${n.id}/y`,n.y+minY);
    });
    flowContainerExpanded[cid]=true;
    drawer.remove();
    render();
    toast("Container expandido no canvas","success");
  };
  document.getElementById("dn-add").onclick=()=>{
    const label=document.getElementById("dn-label")?.value.trim();
    if(!label){toast("Digite um nome","error");return;}
    if(Object.keys(flowData.nodes||{}).length>=LIMITS.MAX_FLOW_NODES){toast("Limite de blocos atingido","error");return;}
    const color=document.getElementById("dn-color")?.value||"#c8f04e";
    const nid=uid();
    const nx=60+Math.random()*200, ny=60+Math.random()*150;
    const nodeData={label,color,shape:"rect",x:nx+minX,y:ny+minY,containerParent:cid};
    dbSet(`flow/nodes/${nid}`,nodeData);
    // Atualiza estado local
    if(!flowData.nodes) flowData.nodes={};
    flowData.nodes[nid]={...nodeData,id:nid};
    dNodes.push({...nodeData,id:nid,x:nx,y:ny});
    document.getElementById("dn-label").value="";
    buildInnerSVG();
    toast("Bloco adicionado","success");
  };

  const dsvg=document.getElementById("dn-svg");
  dsvg.addEventListener("mousedown",ev=>{
    if(ev.target===dsvg||ev.target.getAttribute("fill")==="url(#dn-grid)"){
      dPanning=true;
      dPanStart={x:ev.clientX-dPan.x,y:ev.clientY-dPan.y};
      dsvg.style.cursor="grabbing";
    }
  });
  dsvg.addEventListener("mousemove",ev=>{
    if(dPanning){
      dPan.x=ev.clientX-dPanStart.x;
      dPan.y=ev.clientY-dPanStart.y;
      document.getElementById("dn-canvas-g")?.setAttribute("transform",`translate(${dPan.x},${dPan.y}) scale(${dZoom})`);
      return;
    }
    if(!dDragging)return;
    const r2=dsvg.getBoundingClientRect();
    const nx=Math.max(0,(ev.clientX-r2.left-dPan.x)/dZoom-dDragging.ox);
    const ny=Math.max(0,(ev.clientY-r2.top-dPan.y)/dZoom-dDragging.oy);
    const n=dNodes.find(n=>n.id===dDragging.id);
    if(n){n.x=nx;n.y=ny;}
    buildInnerSVG();
  });
  dsvg.addEventListener("mouseup",()=>{
    if(dPanning){dPanning=false;dsvg.style.cursor="grab";return;}
    if(dDragging){
      const n=dNodes.find(n=>n.id===dDragging.id);
      if(n){
        dbSet(`flow/nodes/${dDragging.id}/x`,n.x+minX);
        dbSet(`flow/nodes/${dDragging.id}/y`,n.y+minY);
      }
      dDragging=null;
    }
  });
  dsvg.addEventListener("wheel",ev=>{
    ev.preventDefault();
    const r2=dsvg.getBoundingClientRect();
    const mx=ev.clientX-r2.left, my=ev.clientY-r2.top;
    const delta=ev.deltaY>0?-0.1:0.1;
    const nz=Math.min(2.5,Math.max(0.25,+(dZoom+delta).toFixed(2)));
    dPan.x=mx-(mx-dPan.x)*(nz/dZoom);
    dPan.y=my-(my-dPan.y)*(nz/dZoom);
    dZoom=nz;
    document.getElementById("dn-canvas-g")?.setAttribute("transform",`translate(${dPan.x},${dPan.y}) scale(${dZoom})`);
    buildInnerSVG();
  },{passive:false});
}


function renderStickies(){
  const layer=document.getElementById("stickies-layer"); if(!layer)return;
  layer.innerHTML="";
  Object.entries(flowStickies).forEach(([sid,s])=>{
    const div=document.createElement("div");
    div.dataset.sid=sid;
    div.style.cssText=`position:absolute;left:${s.x}px;top:${s.y}px;width:200px;pointer-events:all;z-index:20;`;
    const color=s.color||"#f0a832";
    const expanded=s.expanded!==false;
    div.innerHTML=`
      <div class="sticky-note" style="background:${color}18;border:1.5px solid ${color}55;border-radius:10px;box-shadow:0 4px 18px rgba(0,0,0,.35);overflow:hidden;user-select:none">
        <!-- Header bar -->
        <div class="sticky-header" style="display:flex;align-items:center;gap:6px;padding:6px 8px;background:${color}30;cursor:grab;border-bottom:1px solid ${color}33">
          <span style="font-size:13px">📝</span>
          <span style="flex:1;font-size:11px;font-weight:700;color:${color};font-family:'Syne',sans-serif;white-space:nowrap;overflow:hidden;text-overflow:ellipsis">${s.text?s.text.slice(0,28)+(s.text.length>28?"…":""):"Nova nota"}</span>
          <div style="display:flex;gap:4px">
            ${isAdmin()?`<div class="sticky-color-btn" data-sid="${sid}" title="Cor" style="width:14px;height:14px;border-radius:50%;background:${color};cursor:pointer;border:2px solid ${color}88"></div>`:""}
            <div class="sticky-toggle" data-sid="${sid}" title="${expanded?"Minimizar":"Expandir"}" style="width:18px;height:18px;display:flex;align-items:center;justify-content:center;cursor:pointer;color:${color};font-size:12px;border-radius:4px">${expanded?"▲":"▼"}</div>
            ${isAdmin()?`<div class="sticky-del" data-sid="${sid}" title="Excluir" style="width:18px;height:18px;display:flex;align-items:center;justify-content:center;cursor:pointer;color:#ff6b6b;font-size:12px;border-radius:4px">✕</div>`:""}
          </div>
        </div>
        <!-- Body -->
        ${expanded?`<div style="padding:10px">
          <div class="sticky-body" data-sid="${sid}" contenteditable="${isAdmin()||true}" spellcheck="false" style="font-size:12px;color:#d0d0d8;line-height:1.7;min-height:60px;outline:none;word-break:break-word;white-space:pre-wrap;font-family:'DM Sans',sans-serif">${esc(s.text||"")}</div>
        </div>`:""}
      </div>`;
    layer.appendChild(div);

    // Drag the sticky
    const header=div.querySelector(".sticky-header");
    let dsx=0,dsy=0,startX=0,startY=0,isDragging=false;
    header.addEventListener("mousedown",e=>{
      if(e.target.classList.contains("sticky-toggle")||e.target.classList.contains("sticky-del")||e.target.classList.contains("sticky-color-btn"))return;
      e.preventDefault(); e.stopPropagation();
      isDragging=true;
      startX=e.clientX; startY=e.clientY;
      dsx=s.x; dsy=s.y;
      header.style.cursor="grabbing";
      function onMove(ev){
        if(!isDragging)return;
        const nx=Math.max(0,dsx+(ev.clientX-startX));
        const ny=Math.max(0,dsy+(ev.clientY-startY));
        div.style.left=nx+"px"; div.style.top=ny+"px";
      }
      function onUp(ev){
        isDragging=false; header.style.cursor="grab";
        const nx=Math.max(0,dsx+(ev.clientX-startX));
        const ny=Math.max(0,dsy+(ev.clientY-startY));
        dbSet(`flow/stickies/${sid}/x`,nx);
        dbSet(`flow/stickies/${sid}/y`,ny);
        document.removeEventListener("mousemove",onMove);
        document.removeEventListener("mouseup",onUp);
      }
      document.addEventListener("mousemove",onMove);
      document.addEventListener("mouseup",onUp);
    });

    // Toggle expand/collapse
    div.querySelector(".sticky-toggle")?.addEventListener("click",e=>{
      e.stopPropagation();
      dbSet(`flow/stickies/${sid}/expanded`,!expanded);
    });

    // Delete
    div.querySelector(".sticky-del")?.addEventListener("click",e=>{
      e.stopPropagation();
      if(confirm("Excluir esta nota?")) dbRemove(`flow/stickies/${sid}`);
    });

    // Save text on blur
    div.querySelector(".sticky-body")?.addEventListener("blur",e=>{
      dbSet(`flow/stickies/${sid}/text`,e.target.innerText.trim());
    });
    div.querySelector(".sticky-body")?.addEventListener("click",e=>e.stopPropagation());

    // Color picker
    div.querySelector(".sticky-color-btn")?.addEventListener("click",e=>{
      e.stopPropagation();
      const STICKY_COLORS=["#f0a832","#c8f04e","#7c6eff","#4ac8e8","#ff6b6b","#4ae89c","#e84ab8"];
      showCtxMenu(e.clientX,e.clientY,STICKY_COLORS.map(c=>({
        action:c,icon:`<span style="display:inline-block;width:12px;height:12px;border-radius:50%;background:${c};margin-right:2px;vertical-align:middle"></span>`,
        label:["Laranja","Verde","Roxo","Azul","Vermelho","Verde-água","Rosa"][STICKY_COLORS.indexOf(c)],
        fn:()=>dbSet(`flow/stickies/${sid}/color`,c)
      })));
    });
  });
}


// ── FLOW NODE EDIT MODAL ──────────────────────────────────────────────────────
function openFlowNodeEditModal(nodeId){
  const n=flowData.nodes?.[nodeId]; if(!n)return;
  const areaOptions=Object.entries(areas).map(([id,a])=>`<option value="${id}" ${n.areaId===id?"selected":""}>${esc(a.name)}</option>`).join("");
  const fontFams=["Syne","DM Sans","Arial","Georgia","Courier New","Impact"];
  openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:480px">
    <div class="modal-header"><div class="modal-title">✏ Editar bloco</div><button class="icon-btn" id="m-x">✕</button></div>
    <div class="modal-body">
      <div class="field-row">
        <div class="field"><label>Rótulo *</label><input id="m-nlabel" value="${esc(n.label||"")}" autofocus/></div>
        <div class="field"><label>Detalhe (linha menor)</label><input id="m-ndetail" value="${esc(n.detail||"")}" placeholder="texto menor abaixo do rótulo"/></div>
      </div>
      <div class="field-row">
        <div class="field"><label>Forma</label>
          <select id="m-nshape" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none">
            <option value="rect" ${(n.shape||"rect")==="rect"?"selected":""}>Retângulo</option>
            <option value="diamond" ${n.shape==="diamond"?"selected":""}>Decisão ◇</option>
            <option value="pill" ${n.shape==="pill"?"selected":""}>Pílula</option>
          </select>
        </div>
        <div class="field"><label>Cor</label><input type="color" id="m-ncolor" value="${n.color||"#c8f04e"}" style="width:100%;height:38px;border:none;background:none;cursor:pointer;border-radius:6px"/></div>
      </div>
      <div style="font-size:11px;color:#4a4a5a;background:#13131a;border:1px solid #2e2e3a;border-radius:6px;padding:7px 10px;margin-bottom:4px">💡 Redimensione o bloco arrastando o canto inferior direito diretamente no canvas.</div>
      <div class="field">
        <label>Fonte</label>
        <select id="m-nffam" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none">
          ${["Syne","DM Sans","Arial","Georgia","Courier New","Impact"].map(f=>`<option value="${f}" ${(n.ffam||"Syne")===f?"selected":""}>${f}</option>`).join("")}
        </select>
      </div>
      <div class="field">
        <label>Áreas vinculadas <span style="color:#7a7a8a;font-size:10px">(cor do bloco será dividida entre as áreas)</span></label>
        <div id="m-area-chips" style="display:flex;gap:6px;flex-wrap:wrap;min-height:24px;margin-bottom:6px"></div>
        <select id="m-narea" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none">
          <option value="">+ Adicionar área…</option>
          ${areaOptions}
        </select>
      </div>
      <div class="field">
        <label>Criar nova área e vincular <span style="color:#7a7a8a;font-size:10px">(deixe vazio para não criar)</span></label>
        <div style="display:flex;gap:8px">
          <input id="m-nnewarea" placeholder="Nome da nova área…" style="flex:1;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none"/>
          <input type="color" id="m-nnewareacolor" value="#c8f04e" style="width:38px;height:38px;border:none;background:none;cursor:pointer;border-radius:6px"/>
        </div>
      </div>
    </div>
    <div class="modal-footer">
      <button class="btn-ghost" id="m-cancel">Cancelar</button>
      <button class="btn-primary" id="m-save">Salvar</button>
    </div>
  </div></div>`);
  document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;

  // Multi-area chips
  let selAreaIds=Array.isArray(n.areaIds)?[...n.areaIds]:(n.areaId?[n.areaId]:[]);
  function refreshAreaChips(){
    const el=document.getElementById("m-area-chips");if(!el)return;
    el.innerHTML=selAreaIds.map(aid=>{
      const a=areas[aid];if(!a)return"";
      return`<span style="background:${a.color}22;color:${a.color};border:1px solid ${a.color}55;padding:3px 10px;border-radius:20px;font-size:12px;cursor:pointer" data-aid="${aid}">✕ ${esc(a.name)}</span>`;
    }).join("")||`<span style="font-size:12px;color:#5a5a6a">Nenhuma área</span>`;
    el.querySelectorAll("[data-aid]").forEach(ch=>ch.addEventListener("click",()=>{selAreaIds=selAreaIds.filter(id=>id!==ch.dataset.aid);refreshAreaChips();}));
  }
  refreshAreaChips();
  document.getElementById("m-narea")?.addEventListener("change",e=>{
    const val=e.target.value;
    if(val&&!selAreaIds.includes(val)){selAreaIds.push(val);refreshAreaChips();}
    e.target.value="";
  });

  document.getElementById("m-save").onclick=async()=>{
    const label=document.getElementById("m-nlabel").value.trim(); if(!label){toast("Rótulo obrigatório","error");return;}
    const newAreaName=document.getElementById("m-nnewarea").value.trim();
    if(newAreaName){
      const newColor=document.getElementById("m-nnewareacolor").value||"#c8f04e";
      const newAid=uid();
      await dbSet(`areas/${newAid}`,{name:newAreaName,color:newColor,createdAt:new Date().toISOString()});
      selAreaIds.push(newAid);
      toast(`Área "${newAreaName}" criada!`,"success");
    }
    const updated={...n,
      label,
      detail:document.getElementById("m-ndetail").value.trim()||"",
      shape:document.getElementById("m-nshape").value,
      color:document.getElementById("m-ncolor").value,
      w:n.w||150,
      h:n.h||48,
      fsize:n.fsize||14,
      ffam:document.getElementById("m-nffam").value||"Syne",
      areaIds:selAreaIds.length?selAreaIds:null,
      areaId:selAreaIds[0]||null // backward compat
    };
    await dbSet(`flow/nodes/${nodeId}`,updated);
    toast("Bloco atualizado!","success"); closeModal();
  };
  overlayClose("ov");
}

function addFlowNode(){
  if(Object.keys(flowData.nodes||{}).length>=LIMITS.MAX_FLOW_NODES){toast(`Limite de ${LIMITS.MAX_FLOW_NODES} blocos atingido`,"error");return;}
  const l=document.getElementById("node-label")?.value.trim(),s=document.getElementById("node-shape")?.value||"rect",c=document.getElementById("node-color")?.value||"#c8f04e";
  if(!l)return;
  dbSet(`flow/nodes/${uid()}`,{label:l,color:c,shape:s,areaId:null,x:60+Math.random()*380,y:60+Math.random()*280});
  if(document.getElementById("node-label"))document.getElementById("node-label").value="";
}

// ── EDGE MODAL: nome + detalhes da seta ───────────────────────────────────────
function openEdgeModal(edgeId){
  const e=flowData.edges?.[edgeId];if(!e)return;
  const fromLbl=flowData.nodes?.[e.from]?.label||"?";
  const toLbl=flowData.nodes?.[e.to]?.label||"?";
  const sideOpts=(val)=>["top","right","bottom","left"].map(s=>`<option value="${s}" ${val===s?"selected":""}>${{top:"Cima",right:"Direita",bottom:"Baixo",left:"Esquerda"}[s]}</option>`).join("");
  openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:480px"><div class="modal-header"><div class="modal-title">Editar seta</div><button class="icon-btn" id="m-x">✕</button></div><div class="modal-body">
    <div style="display:flex;align-items:center;gap:8px;margin-bottom:16px;font-size:12px;color:#7a7a8a">
      <span style="background:#1e1e28;border:1px solid #2e2e3a;padding:4px 10px;border-radius:6px;color:#f0eff5">${esc(fromLbl)}</span>
      <span style="color:#7c6eff;font-size:16px">→</span>
      <span style="background:#1e1e28;border:1px solid #2e2e3a;padding:4px 10px;border-radius:6px;color:#f0eff5">${esc(toLbl)}</span>
    </div>
    <div class="field">
      <label>Nome da seta <span style="color:#7a7a8a;font-size:11px">(aparece sobre a seta no fluxograma)</span></label>
      <input id="m-elabel" value="${esc(e.label||"")}" placeholder="Ex: lead criado, aprovado, enviado para estoque…" autofocus/>
    </div>
    <div class="field">
      <label>Detalhes do processo <span style="color:#7a7a8a;font-size:11px">(bloco expandido ao selecionar a seta)</span></label>
      <textarea id="m-edetail" rows="5" placeholder="Descreva o que ocorre neste processo, quem é responsável, documentos, prazos…">${esc(e.detail||"")}</textarea>
    </div>
  </div><div class="modal-footer"><button class="btn-ghost" id="m-cancel">Cancelar</button><button class="btn-primary" id="m-save">Salvar</button></div></div></div>`);
  document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;
  document.getElementById("m-save").onclick=async()=>{
    const label=document.getElementById("m-elabel").value.trim();
    const detail=document.getElementById("m-edetail").value.trim();
    await dbSet(`flow/edges/${edgeId}/label`,label||null);
    await dbSet(`flow/edges/${edgeId}/detail`,detail||null);
    await logAction("editar_seta",`Seta editada: ${fromLbl} -> ${toLbl}${label?" ("+label+")":""}`);
    selEdge=edgeId; closeModal(); render(); toast("Seta atualizada!","success");
  };
  // Show detail popup if there's existing detail
  if(e.detail){
    const detailDiv=document.createElement("div");
    detailDiv.style.cssText="background:#1a1a2e;border:1px solid #7c6eff44;border-radius:8px;padding:10px 14px;margin-top:8px;font-size:12px;color:#a0a0b0;line-height:1.6";
    detailDiv.textContent=e.detail;
  }
  overlayClose("ov");
}


// ── ORGANOGRAMA ───────────────────────────────────────────────────────────────


// ── REPEAT TASK MODAL ─────────────────────────────────────────────────────────
function calcNextRecurDate(task){
  const r=task.recurrence; if(!r||!task.date)return null;
  const base=new Date(task.date+"T00:00:00");
  const d=new Date(base);
  const freq=r.freq||"semanal";
  if(freq==="diaria") d.setDate(d.getDate()+1);
  else if(freq==="semanal") d.setDate(d.getDate()+7);
  else if(freq==="quinzenal") d.setDate(d.getDate()+15);
  else if(freq==="mensal") d.setMonth(d.getMonth()+1);
  else if(freq==="anual") d.setFullYear(d.getFullYear()+1);
  else if(freq==="custom") d.setDate(d.getDate()+(r.interval||7));
  return d.toISOString().slice(0,10);
}

function openRepeatTaskModal(t){
  const hasRecur=!!t.recurrence;
  setTimeout(()=>{
    if(hasRecur&&t.recurrence.cond==="after_complete"){
      // Cria automaticamente sem perguntar
      const nextDate=calcNextRecurDate(t);
      const newId=uid();
      dbSet(`tasks/${newId}`,{...t,id:newId,status:"a-fazer",pinned:false,date:nextDate,completions:null,createdAt:new Date().toISOString()});
      logAction("repetir_tarefa",`Recorrência automática: ${t.title} → ${nextDate?fmtDate(nextDate):"sem prazo"}`);
      const freqLabel={diaria:"diária",semanal:"semanal",quinzenal:"quinzenal",mensal:"mensal",anual:"anual",custom:`a cada ${t.recurrence.interval||7} dias`}[t.recurrence.freq]||"";
      toast(`🔁 Tarefa ${freqLabel} recriada${nextDate?" para "+fmtDate(nextDate):""}!`,"success");
      return;
    }
    // Modal manual (sem recorrência ou data fixa)
    const nextSuggestion=hasRecur?calcNextRecurDate(t):"";
    openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:420px">
      <div class="modal-header"><div class="modal-title">✅ Tarefa concluída!</div><button class="icon-btn" id="m-x">✕</button></div>
      <div class="modal-body">
        <div style="font-size:14px;color:#a0a0b0;margin-bottom:18px">Deseja repetir <strong style="color:#f0eff5">${esc(t.title)}</strong>?</div>
        <div class="field"><label>Novo prazo ${nextSuggestion?"(sugerido: "+fmtDate(nextSuggestion)+")":""}</label><input type="date" id="m-rdate" value="${nextSuggestion||""}"/></div>
      </div>
      <div class="modal-footer">
        <button class="btn-ghost" id="m-no">Não repetir</button>
        <button class="btn-primary" id="m-yes">Repetir tarefa</button>
      </div>
    </div></div>`);
    document.getElementById("m-x").onclick=document.getElementById("m-no").onclick=closeModal;
    document.getElementById("m-yes").onclick=async()=>{
      const newDate=document.getElementById("m-rdate").value;
      const newId=uid();
      await dbSet(`tasks/${newId}`,{...t,id:newId,status:"a-fazer",pinned:false,date:newDate||null,completions:null,createdAt:new Date().toISOString()});
      await logAction("repetir_tarefa","Repetida: "+t.title+(newDate?" → "+fmtDate(newDate):""));
      toast("Tarefa repetida!","success");closeModal();
    };
    overlayClose("ov");
  },300);
}

// ── MINHAS TAREFAS ────────────────────────────────────────────────────────────
function renderMyTasksPage(){
  const myName=currentProfile?.name||"";
  const myAreas=visibleAreas().map(a=>a.id);

  // Tarefas designadas PARA mim (meu nome nos resps)
  const assignedToMe=Object.entries(tasks)
    .map(([id,t])=>({id,...t}))
    .filter(t=>{
      const resps=Array.isArray(t.resps)?t.resps:(t.resp?[t.resp]:[]);
      return resps.some(r=>r===myName);
    })
    .sort((a,b)=>new Date(a.date||"9999")-new Date(b.date||"9999"));

  // Tarefas que EU criei (e designei a outros)
  const createdByMe=Object.entries(tasks)
    .map(([id,t])=>({id,...t}))
    .filter(t=>t.creatorId===currentUser?.uid)
    .sort((a,b)=>new Date(a.date||"9999")-new Date(b.date||"9999"));

  // Tarefas das minhas áreas (visibilidade geral da área)
  const areaVisible=Object.entries(tasks)
    .map(([id,t])=>({id,...t}))
    .filter(t=>myAreas.includes(t.areaId)&&t.creatorId!==currentUser?.uid)
    .filter(t=>{
      const resps=Array.isArray(t.resps)?t.resps:(t.resp?[t.resp]:[]);
      return!resps.some(r=>r===myName); // exclude already shown in "to me"
    })
    .sort((a,b)=>new Date(a.date||"9999")-new Date(b.date||"9999"));

  function taskRow(t,showArea=true){
    const st=STATUS[t.status];
    const resps=Array.isArray(t.resps)?t.resps:(t.resp?[t.resp]:[]);
    const ar=areas[t.areaId];
    const dl=deadlineClass(t.date);
    return`<div class="task-row btn-detail-task" data-id="${t.id}" style="display:flex;align-items:center;gap:12px;padding:10px 14px;background:#13131a;border:1px solid #1e1e28;border-radius:8px;margin-bottom:6px;cursor:pointer;transition:background .12s;${t.pinned?"border-left:3px solid #c8f04e;":""}">
      <span style="width:8px;height:8px;border-radius:50%;background:${st?.color};flex-shrink:0"></span>
      <div style="flex:1;min-width:0">
        <div style="font-size:13px;font-weight:500;white-space:nowrap;overflow:hidden;text-overflow:ellipsis">${esc(t.title)}</div>
        <div style="display:flex;gap:8px;flex-wrap:wrap;margin-top:3px">
          <span style="font-size:10px;color:${st?.color}">${st?.label}</span>
          ${showArea&&ar?`<span style="font-size:10px;color:#7a7a8a">📁 ${esc(ar.name)}</span>`:""}
          ${resps.length?`<span style="font-size:10px;color:#9d93ff">👤 ${resps.join(", ")}</span>`:""}
          ${t.creatorName?`<span style="font-size:10px;color:#5a5a6a">por ${esc(t.creatorName)}</span>`:""}
          ${t.createdAt?`<span style="font-size:10px;color:#3a3a4a">🕐 ${fmtDate(t.createdAt.slice(0,10))}</span>`:""}
        </div>
      </div>
      ${t.date?`<span style="font-size:10px;color:${dl?"#f0a832":"#7a7a8a"};white-space:nowrap;flex-shrink:0">${fmtDate(t.date)}</span>`:""}
      ${deadlineBadge(t.date)}
    </div>`;
  }

  const section=(title,icon,list,emptyMsg,showArea=true)=>`
    <div style="margin-bottom:28px">
      <div style="font-family:'Syne',sans-serif;font-size:14px;font-weight:700;margin-bottom:10px;display:flex;align-items:center;gap:8px">
        <span>${icon}</span>${title}
        <span style="font-size:11px;color:#7a7a8a;font-weight:400;font-family:'DM Sans',sans-serif">(${list.length})</span>
      </div>
      ${list.length?list.map(t=>taskRow(t,showArea)).join(""):`<div style="font-size:12px;color:#4a4a5a;padding:16px;text-align:center;background:#0e0e14;border-radius:8px">${emptyMsg}</div>`}
    </div>`;

  return`<div class="page-header"><div><div class="page-title">Minhas Tarefas</div><div class="page-sub">Suas atribuições e tarefas das suas áreas</div></div></div>
    ${section("Designadas para mim","📥",assignedToMe,"Nenhuma tarefa designada para você")}
    ${section("Criadas por mim","📤",createdByMe,"Você ainda não criou nenhuma tarefa")}
    ${section("Outras tarefas nas minhas áreas","📁",areaVisible,"Sem outras tarefas nas suas áreas")}`;
}


let areaCalCollapsed={}; // {areaId: true/false} — persiste na sessão
let calYear=new Date().getFullYear(), calMonth=new Date().getMonth();
let calAreaFilter=[]; // [] = todas; array de areaIds = filtrado. Reseta ao sair do calendário
let freelaYear=new Date().getFullYear(), freelaMonth=new Date().getMonth();
let freelaEvents={};
let prospYear=new Date().getFullYear(), prospMonth=new Date().getMonth();
let prospEvents={};

const CAL_PRIORITY={
  essential:{label:"Essencial",color:"#ff6b6b",alertDays:[3,2,1,0]},
  important:{label:"Importante",color:"#f0a832",alertDays:[2,1]}
};

function renderCalPage(){
  const today=new Date(); today.setHours(0,0,0,0);
  const yr=calYear, mo=calMonth;
  const firstDay=new Date(yr,mo,1);
  const lastDay=new Date(yr,mo+1,0);
  const startWd=(firstDay.getDay()+6)%7; // Mon=0
  const totalCells=Math.ceil((startWd+lastDay.getDate())/7)*7;
  const monthNames=["Janeiro","Fevereiro","Março","Abril","Maio","Junho","Julho","Agosto","Setembro","Outubro","Novembro","Dezembro"];
  const dayNames=["Seg","Ter","Qua","Qui","Sex","Sáb","Dom"];

  // Build map: dateStr -> [events]
  const eventMap={};
  const myVisibleAreaIds=visibleAreas().map(a=>a.id);
  // Filtro de área — se vazio mostra todas as áreas visíveis
  const activeAreaIds=calAreaFilter.length?calAreaFilter.filter(id=>myVisibleAreaIds.includes(id)):myVisibleAreaIds;
  Object.entries(tasks).forEach(([tid,t])=>{
    if(!t.date)return;
    if(!activeAreaIds.includes(t.areaId))return;
    if(!eventMap[t.date])eventMap[t.date]=[];
    const resps=Array.isArray(t.resps)?t.resps:(t.resp?[t.resp]:[]);
    eventMap[t.date].push({type:"task",id:tid,title:t.title,color:STATUS[t.status]?.color||"#7c6eff",status:t.status,area:areas[t.areaId]?.name||"",resps});
  });
  // Calendar events + freela events (unified) — filtrados pela área se ativo
  const allCalEvents={...calEvents,...freelaEvents};
  Object.entries(allCalEvents).forEach(([eid,e])=>{
    if(!e.dateStart)return;
    // Filtrar por área se houver filtro ativo
    if(calAreaFilter.length){
      // Evento sem área vinculada: ocultar quando filtro ativo
      if(!e.areaId||!calAreaFilter.includes(e.areaId))return;
    }
    const start=new Date(e.dateStart+"T00:00:00");
    const end=e.dateEnd?new Date(e.dateEnd+"T00:00:00"):start;
    for(let d=new Date(start);d<=end;d.setDate(d.getDate()+1)){
      const ds=d.toISOString().slice(0,10);
      if(!eventMap[ds])eventMap[ds]=[];
      const isFirst=ds===e.dateStart, isLast=ds===(e.dateEnd||e.dateStart);
      const span=e.dateEnd&&e.dateEnd!==e.dateStart;
      const evColor=e.color||(e.priority&&CAL_PRIORITY[e.priority]?.color)||"#7c6eff";
      eventMap[ds].push({type:"event",id:eid,title:e.title,color:evColor,priority:e.priority,isFirst,isLast,span,person:e.person||"",note:e.note||""});
    }
  });

  // Render cells
  let cells="";
  for(let i=0;i<totalCells;i++){
    const dayNum=i-startWd+1;
    const isCurrentMonth=dayNum>=1&&dayNum<=lastDay.getDate();
    const cellDate=new Date(yr,mo,dayNum);
    const ds=cellDate.toISOString().slice(0,10);
    const isToday=isCurrentMonth&&cellDate.getTime()===today.getTime();
    const isPast=isCurrentMonth&&cellDate<today;
    const evs=eventMap[ds]||[];
    const taskEvs=evs.filter(e=>e.type==="task");
    const calEvs=evs.filter(e=>e.type==="event");
    const calChips=calEvs.map(e=>`<div class="cal-event-chip ${e.span&&!e.isFirst?"chip-cont":""} ${e.span&&!e.isLast?"chip-start":""}" data-eid="${e.id}" style="background:${e.color}22;border-left:3px solid ${e.color};color:${e.color};font-size:9px;padding:2px 5px;border-radius:3px;margin-top:2px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;cursor:pointer;max-width:100%">${e.isFirst||!e.span?"🗓 "+esc(e.title.slice(0,14)):(e.span?"…"+esc(e.title.slice(0,10)):"")}</div>`).join("");
    // Single task: show title inline; multiple tasks: show dots + count
    const taskBlock=taskEvs.length===1
      ?`<div class="cal-task-chip" data-date="${ds}" data-tid="${taskEvs[0].id}" style="display:flex;align-items:center;gap:3px;margin-top:3px;padding:2px 4px;border-radius:3px;cursor:pointer;background:${taskEvs[0].color}12;border-left:2px solid ${taskEvs[0].color}">
          <span style="width:5px;height:5px;border-radius:50%;background:${taskEvs[0].color};flex-shrink:0"></span>
          <span style="font-size:9px;color:${taskEvs[0].color};overflow:hidden;text-overflow:ellipsis;white-space:nowrap;max-width:90%">${esc(taskEvs[0].title.slice(0,16)+(taskEvs[0].title.length>16?"…":""))}</span>
        </div>`
      :taskEvs.length>1
      ?`<div style="margin-top:3px;display:flex;flex-wrap:wrap;gap:1px;padding:0 3px;align-items:center">
          ${taskEvs.slice(0,3).map(e=>`<span style="display:inline-block;width:7px;height:7px;border-radius:50%;background:${e.color};margin:0 1px"></span>`).join("")}
          ${taskEvs.length>3?`<span style="font-size:9px;color:#7a7a8a">+${taskEvs.length-3}</span>`:""}
        </div>
        <div class="cal-task-count" data-date="${ds}" style="font-size:9px;color:#7a7a8a;padding:0 4px;cursor:pointer">${taskEvs.length} tarefas</div>`
      :"";
    cells+=`<div class="cal-cell ${isToday?"cal-today":""} ${!isCurrentMonth?"cal-other":""} ${isPast&&isCurrentMonth?"cal-past":""}" data-date="${isCurrentMonth?ds:""}" style="min-height:88px">
      <div class="cal-day-num" style="${isToday?"background:#c8f04e;color:#0c0c0f;":""}${!isCurrentMonth?"color:#2e2e3a;":""}">${isCurrentMonth?dayNum:""}</div>
      ${calChips}
      ${taskBlock}
    </div>`;
  }

  // Upcoming alerts sidebar
  const upcoming=[];
  const nowMs=today.getTime();
  Object.entries({...calEvents,...freelaEvents}).forEach(([eid,e])=>{
    if(!e.dateStart)return;
    if(calAreaFilter.length&&(!e.areaId||!calAreaFilter.includes(e.areaId)))return;
    const ms=new Date(e.dateStart+"T00:00:00").getTime();
    const diffDays=Math.round((ms-nowMs)/86400000);
    if(diffDays>=0&&diffDays<=3)upcoming.push({...e,id:eid,diffDays});
  });
  Object.entries(tasks).forEach(([tid,t])=>{
    if(!t.date||t.status==="concluido")return;
    if(!activeAreaIds.includes(t.areaId))return;
    const ms=new Date(t.date+"T23:59:59").getTime();
    const diffDays=Math.round((ms-nowMs)/86400000);
    if(diffDays>=0&&diffDays<=3)upcoming.push({id:tid,title:t.title,color:STATUS[t.status]?.color||"#7c6eff",diffDays,type:"task",area:areas[t.areaId]?.name||""});
  });
  upcoming.sort((a,b)=>a.diffDays-b.diffDays);

  const upcomingHtml=upcoming.length?upcoming.map(e=>{
    const label=e.diffDays===0?"Hoje":e.diffDays===1?"Amanhã":`${e.diffDays} dias`;
    return`<div style="display:flex;gap:10px;align-items:flex-start;padding:8px 0;border-bottom:1px solid #1e1e28">
      <div style="background:${e.color}22;color:${e.color};border:1px solid ${e.color}44;padding:3px 8px;border-radius:6px;font-size:10px;font-weight:700;white-space:nowrap;min-width:54px;text-align:center">${esc(label)}</div>
      <div>
        <div style="font-size:12px;font-weight:600;color:#f0eff5">${esc(e.title)}</div>
        <div style="font-size:10px;color:#7a7a8a">${e.type==="task"?("Tarefa"+( e.area?" · "+e.area:"")):(CAL_PRIORITY[e.priority]?.label||"")+(e.person?" · "+e.person:"")}</div>
      </div>
    </div>`;
  }).join(""):`<div style="font-size:12px;color:#5a5a6a;text-align:center;padding:20px 0">Nenhum evento nos próximos 3 dias</div>`;

  const filterChips=visibleAreas().map(a=>{
    const on=calAreaFilter.includes(a.id);
    return`<button class="cal-area-filter" data-aid="${a.id}" style="border:1px solid ${on?a.color:"#2e2e3a"};color:${on?a.color:"#7a7a8a"};background:${on?a.color+"18":"transparent"};border-radius:20px;padding:3px 10px;font-size:11px;cursor:pointer;white-space:nowrap">${esc(a.name)}</button>`;
  }).join("");

  return`<div class="page-header">
    <div><div class="page-title">Calendário</div><div class="page-sub">Prazos, eventos e agendamentos da equipe</div></div>
    <button class="btn-primary" id="btn-new-event">+ Novo Evento</button>
  </div>
  ${filterChips?`<div style="display:flex;gap:6px;flex-wrap:wrap;margin-bottom:12px;align-items:center">
    <span style="font-size:11px;color:#7a7a8a">Filtrar tarefas:</span>
    ${filterChips}
    ${calAreaFilter.length?`<button id="cal-filter-clear" style="border:1px solid #ff6b6b44;color:#ff6b6b;background:transparent;border-radius:20px;padding:3px 10px;font-size:11px;cursor:pointer">✕ Limpar</button>`:""}
  </div>`:""}
  <div style="display:grid;grid-template-columns:1fr 240px;gap:20px;align-items:start">
    <div>
      <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:14px">
        <button class="btn-small" id="cal-prev" style="border:1px solid #2e2e3a;color:#f0eff5">‹ Anterior</button>
        <div style="font-family:'Syne',sans-serif;font-size:17px;font-weight:700">${monthNames[mo]} ${yr}</div>
        <button class="btn-small" id="cal-next" style="border:1px solid #2e2e3a;color:#f0eff5">Próximo ›</button>
      </div>
      <div class="cal-grid">
        ${dayNames.map(d=>`<div class="cal-header-cell">${d}</div>`).join("")}
        ${cells}
      </div>
      <div style="display:flex;gap:16px;margin-top:10px;font-size:11px;color:#5a5a6a;flex-wrap:wrap">
        <span><span style="display:inline-block;width:8px;height:8px;border-radius:50%;background:#ff6b6b;margin-right:4px"></span>Essencial</span>
        <span><span style="display:inline-block;width:8px;height:8px;border-radius:50%;background:#f0a832;margin-right:4px"></span>Importante</span>
        <span><span style="display:inline-block;width:8px;height:8px;border-radius:50%;background:#7c6eff;margin-right:4px"></span>Tarefa com prazo</span>
        <span style="margin-left:auto">🗓 Clique num dia para ver detalhes</span>
      </div>
    </div>
    <div style="background:#13131a;border:1px solid #1e1e28;border-radius:12px;padding:16px">
      <div style="font-size:12px;font-weight:700;text-transform:uppercase;letter-spacing:1px;color:#7a7a8a;margin-bottom:12px">Próximos 3 dias</div>
      ${upcomingHtml}
    </div>
  </div>`;
}

function attachCalEvents(){
  document.getElementById("cal-prev")?.addEventListener("click",()=>{calMonth--;if(calMonth<0){calMonth=11;calYear--;}render();});
  document.getElementById("cal-next")?.addEventListener("click",()=>{calMonth++;if(calMonth>11){calMonth=0;calYear++;}render();});
  document.getElementById("cal-filter-clear")?.addEventListener("click",()=>{calAreaFilter=[];render();});
  document.querySelectorAll(".cal-area-filter").forEach(btn=>{
    btn.addEventListener("click",()=>{
      const aid=btn.dataset.aid;
      if(calAreaFilter.includes(aid)) calAreaFilter=calAreaFilter.filter(id=>id!==aid);
      else calAreaFilter.push(aid);
      render();
    });
  });
  // Use setTimeout to ensure DOM is ready after render
  setTimeout(()=>document.getElementById("btn-new-event")?.addEventListener("click",()=>openCalEventModal(null,null)),0);

  // Click on day cell → abre detalhes do dia
  document.querySelectorAll(".cal-cell[data-date]").forEach(el=>{
    el.addEventListener("click",e=>{
      if(e.target.classList.contains("cal-event-chip")||e.target.classList.contains("cal-task-count")||e.target.classList.contains("cal-task-chip"))return;
      const ds=el.dataset.date; if(!ds)return;
      openCalDayModal(ds);
    });
  });

  // Click on event chip
  document.querySelectorAll(".cal-event-chip[data-eid]").forEach(el=>{
    el.addEventListener("click",e=>{e.stopPropagation();openCalEventDetailModal(el.dataset.eid);});
  });

  // Click on single task chip → open detail
  document.querySelectorAll(".cal-task-chip[data-tid]").forEach(el=>{
    el.addEventListener("click",e=>{e.stopPropagation();openDetailModal(el.dataset.tid);});
  });
  // Click on task count
  document.querySelectorAll(".cal-task-count[data-date]").forEach(el=>{
    el.addEventListener("click",e=>{e.stopPropagation();openCalDayModal(el.dataset.date);});
  });
}

// ── FREELA CALENDAR ───────────────────────────────────────────────────────────
const FREELA_COLORS=["#c8f04e","#7c6eff","#4ac8e8","#f0a832","#ff6b6b","#4ae89c","#e84ab8"];

function renderFreelaPage(){
  const today=new Date(); today.setHours(0,0,0,0);
  const yr=freelaYear, mo=freelaMonth;
  const firstDay=new Date(yr,mo,1);
  const lastDay=new Date(yr,mo+1,0);
  const startWd=(firstDay.getDay()+6)%7;
  const totalCells=Math.ceil((startWd+lastDay.getDate())/7)*7;
  const monthNames=["Janeiro","Fevereiro","Março","Abril","Maio","Junho","Julho","Agosto","Setembro","Outubro","Novembro","Dezembro"];
  const dayNames=["Seg","Ter","Qua","Qui","Sex","Sáb","Dom"];

  // Build event map
  const eventMap={};
  Object.entries(freelaEvents).forEach(([eid,e])=>{
    if(!e.dateStart)return;
    const start=new Date(e.dateStart+"T00:00:00");
    const end=e.dateEnd?new Date(e.dateEnd+"T00:00:00"):start;
    for(let d=new Date(start);d<=end;d.setDate(d.getDate()+1)){
      const ds=d.toISOString().slice(0,10);
      if(!eventMap[ds])eventMap[ds]=[];
      const isFirst=ds===e.dateStart, isLast=ds===(e.dateEnd||e.dateStart);
      const span=!!(e.dateEnd&&e.dateEnd!==e.dateStart);
      eventMap[ds].push({id:eid,title:e.title,color:e.color||"#7c6eff",isFirst,isLast,span,note:e.note||"",client:e.client||""});
    }
  });

  let cells="";
  for(let i=0;i<totalCells;i++){
    const dayNum=i-startWd+1;
    const isCurrentMonth=dayNum>=1&&dayNum<=lastDay.getDate();
    const cellDate=new Date(yr,mo,dayNum);
    const ds=cellDate.toISOString().slice(0,10);
    const isToday=isCurrentMonth&&cellDate.getTime()===today.getTime();
    const isPast=isCurrentMonth&&cellDate<today;
    const evs=eventMap[ds]||[];
    const chips=evs.map(e=>`<div class="freela-chip" data-eid="${e.id}" style="background:${e.color}22;border-left:3px solid ${e.color};color:${e.color};font-size:9px;padding:2px 5px;border-radius:3px;margin-top:2px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;cursor:pointer;max-width:100%">${e.isFirst||!e.span?"📌 "+esc(e.title.slice(0,15)):"↳ "+esc(e.title.slice(0,12))}</div>`).join("");
    cells+=`<div class="cal-cell freela-cell ${isToday?"cal-today":""} ${!isCurrentMonth?"cal-other":""} ${isPast&&isCurrentMonth?"cal-past":""}" data-date="${isCurrentMonth?ds:""}" style="min-height:88px;cursor:pointer">
      <div class="cal-day-num" style="${isToday?"background:#7c6eff;color:#fff;":""}${!isCurrentMonth?"color:#2e2e3a;":""}">${isCurrentMonth?dayNum:""}</div>
      ${chips}
    </div>`;
  }

  // Upcoming sidebar — next 7 days
  const nowMs=today.getTime();
  const upcoming=Object.entries(freelaEvents).map(([id,e])=>{
    if(!e.dateStart)return null;
    const ms=new Date(e.dateStart+"T00:00:00").getTime();
    const diff=Math.round((ms-nowMs)/86400000);
    if(diff<0||diff>7)return null;
    return{id,...e,diff};
  }).filter(Boolean).sort((a,b)=>a.diff-b.diff);

  const upHtml=upcoming.length?upcoming.map(e=>{
    const lbl=e.diff===0?"Hoje":e.diff===1?"Amanhã":`${e.diff} dias`;
    return`<div style="display:flex;gap:8px;align-items:flex-start;padding:8px 0;border-bottom:1px solid #1e1e28">
      <div style="background:${e.color||"#7c6eff"}22;color:${e.color||"#7c6eff"};border:1px solid ${e.color||"#7c6eff"}44;padding:3px 6px;border-radius:6px;font-size:10px;font-weight:700;white-space:nowrap;min-width:48px;text-align:center">${lbl}</div>
      <div>
        <div style="font-size:12px;font-weight:600;color:#f0eff5">${esc(e.title)}</div>
        ${e.client?`<div style="font-size:10px;color:#7a7a8a">👤 ${esc(e.client)}</div>`:""}
        ${e.note?`<div style="font-size:10px;color:#5a5a6a">${esc(e.note.slice(0,40))}</div>`:""}
      </div>
    </div>`;
  }).join(""):`<div style="font-size:12px;color:#5a5a6a;text-align:center;padding:20px 0">Sem freelas nos próximos 7 dias</div>`;

  // Quick-add panel (top right corner block)
  const quickAdd=`<div id="freela-quick-add" style="background:#13131a;border:1px solid #2e2e3a;border-radius:10px;padding:14px;margin-bottom:18px">
    <div style="font-family:'Syne',sans-serif;font-size:13px;font-weight:700;margin-bottom:10px;color:#c8f04e">+ Novo Agendamento</div>
    <div style="display:flex;flex-direction:column;gap:8px">
      <input id="fq-title" placeholder="Título *" style="background:#0e0e14;border:1px solid #2e2e3a;border-radius:6px;padding:7px 10px;color:#f0eff5;font-family:'DM Sans',sans-serif;font-size:12px;outline:none"/>
      <input id="fq-client" placeholder="Cliente (opcional)" style="background:#0e0e14;border:1px solid #2e2e3a;border-radius:6px;padding:7px 10px;color:#f0eff5;font-family:'DM Sans',sans-serif;font-size:12px;outline:none"/>
      <div style="display:flex;gap:6px">
        <div style="flex:1">
          <div style="font-size:10px;color:#7a7a8a;margin-bottom:3px">Tipo</div>
          <select id="fq-type" style="width:100%;background:#0e0e14;border:1px solid #2e2e3a;border-radius:6px;padding:6px 8px;color:#f0eff5;font-family:'DM Sans',sans-serif;font-size:12px;outline:none">
            <option value="single">Dia único</option>
            <option value="range">Período</option>
          </select>
        </div>
        <div style="flex:1">
          <div style="font-size:10px;color:#7a7a8a;margin-bottom:3px">Cor</div>
          <select id="fq-color" style="width:100%;background:#0e0e14;border:1px solid #2e2e3a;border-radius:6px;padding:6px 8px;color:#f0eff5;font-family:'DM Sans',sans-serif;font-size:12px;outline:none">
            ${FREELA_COLORS.map((c,i)=>`<option value="${c}" style="background:${c}">${["Verde","Roxo","Azul","Laranja","Vermelho","Verde-água","Rosa"][i]}</option>`).join("")}
          </select>
        </div>
      </div>
      <div id="fq-dates" style="display:flex;flex-direction:column;gap:6px">
        <input type="date" id="fq-start" style="background:#0e0e14;border:1px solid #2e2e3a;border-radius:6px;padding:6px 10px;color:#f0eff5;font-family:'DM Sans',sans-serif;font-size:12px;outline:none"/>
        <input type="date" id="fq-end" id="fq-end" style="display:none;background:#0e0e14;border:1px solid #2e2e3a;border-radius:6px;padding:6px 10px;color:#f0eff5;font-family:'DM Sans',sans-serif;font-size:12px;outline:none" placeholder="Data fim"/>
      </div>
      <textarea id="fq-note" rows="2" placeholder="Observações…" style="background:#0e0e14;border:1px solid #2e2e3a;border-radius:6px;padding:7px 10px;color:#f0eff5;font-family:'DM Sans',sans-serif;font-size:12px;outline:none;resize:none"></textarea>
      <button id="fq-save" style="background:#7c6eff;border:none;border-radius:6px;padding:8px;color:#fff;font-family:'Syne',sans-serif;font-size:12px;font-weight:700;cursor:pointer">Agendar</button>
    </div>
  </div>`;

  return`<div class="page-header">
    <div><div class="page-title">Calendário Ajudante</div><div class="page-sub">Agendamentos e projetos de apoio</div></div>
  </div>
  <div style="display:grid;grid-template-columns:1fr 240px;gap:20px;align-items:start">
    <div>
      <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:14px">
        <button class="btn-small" id="freela-prev" style="border:1px solid #2e2e3a;color:#f0eff5">‹ Anterior</button>
        <div style="font-family:'Syne',sans-serif;font-size:17px;font-weight:700">${monthNames[mo]} ${yr}</div>
        <button class="btn-small" id="freela-next" style="border:1px solid #2e2e3a;color:#f0eff5">Próximo ›</button>
      </div>
      <div class="cal-grid">
        ${dayNames.map(d=>`<div class="cal-header-cell">${d}</div>`).join("")}
        ${cells}
      </div>
      <div style="margin-top:10px;font-size:11px;color:#5a5a6a">🗓 Clique num dia ou evento para gerenciar</div>
    </div>
    <div>
      ${quickAdd}
      <div style="background:#13131a;border:1px solid #1e1e28;border-radius:12px;padding:16px">
        <div style="font-size:12px;font-weight:700;text-transform:uppercase;letter-spacing:1px;color:#7a7a8a;margin-bottom:12px">Próximos 7 dias</div>
        ${upHtml}
      </div>
    </div>
  </div>`;
}

function attachFreelaEvents(){
  document.getElementById("freela-prev")?.addEventListener("click",()=>{freelaMonth--;if(freelaMonth<0){freelaMonth=11;freelaYear--;}render();});
  document.getElementById("freela-next")?.addEventListener("click",()=>{freelaMonth++;if(freelaMonth>11){freelaMonth=0;freelaYear++;}render();});

  // Type toggle — show/hide end date
  const typeEl=document.getElementById("fq-type");
  const endEl=document.getElementById("fq-end");
  typeEl?.addEventListener("change",()=>{if(endEl)endEl.style.display=typeEl.value==="range"?"":"none";});

  // Click on day to prefill date
  document.querySelectorAll(".freela-cell[data-date]").forEach(el=>{
    el.addEventListener("click",e=>{
      if(e.target.classList.contains("freela-chip"))return;
      const ds=el.dataset.date; if(!ds)return;
      const startEl=document.getElementById("fq-start");
      if(startEl)startEl.value=ds;
    });
  });

  // Click on chip → edit modal
  document.querySelectorAll(".freela-chip[data-eid]").forEach(el=>{
    el.addEventListener("click",e=>{e.stopPropagation();openFreelaEventModal(el.dataset.eid);});
  });

  // Save quick add
  document.getElementById("fq-save")?.addEventListener("click",async()=>{
    const title=document.getElementById("fq-title")?.value.trim();
    const client=document.getElementById("fq-client")?.value.trim();
    const type=document.getElementById("fq-type")?.value;
    const color=document.getElementById("fq-color")?.value||"#7c6eff";
    const dateStart=document.getElementById("fq-start")?.value;
    const dateEnd=type==="range"?document.getElementById("fq-end")?.value:"";
    const note=document.getElementById("fq-note")?.value.trim();
    if(!title){toast("Digite um título","error");return;}
    if(!dateStart){toast("Selecione uma data","error");return;}
    const data={title,client:client||"",color,dateStart,dateEnd:dateEnd||"",note:note||"",createdBy:currentUser.uid,createdAt:new Date().toISOString()};
    await dbSet(`freela_events/${uid()}`,data);
    // clear form
    ["fq-title","fq-client","fq-start","fq-end","fq-note"].forEach(id=>{const el=document.getElementById(id);if(el)el.value="";});
    toast("Agendado!","success");
  });
}

function openFreelaEventModal(eventId){
  const ev=freelaEvents[eventId]; if(!ev)return;
  const color=ev.color||"#7c6eff";
  openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:460px">
    <div class="modal-header" style="border-bottom:2px solid ${color}44"><div class="modal-title">📌 ${esc(ev.title)}</div><button class="icon-btn" id="m-x">✕</button></div>
    <div class="modal-body">
      <div style="display:flex;gap:14px;flex-wrap:wrap;font-size:13px;margin-bottom:12px">
        <span>📅 ${fmtDate(ev.dateStart)}${ev.dateEnd&&ev.dateEnd!==ev.dateStart?" → "+fmtDate(ev.dateEnd):""}</span>
        ${ev.client?`<span>👤 ${esc(ev.client)}</span>`:""}
      </div>
      ${ev.note?`<div style="font-size:13px;color:#a0a0b0;line-height:1.7;background:#13131a;border-radius:8px;padding:10px 14px">${esc(ev.note)}</div>`:""}
    </div>
    <div class="modal-footer">
      <button class="btn-ghost" id="m-x2">Fechar</button>
      <button class="btn-danger" id="m-del-freela">🗑 Excluir</button>
    </div>
  </div></div>`);
  document.getElementById("m-x").onclick=document.getElementById("m-x2").onclick=closeModal;
  document.getElementById("m-del-freela").onclick=async()=>{
    if(confirm("Excluir este agendamento?")){await dbRemove(`freela_events/${eventId}`);closeModal();toast("Excluído","warning");}
  };
}

// ── CALENDÁRIO PROSPECÇÃO ─────────────────────────────────────────────────────
const PROSP_SEED=[
  {title:"Búzios Sailing Week Oceano",dateStart:"2026-04-02",dateEnd:"2026-04-05",color:"#4ac8e8"},
  {title:"Via Sacra",dateStart:"2026-04-03",color:"#c8f04e"},
  {title:"Desafio das Ilhas – Búzios Swim",dateStart:"2026-04-12",color:"#f0a832"},
  {title:"Estadual de Va'a – RJ",dateStart:"2026-04-18",dateEnd:"2026-04-19",color:"#7c6eff"},
  {title:"Águas Abertas",dateStart:"2026-04-24",dateEnd:"2026-04-25",color:"#4ac8e8"},
  {title:"Búzios Jazz Festival",dateStart:"2026-05-01",dateEnd:"2026-05-03",color:"#f0a832"},
  {title:"Campeonato de Motocross",dateStart:"2026-05-08",dateEnd:"2026-05-09",color:"#e8624a"},
  {title:"Circuito Mundial de Beach Tennis",dateStart:"2026-05-13",dateEnd:"2026-05-17",color:"#c8f04e"},
  {title:"Estadual de Surf",dateStart:"2026-05-23",dateEnd:"2026-05-24",color:"#4ac8e8"},
  {title:"Mi Búzios",dateStart:"2026-05-29",dateEnd:"2026-05-30",color:"#7c6eff"},
  {title:"Wine in Búzios",dateStart:"2026-06-02",dateEnd:"2026-06-07",color:"#a84ae8"},
  {title:"Corpus Christ",dateStart:"2026-06-04",color:"#c8f04e"},
  {title:"Búzios Sailing Week Monotipo",dateStart:"2026-06-04",dateEnd:"2026-06-07",color:"#4ac8e8"},
  {title:"Semana Gospel",dateStart:"2026-06-05",dateEnd:"2026-06-06",color:"#f0a832"},
  {title:"Nativo Swim Run – Búzios",dateStart:"2026-06-07",color:"#4ac8e8"},
  {title:"Anarriê",dateStart:"2026-06-19",dateEnd:"2026-06-20",color:"#e8624a"},
  {title:"Make Music Day",dateStart:"2026-06-21",color:"#c8f04e"},
  {title:"Festa dos Pescadores",dateStart:"2026-06-26",dateEnd:"2026-06-29",color:"#4a7ee8"},
  {title:"Festa do Divino",dateStart:"2026-07-05",color:"#f0a832"},
  {title:"2ª Corrida das Guardas de Búzios",dateStart:"2026-07-05",color:"#e8624a"},
  {title:"Semana LGBT+ de Búzios",dateStart:"2026-07-11",color:"#a84ae8"},
  {title:"Pride Búzios",dateStart:"2026-07-12",color:"#e84ab8"},
  {title:"Paralimpíadas de Búzios",dateStart:"2026-07-19",color:"#7c6eff"},
  {title:"Búzios On",dateStart:"2026-07-24",dateEnd:"2026-07-25",color:"#c8f04e"},
  {title:"Festa de Sant'Anna",dateStart:"2026-07-24",dateEnd:"2026-07-26",color:"#f0a832"},
  {title:"Búzios Sailing Week Optimis",dateStart:"2026-07-24",dateEnd:"2026-07-26",color:"#4ac8e8"},
  {title:"Degusta",dateStart:"2026-08-31",dateEnd:"2026-09-02",color:"#e8a84a"},
  {title:"Degusta (2ª etapa)",dateStart:"2026-08-07",dateEnd:"2026-08-09",color:"#e8a84a"},
  {title:"Mr.Búzios",dateStart:"2026-08-15",color:"#e84ab8"},
  {title:"Hero Swim Run",dateStart:"2026-08-22",color:"#4ac8e8"},
  {title:"Encontro de Motos",dateStart:"2026-08-27",dateEnd:"2026-08-30",color:"#e8624a"},
  {title:"Circuito das Artes",dateStart:"2026-09-03",dateEnd:"2026-09-05",color:"#a84ae8"},
  {title:"Evento Petz",dateStart:"2026-09-11",dateEnd:"2026-09-12",color:"#c8f04e"},
  {title:"Festival da Sardinha e Frutos do Mar",dateStart:"2026-09-18",dateEnd:"2026-09-19",color:"#4ac8e8"},
  {title:"Parafina",dateStart:"2026-09-24",dateEnd:"2026-09-27",color:"#7c6eff"},
  {title:"Búzios Café e Chocolate",dateStart:"2026-09-25",dateEnd:"2026-09-27",color:"#e8a84a"},
  {title:"MPBúzios",dateStart:"2026-10-09",dateEnd:"2026-10-11",color:"#c8f04e"},
  {title:"Dia das Crianças",dateStart:"2026-10-12",color:"#f0a832"},
  {title:"Circuito Bike Lagos",dateStart:"2026-10-13",color:"#4ac8e8"},
  {title:"XC Run Búzios",dateStart:"2026-10-18",color:"#e8624a"},
  {title:"1ª Copa Triathlon – RJ",dateStart:"2026-11-01",color:"#7c6eff"},
  {title:"Festa Literária",dateStart:"2026-11-09",dateEnd:"2026-11-11",color:"#a84ae8"},
  {title:"Festa da Cidade",dateStart:"2026-11-12",dateEnd:"2026-11-14",color:"#c8f04e"},
  {title:"Consciência Negra",dateStart:"2026-11-20",color:"#f0a832"},
  {title:"Carros Antigos",dateStart:"2026-11-27",dateEnd:"2026-11-28",color:"#e8624a"},
  {title:"Natal de Luz",dateStart:"2026-12-01",dateEnd:"2026-12-31",color:"#c8f04e"},
  {title:"Meia Maratona de Búzios",dateStart:"2026-12-06",color:"#4ac8e8"},
  {title:"Cantata de Natal",dateStart:"2026-12-11",dateEnd:"2026-12-12",color:"#f0a832"},
  // ── Calendário Maricá ──
  {title:"Páscoa / Cinema Inflável",dateStart:"2026-04-03",dateEnd:"2026-04-05",color:"#f0a832",note:"Calendário Marica"},
  {title:"Paixão de Cristo",dateStart:"2026-04-10",dateEnd:"2026-04-11",color:"#7c6eff",note:"Calendário Marica"},
  {title:"Páscoa das Comunidades",dateStart:"2026-04-11",color:"#c8f04e",note:"Calendário Marica"},
  {title:"Espraiado de Portas Abertas",dateStart:"2026-04-12",color:"#4ac8e8",note:"Calendário Marica"},
  {title:"Celebração do Dia dos Povos Indígenas",dateStart:"2026-04-19",color:"#4ae89c",note:"Calendário Marica"},
  {title:"Festival Nacional do Choro",dateStart:"2026-04-23",dateEnd:"2026-04-24",color:"#e8a84a",note:"Calendário Marica"},
  {title:"Festa de São Jorge no Espraiado",dateStart:"2026-04-23",color:"#e8624a",note:"Calendário Marica"},
  {title:"Festa de Ogum em Cordeirinho",dateStart:"2026-04-25",color:"#c8f04e",note:"Calendário Marica"},
  {title:"Maricá em Dança",dateStart:"2026-04-25",dateEnd:"2026-04-26",color:"#a84ae8",note:"Calendário Marica"},
  {title:"Festa da Trabalhadora e do Trabalhador",dateStart:"2026-05-01",color:"#e8624a",note:"Calendário Marica"},
  {title:"Festa da Pesca de Maricá",dateStart:"2026-05-02",dateEnd:"2026-05-03",color:"#4ac8e8",note:"Calendário Marica"},
  {title:"Maricá Musical",dateStart:"2026-05-08",dateEnd:"2026-05-09",color:"#7c6eff",note:"Calendário Marica"},
  {title:"Curta Itaocaia Valley",dateStart:"2026-05-10",color:"#c8f04e",note:"Calendário Marica"},
  {title:"Corrida Cidade Maricá",dateStart:"2026-05-16",color:"#4ac8e8",note:"Calendário Marica"},
  {title:"Aqui é mais liberdade (Feira Ancestral Casa de Terreiro)",dateStart:"2026-05-17",color:"#e8a84a",note:"Calendário Marica"},
  {title:"Aniversário da Cidade de Maricá (212 anos)",dateStart:"2026-05-23",dateEnd:"2026-05-26",color:"#f0a832",note:"Calendário Marica"},
  {title:"Circuito Maricá de Pesca Esportiva",dateStart:"2026-05-24",color:"#4ac8e8",note:"Calendário Marica"},
  {title:"Dia do Evangélico",dateStart:"2026-05-25",color:"#c8f04e",note:"Calendário Marica"},
  {title:"Casamento e 15 anos comunitários",dateStart:"2026-05-01",color:"#e84ab8",note:"Calendário Marica — Data em aberto"},
  {title:"Festival de Cinema e Política",dateStart:"2026-06-02",dateEnd:"2026-06-07",color:"#7c6eff",note:"Calendário Marica"},
  {title:"Corpus Christi",dateStart:"2026-06-04",color:"#c8f04e",note:"Calendário Marica"},
  {title:"Prêmio Maysa",dateStart:"2026-06-06",color:"#e84ab8",note:"Calendário Marica"},
  {title:"Maricá na Copa (Copa do Mundo)",dateStart:"2026-06-11",dateEnd:"2026-07-19",color:"#4ae89c",note:"Calendário Marica"},
  {title:"Espraiado de Portas Abertas",dateStart:"2026-06-14",color:"#4ac8e8",note:"Calendário Marica"},
  {title:"Festa de São Pedro",dateStart:"2026-06-28",dateEnd:"2026-06-29",color:"#4a7ee8",note:"Calendário Marica"},
  {title:"Festival de Inverno Recantando",dateStart:"2026-07-03",dateEnd:"2026-07-05",color:"#7c6eff",note:"Calendário Marica"},
  {title:"Circuito Maricá de Pesca Esportiva",dateStart:"2026-07-05",color:"#4ac8e8",note:"Calendário Marica"},
  {title:"Festival Internacional de Blues, Rock e Jazz",dateStart:"2026-07-09",dateEnd:"2026-07-12",color:"#e8624a",note:"Calendário Marica"},
  {title:"Maricá Games",dateStart:"2026-07-10",dateEnd:"2026-07-11",color:"#c8f04e",note:"Calendário Marica"},
  {title:"Curta Itaocaia Valley",dateStart:"2026-07-12",color:"#c8f04e",note:"Calendário Marica"},
  {title:"Colônia de férias das comunidades",dateStart:"2026-07-13",dateEnd:"2026-07-24",color:"#4ae89c",note:"Calendário Marica"},
  {title:"Maricá Moto Fest / Roteiros Trilhas Maricá",dateStart:"2026-07-23",dateEnd:"2026-07-26",color:"#e8624a",note:"Calendário Marica"},
  {title:"Festa do Produtor Rural",dateStart:"2026-07-24",dateEnd:"2026-07-26",color:"#e8a84a",note:"Calendário Marica"},
  {title:"Festa de Nossa Senhora do Amparo",dateStart:"2026-08-03",dateEnd:"2026-08-15",color:"#4a7ee8",note:"Calendário Marica"},
  {title:"Expo Maricá",dateStart:"2026-08-06",dateEnd:"2026-08-08",color:"#c8f04e",note:"Calendário Marica"},
  {title:"A Padroeira Abraça São João (Comunidades)",dateStart:"2026-08-07",dateEnd:"2026-08-09",color:"#f0a832",note:"Calendário Marica"},
  {title:"Espraiado de Portas Abertas",dateStart:"2026-08-09",color:"#4ac8e8",note:"Calendário Marica"},
  {title:"FRACJ — Festival Regional de Arte e Cultura Jovem",dateStart:"2026-08-10",dateEnd:"2026-08-15",color:"#a84ae8",note:"Calendário Marica"},
  {title:"Festa da Padroeira Abraça São João",dateStart:"2026-08-14",dateEnd:"2026-08-16",color:"#7c6eff",note:"Calendário Marica"},
  {title:"Marcha para Jesus",dateStart:"2026-08-29",color:"#c8f04e",note:"Calendário Marica"},
  {title:"FLIM + Língua ao Mar",dateStart:"2026-09-01",color:"#4ac8e8",note:"Calendário Marica — Data em aberto"},
  {title:"Circuito Maricá de Pesca Esportiva",dateStart:"2026-09-13",color:"#4ac8e8",note:"Calendário Marica"},
  {title:"Curta Itaocaia Valley",dateStart:"2026-09-13",color:"#c8f04e",note:"Calendário Marica"},
  {title:"Dia Nacional da Luta da Pessoa com Deficiência",dateStart:"2026-09-26",color:"#7c6eff",note:"Calendário Marica"},
  {title:"Festividade de São Cosme e Damião",dateStart:"2026-09-27",color:"#f0a832",note:"Calendário Marica"},
  {title:"FLIM nas Comunidades",dateStart:"2026-09-15",color:"#4ac8e8",note:"Calendário Marica — Data em aberto"},
  {title:"Aniversário Berta Ribeiro",dateStart:"2026-10-03",color:"#e84ab8",note:"Calendário Marica"},
  {title:"Festival de Artes Cênicas (FESTACEM)",dateStart:"2026-10-08",dateEnd:"2026-10-12",color:"#a84ae8",note:"Calendário Marica"},
  {title:"Dia das Crianças nas Comunidades",dateStart:"2026-10-10",dateEnd:"2026-10-11",color:"#f0a832",note:"Calendário Marica"},
  {title:"Festa de Nossa Senhora Aparecida",dateStart:"2026-10-10",dateEnd:"2026-10-12",color:"#4a7ee8",note:"Calendário Marica"},
  {title:"Espraiado de Portas Abertas",dateStart:"2026-10-11",color:"#4ac8e8",note:"Calendário Marica"},
  {title:"Maricá Bier Fest",dateStart:"2026-10-15",dateEnd:"2026-10-18",color:"#e8a84a",note:"Calendário Marica"},
  {title:"Prêmio Heloneida Studart",dateStart:"2026-10-24",color:"#e84ab8",note:"Calendário Marica"},
  {title:"Festival Internacional de Poesia de Maricá",dateStart:"2026-10-29",dateEnd:"2026-11-02",color:"#7c6eff",note:"Calendário Marica"},
  {title:"Aniversário Darcy Ribeiro",dateStart:"2026-10-31",color:"#c8f04e",note:"Calendário Marica"},
  {title:"Parada LGBTQIAPN+",dateStart:"2026-10-15",color:"#e84ab8",note:"Calendário Marica — Data em aberto"},
  {title:"Feira de Ciências, Tecnologia e Inovação",dateStart:"2026-10-20",color:"#4ac8e8",note:"Calendário Marica — Data em aberto"},
  {title:"Dia da Favela / Virada Cultural",dateStart:"2026-11-07",color:"#7c6eff",note:"Calendário Marica"},
  {title:"Circuito Maricá de Pesca Esportiva",dateStart:"2026-11-08",color:"#4ac8e8",note:"Calendário Marica"},
  {title:"Volta ao Mundo Bambas (Capoeira)",dateStart:"2026-11-13",dateEnd:"2026-11-15",color:"#e8624a",note:"Calendário Marica"},
  {title:"Semana da Consciência Negra",dateStart:"2026-11-14",dateEnd:"2026-11-21",color:"#f0a832",note:"Calendário Marica"},
  {title:"Curta Itaocaia Valley",dateStart:"2026-11-15",color:"#c8f04e",note:"Calendário Marica"},
  {title:"Feira das Yabás",dateStart:"2026-11-20",color:"#e84ab8",note:"Calendário Marica"},
  {title:"Natal Brasilidade",dateStart:"2026-11-22",dateEnd:"2026-12-31",color:"#c8f04e",note:"Calendário Marica"},
  {title:"Dia Nacional do Samba",dateStart:"2026-12-05",dateEnd:"2026-12-06",color:"#e8624a",note:"Calendário Marica"},
  {title:"Espraiado de Portas Abertas",dateStart:"2026-12-13",color:"#4ac8e8",note:"Calendário Marica"},
  {title:"Natal Brasilidade nas Comunidades",dateStart:"2026-12-20",dateEnd:"2026-12-23",color:"#c8f04e",note:"Calendário Marica"},
  {title:"Ano Novo",dateStart:"2026-12-30",dateEnd:"2026-12-31",color:"#f0a832",note:"Calendário Marica"},
];

let _prospSeeded=false;
async function seedProspEvents(){
  if(_prospSeeded)return;
  _prospSeeded=true;
  const existing=Object.entries(prospEvents);
  if(existing.length===0){
    // Primeiro uso: inserir todos
    for(const ev of PROSP_SEED){
      await dbPush("prosp_events",{...ev,note:ev.note||"LOCAL Búzios",createdAt:new Date().toISOString()});
    }
    toast("Calendário Prospecção populado!","success");
  } else {
    // Atualizar notas vazias para LOCAL Búzios
    let updated=0;
    for(const [id,ev] of existing){
      if(!ev.note||ev.note.trim()===""){
        await dbSet(`prosp_events/${id}/note`,"LOCAL Búzios");
        updated++;
      }
    }
    // Inserir eventos novos que não existem ainda (por título+data)
    const existingKeys=new Set(existing.map(([,e])=>`${e.title}|${e.dateStart}`));
    let added=0;
    for(const ev of PROSP_SEED){
      const key=`${ev.title}|${ev.dateStart}`;
      if(!existingKeys.has(key)){
        await dbPush("prosp_events",{...ev,note:ev.note||"LOCAL Búzios",createdAt:new Date().toISOString()});
        added++;
      }
    }
    if(updated>0||added>0) toast(`Prospecção: ${added} evento(s) adicionado(s), ${updated} atualizado(s)`,"success");
  }
}

function renderProspPage(){
  const today=new Date(); today.setHours(0,0,0,0);
  const yr=prospYear, mo=prospMonth;
  const firstDay=new Date(yr,mo,1);
  const lastDay=new Date(yr,mo+1,0);
  const startWd=(firstDay.getDay()+6)%7;
  const totalCells=Math.ceil((startWd+lastDay.getDate())/7)*7;
  const monthNames=["Janeiro","Fevereiro","Março","Abril","Maio","Junho","Julho","Agosto","Setembro","Outubro","Novembro","Dezembro"];
  const dayNames=["Seg","Ter","Qua","Qui","Sex","Sáb","Dom"];

  const eventMap={};
  Object.entries(prospEvents).forEach(([eid,e])=>{
    if(!e.dateStart)return;
    const start=new Date(e.dateStart+"T00:00:00");
    const end=e.dateEnd?new Date(e.dateEnd+"T00:00:00"):start;
    for(let d=new Date(start);d<=end;d.setDate(d.getDate()+1)){
      const ds=d.toISOString().slice(0,10);
      if(!eventMap[ds])eventMap[ds]=[];
      const isFirst=ds===e.dateStart, isLast=ds===(e.dateEnd||e.dateStart);
      const span=!!(e.dateEnd&&e.dateEnd!==e.dateStart);
      eventMap[ds].push({id:eid,...e,isFirst,isLast,span});
    }
  });

  let cells="";
  for(let i=0;i<totalCells;i++){
    const dayNum=i-startWd+1;
    const isCurrentMonth=dayNum>=1&&dayNum<=lastDay.getDate();
    const cellDate=new Date(yr,mo,dayNum);
    const ds=cellDate.toISOString().slice(0,10);
    const isToday=isCurrentMonth&&cellDate.getTime()===today.getTime();
    const isPast=isCurrentMonth&&cellDate<today;
    const evs=eventMap[ds]||[];
    const chips=evs.map(e=>`<div class="prosp-chip" data-eid="${e.id}" style="background:${e.color||"#7c6eff"}22;border-left:3px solid ${e.color||"#7c6eff"};color:${e.color||"#7c6eff"};font-size:9px;padding:2px 5px;border-radius:3px;margin-top:2px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;cursor:pointer;max-width:100%">${e.isFirst||!e.span?"🎯 "+esc(e.title.slice(0,15)):"↳ "+esc(e.title.slice(0,12))}</div>`).join("");
    cells+=`<div class="cal-cell ${isToday?"cal-today":""} ${!isCurrentMonth?"cal-other":""} ${isPast&&isCurrentMonth?"cal-past":""}" data-date="${isCurrentMonth?ds:""}">
      <div class="cal-day-num" style="${isToday?"background:#7c6eff;color:#fff;":""}${!isCurrentMonth?"color:#2e2e3a;":""}">${isCurrentMonth?dayNum:""}</div>
      ${chips}
    </div>`;
  }

  const upcoming=Object.entries(prospEvents).map(([id,e])=>{
    if(!e.dateStart)return null;
    const ms=new Date(e.dateStart+"T00:00:00").getTime();
    const diff=Math.round((ms-today.getTime())/86400000);
    if(diff<0||diff>14)return null;
    return{id,...e,diff};
  }).filter(Boolean).sort((a,b)=>a.diff-b.diff);

  const upHtml=upcoming.length?upcoming.map(e=>{
    const lbl=e.diff===0?"Hoje":e.diff===1?"Amanhã":`${e.diff} dias`;
    return`<div style="display:flex;gap:8px;align-items:flex-start;padding:8px 0;border-bottom:1px solid #1e1e28">
      <div style="background:${e.color||"#7c6eff"}22;color:${e.color||"#7c6eff"};border:1px solid ${e.color||"#7c6eff"}44;padding:3px 6px;border-radius:6px;font-size:10px;font-weight:700;white-space:nowrap;min-width:52px;text-align:center">${lbl}</div>
      <div><div style="font-size:12px;font-weight:600;color:#f0eff5">${esc(e.title)}</div>${e.note?`<div style="font-size:10px;color:#5a5a6a">${esc(e.note.slice(0,40))}</div>`:""}</div>
    </div>`;
  }).join(""):`<div style="font-size:12px;color:#5a5a6a;text-align:center;padding:20px 0">Nenhum evento nos próximos 14 dias</div>`;

  return`<div class="page-header">
    <div><div class="page-title">🎯 Cal. Prospecção</div><div class="page-sub">Eventos e oportunidades de Búzios — ${monthNames[mo]} ${yr}</div></div>
    ${isAdmin()?`<button class="btn-primary" id="btn-new-prosp">+ Novo Evento</button>`:""}
  </div>
  <div style="display:grid;grid-template-columns:1fr 230px;gap:20px;align-items:start">
    <div>
      <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:14px">
        <button class="btn-small" id="prosp-prev" style="border:1px solid #2e2e3a;color:#f0eff5">‹ Anterior</button>
        <div style="font-family:'Syne',sans-serif;font-size:17px;font-weight:700">${monthNames[mo]} ${yr}</div>
        <button class="btn-small" id="prosp-next" style="border:1px solid #2e2e3a;color:#f0eff5">Próximo ›</button>
      </div>
      <div class="cal-grid">
        ${dayNames.map(d=>`<div class="cal-header-cell">${d}</div>`).join("")}
        ${cells}
      </div>
    </div>
    <div>
      <div style="font-family:'Syne',sans-serif;font-size:14px;font-weight:700;margin-bottom:12px;color:#7c6eff">📌 Próximos 14 dias</div>
      ${upHtml}
    </div>
  </div>`;
}

function attachProspEvents(){
  document.getElementById("prosp-prev")?.addEventListener("click",()=>{prospMonth--;if(prospMonth<0){prospMonth=11;prospYear--;}render();});
  document.getElementById("prosp-next")?.addEventListener("click",()=>{prospMonth++;if(prospMonth>11){prospMonth=0;prospYear++;}render();});
  document.getElementById("btn-new-prosp")?.addEventListener("click",()=>openProspEventModal(null,null));
  document.querySelectorAll(".prosp-chip[data-eid]").forEach(el=>{
    el.addEventListener("click",e=>{e.stopPropagation();openProspEventModal(el.dataset.eid);});
  });
  document.querySelectorAll(".cal-cell[data-date]").forEach(el=>{
    el.addEventListener("click",e=>{
      if(e.target.classList.contains("prosp-chip"))return;
      const ds=el.dataset.date; if(!ds||page!=="prospecção")return;
      openProspEventModal(null,ds);
    });
  });
  // Semear dados iniciais se necessário
  seedProspEvents(); // popula se vazio, ou migra notas se necessário
}

function openProspEventModal(eventId, prefillDate=null){
  const ev=eventId?(prospEvents[eventId]||{}):{}; 
  const isEdit=!!eventId;
  openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:500px">
    <div class="modal-header"><div class="modal-title">${isEdit?"Editar":"Novo"} Evento — Prospecção</div><button class="icon-btn" id="m-x">✕</button></div>
    <div class="modal-body">
      <div class="field"><label>Título *</label><input id="m-ptitle" value="${esc(ev.title||"")}" placeholder="Nome do evento…" autofocus/></div>
      <div class="field-row">
        <div class="field"><label>Data início *</label><input type="date" id="m-pstart" value="${ev.dateStart||prefillDate||""}"/></div>
        <div class="field"><label>Data fim <span style="color:#7a7a8a;font-size:10px">(opcional)</span></label><input type="date" id="m-pend" value="${ev.dateEnd||""}"/></div>
      </div>
      <div class="field"><label>Observações</label><textarea id="m-pnote" rows="3" placeholder="Detalhes, local, oportunidade…">${esc(ev.note||"")}</textarea></div>
      <div class="field"><label>Cor</label>
        <div style="display:flex;align-items:center;gap:10px">
          <input type="color" id="m-pcolor" value="${ev.color||"#7c6eff"}" style="width:36px;height:36px;border:none;background:none;cursor:pointer;border-radius:6px"/>
        </div>
      </div>
    </div>
    <div class="modal-footer">
      ${isEdit?`<button class="btn-danger" id="m-pdel">Excluir</button>`:""}
      <button class="btn-ghost" id="m-cancel">Cancelar</button>
      <button class="btn-primary" id="m-psave">Salvar</button>
    </div>
  </div></div>`);
  document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;
  document.getElementById("m-pdel")?.addEventListener("click",async()=>{
    if(confirm("Excluir evento?")){await dbRemove(`prosp_events/${eventId}`);closeModal();toast("Evento excluído","warning");}
  });
  document.getElementById("m-psave").onclick=async()=>{
    const title=document.getElementById("m-ptitle").value.trim();
    const dateStart=document.getElementById("m-pstart").value;
    if(!title||!dateStart){toast("Preencha título e data início","error");return;}
    const data={title,dateStart,dateEnd:document.getElementById("m-pend").value||null,
      note:document.getElementById("m-pnote").value.trim()||null,
      color:document.getElementById("m-pcolor").value||"#7c6eff",
      creatorId:currentUser.uid,creatorName:currentProfile.name,
      createdAt:ev.createdAt||new Date().toISOString()};
    await dbSet(`prosp_events/${eventId||uid()}`,data);
    toast(isEdit?"Evento atualizado!":"Evento criado!","success");closeModal();
  };
  overlayClose("ov");
}

function openCalEventModal(eventId, prefillDate, isFreela=false){
  const ev=eventId?(calEvents[eventId]||freelaEvents[eventId]||{}):{}; 
  if(!ev&&eventId){toast("Evento não encontrado","error");return;}
  if(eventId&&!calEvents[eventId]&&freelaEvents[eventId])isFreela=true;
  const orgPersons=Object.values(orgData.nodes||{}).filter(n=>n.name).map(n=>n.name);
  const isEdit=!!eventId;
  const rootAreas=Object.entries(areas).filter(([,a])=>!a.parentId);
  openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:500px">
    <div class="modal-header"><div class="modal-title">${isEdit?"Editar":"Novo"} Evento</div><button class="icon-btn" id="m-x">✕</button></div>
    <div class="modal-body">
      <div class="field"><label>Título *</label><input id="m-etitle" value="${esc(ev.title||"")}" placeholder="Nome do evento…" autofocus/></div>
      <div class="field"><label>Área *</label>
        <select id="m-earea" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none">
          <option value="">— Selecione uma área —</option>
          ${rootAreas.map(([id,a])=>`<option value="${id}" ${ev.areaId===id?"selected":""}>${esc(a.name)}</option>`).join("")}
        </select>
      </div>
      <div class="field-row">
        <div class="field"><label>Data início *</label><input type="date" id="m-estart" value="${ev.dateStart||prefillDate||""}"/></div>
        <div class="field"><label>Data fim <span style="color:#7a7a8a;font-size:10px">(opcional, para multi-dia)</span></label><input type="date" id="m-eend" value="${ev.dateEnd||""}"/></div>
      </div>
      <div class="field-row">
        <div class="field"><label>Prioridade</label>
          <select id="m-eprio" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none">
            <option value="">Sem prioridade</option>
            ${Object.entries(CAL_PRIORITY).map(([k,v])=>`<option value="${k}" ${(ev.priority||"")=== k?"selected":""}>${v.label}</option>`).join("")}
          </select>
        </div>
        <div class="field"><label>Responsável</label>
          <select id="m-eperson" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none">
            <option value="">Nenhum</option>
            ${orgPersons.map(p=>`<option value="${esc(p)}" ${ev.person===p?"selected":""}>${esc(p)}</option>`).join("")}
          </select>
        </div>
      </div>
      <div class="field"><label>Observações</label><textarea id="m-enote" rows="3" placeholder="Detalhes, local, link…">${esc(ev.note||"")}</textarea></div>
      <div class="field"><label>Cor do evento <span style="color:#7a7a8a;font-size:10px">(opcional, substitui a cor da prioridade)</span></label>
        <div style="display:flex;align-items:center;gap:10px">
          <input type="color" id="m-ecolor" value="${ev.color||"#7c6eff"}" style="width:36px;height:36px;border:none;background:none;cursor:pointer;border-radius:6px"/>
          <label style="display:flex;align-items:center;gap:6px;font-size:12px;color:#7a7a8a;cursor:pointer"><input type="checkbox" id="m-ecolor-use" ${ev.color?"checked":""} style="accent-color:#c8f04e"/> Usar cor personalizada</label>
        </div>
      </div>
      <div style="background:#1a1a2e;border:1px solid #2e2e44;border-radius:8px;padding:10px 14px;font-size:11px;color:#7a7a8a;margin-top:4px">
        <strong style="color:#c8f04e">Alertas automáticos:</strong><br>
        Essencial → notificação 3, 2, 1 dia antes e no dia<br>
        Importante → notificação 2 e 1 dia antes
      </div>
    </div>
    <div class="modal-footer">
      ${isEdit?`<button class="btn-danger" id="m-edel">Excluir</button>`:""}
      <button class="btn-ghost" id="m-cancel">Cancelar</button>
      <button class="btn-primary" id="m-save">Salvar</button>
    </div>
  </div></div>`);
  document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;
  document.getElementById("m-edel")?.addEventListener("click",async()=>{
    if(confirm("Excluir evento?")){await dbRemove(`${isFreela?"freela_events":"cal_events"}/${eventId}`);await logAction("excluir_evento",`Evento excluído: ${ev.title}`);closeModal();toast("Evento excluído","warning");}
  });
  document.getElementById("m-save").onclick=async()=>{
    const title=document.getElementById("m-etitle").value.trim();
    const dateStart=document.getElementById("m-estart").value;
    const areaId=document.getElementById("m-earea").value;
    const person=document.getElementById("m-eperson").value||null;
    if(!title||!dateStart){toast("Preencha título e data","error");return;}
    if(!areaId){toast("Selecione uma área para o evento","error");return;}
    if(!person){toast("Selecione um responsável pelo evento","error");return;}
    const dateEnd=document.getElementById("m-eend").value||null;
    const priority=document.getElementById("m-eprio").value||null;
    const note=document.getElementById("m-enote").value.trim()||null;
    const useColor=document.getElementById("m-ecolor-use")?.checked;
    const evColor=useColor?(document.getElementById("m-ecolor")?.value||null):null;
    const data={title,dateStart,dateEnd,priority,person,note,color:evColor||null,areaId,creatorId:currentUser.uid,creatorName:currentProfile.name,createdAt:ev.createdAt||new Date().toISOString()};
    await dbSet(`${isFreela?"freela_events":"cal_events"}/${eventId||uid()}`,data);
    await logAction(isEdit?"editar_evento":"criar_evento",`${isEdit?"Editado":"Criado"}: ${title} (${dateStart})`);
    toast(isEdit?"Evento atualizado!":"Evento criado!","success");closeModal();
  };
  overlayClose("ov");
}

function openCalEventDetailModal(eventId){
  const ev=calEvents[eventId]||freelaEvents[eventId]; if(!ev)return;
  const isFreela=!calEvents[eventId]&&!!freelaEvents[eventId];
  const prio=CAL_PRIORITY[ev.priority];
  const span=ev.dateEnd&&ev.dateEnd!==ev.dateStart;
  const canEdit=true; // all users can edit/delete calendar events
  openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:460px">
    <div class="modal-header">
      <div class="modal-title" style="display:flex;align-items:center;gap:8px">
        ${prio?`<span style="width:10px;height:10px;border-radius:50%;background:${prio.color};display:inline-block;flex-shrink:0"></span>`:""}
        ${esc(ev.title)}
      </div>
      <button class="icon-btn" id="m-x">✕</button>
    </div>
    <div class="modal-body">
      <div style="display:flex;gap:10px;flex-wrap:wrap;margin-bottom:14px">
        ${prio?`<span class="chip" style="background:${prio.color}18;color:${prio.color};border:1px solid ${prio.color}30">${prio.label}</span>`:""}
        <span class="chip" style="background:#1e1e28;color:#a0a0b0">${span?fmtDate(ev.dateStart)+" → "+fmtDate(ev.dateEnd):fmtDate(ev.dateStart)}</span>
        ${span?`<span class="chip" style="background:#7c6eff18;color:#9d93ff;border:1px solid #7c6eff30">${Math.round((new Date(ev.dateEnd)-new Date(ev.dateStart))/86400000)+1} dias</span>`:""}
      </div>
      ${ev.person?`<div style="margin-bottom:10px"><div style="font-size:10px;color:#7a7a8a;text-transform:uppercase;letter-spacing:1px;margin-bottom:4px">Responsável</div><span style="background:#7c6eff18;color:#9d93ff;border:1px solid #7c6eff30;padding:4px 12px;border-radius:20px;font-size:12px">${esc(ev.person)}</span></div>`:""}
      ${ev.note?`<div style="font-size:13px;color:#a0a0b0;line-height:1.6;background:#18181c;padding:12px;border-radius:8px;margin-bottom:12px">${esc(ev.note)}</div>`:""}
      ${ev.creatorName?`<div style="font-size:11px;color:#5a5a6a">Criado por: ${esc(ev.creatorName)}</div>`:""}
    </div>
    <div class="modal-footer">
      ${canEdit?`<button class="btn-danger" id="m-del">Excluir</button><button class="btn-primary" id="m-edit">Editar</button>`:""}
      <button class="btn-ghost" id="m-x2">Fechar</button>
    </div>
  </div></div>`);
  document.getElementById("m-x").onclick=document.getElementById("m-x2").onclick=closeModal;
  document.getElementById("m-edit")?.addEventListener("click",()=>{closeModal();openCalEventModal(eventId,null,isFreela);});
  document.getElementById("m-del")?.addEventListener("click",async()=>{
    if(confirm("Excluir evento?")){await dbRemove(`${isFreela?"freela_events":"cal_events"}/${eventId}`);await logAction("excluir_evento","Excluído: "+ev.title);closeModal();toast("Evento excluído","warning");}
  });
  overlayClose("ov");
}

function openCalDayModal(dateStr){
  const dayFmt=fmtDate(dateStr);
  const today=new Date(); today.setHours(0,0,0,0);
  const dayDate=new Date(dateStr+"T00:00:00");
  const isToday=dayDate.getTime()===today.getTime();
  const isPast=dayDate<today;
  const dayNames=["Domingo","Segunda","Terça","Quarta","Quinta","Sexta","Sábado"];
  const dayName=dayNames[dayDate.getDay()];

  // Tarefas do dia
  const myAreaIds=visibleAreas().map(a=>a.id);
  const taskEvs=Object.entries(tasks)
    .filter(([,t])=>t.date===dateStr&&myAreaIds.includes(t.areaId))
    .map(([id,t])=>({id,...t}))
    .sort((a,b)=>{const order={"a-fazer":0,"em-andamento":1,"bloqueado":2,"concluido":3};return(order[a.status]||0)-(order[b.status]||0);});

  // Eventos do calendário do dia
  const calEvs=Object.entries({...calEvents,...freelaEvents})
    .filter(([,e])=>{
      if(!e.dateStart)return false;
      const start=e.dateStart, end=e.dateEnd||e.dateStart;
      return dateStr>=start&&dateStr<=end;
    })
    .map(([id,e])=>({id,...e}));

  const totalItems=taskEvs.length+calEvs.length;

  // Renderizar tarefas
  const tasksHtml=taskEvs.length?`
    <div style="margin-bottom:20px">
      <div style="font-size:10px;font-weight:700;text-transform:uppercase;letter-spacing:1.5px;color:#7a7a8a;margin-bottom:12px">
        📋 Tarefas (${taskEvs.length})
      </div>
      ${taskEvs.map(t=>{
        const st=STATUS[t.status];
        const area=areas[t.areaId];
        const resps=Array.isArray(t.resps)?t.resps:(t.resp?[t.resp]:[]);
        const dl=deadlineClass(t.date);
        return`<div class="cal-day-task-card" data-tid="${t.id}" style="
          background:${st.color}10;
          border:1.5px solid ${st.color}35;
          border-left:4px solid ${st.color};
          border-radius:10px;padding:14px 16px;
          margin-bottom:10px;cursor:pointer;
          transition:all .13s;
        ">
          <div style="display:flex;align-items:center;gap:10px;margin-bottom:8px">
            <span style="width:10px;height:10px;border-radius:50%;background:${st.color};flex-shrink:0"></span>
            <div style="font-family:'Syne',sans-serif;font-size:16px;font-weight:700;color:#f0eff5;flex:1;line-height:1.3">${esc(t.title)}</div>
            <span style="font-size:11px;font-weight:700;color:${st.color};background:${st.color}18;padding:3px 10px;border-radius:20px;flex-shrink:0">${st.label}</span>
          </div>
          ${t.desc?`<div style="font-size:13px;color:#a0a0b0;line-height:1.6;margin-bottom:8px">${esc(t.desc.slice(0,120)+(t.desc.length>120?"…":""))}</div>`:""}
          <div style="display:flex;gap:8px;flex-wrap:wrap;align-items:center">
            ${area?`<span style="font-size:12px;color:${area.color};background:${area.color}15;border:1px solid ${area.color}30;padding:3px 10px;border-radius:20px">📁 ${esc(area.name)}</span>`:""}
            ${resps.slice(0,3).map(r=>`<span style="font-size:12px;color:#9d93ff;background:#7c6eff15;border:1px solid #7c6eff30;padding:3px 10px;border-radius:20px">👤 ${esc(r)}</span>`).join("")}
            ${resps.length>3?`<span style="font-size:11px;color:#7a7a8a">+${resps.length-3}</span>`:""}
            ${t.priority?`<span style="font-size:12px;color:${PRIORITY[t.priority].color};margin-left:auto">● ${PRIORITY[t.priority].label}</span>`:""}
          </div>
        </div>`;
      }).join("")}
    </div>`:""

  // Renderizar eventos do calendário
  const calHtml=calEvs.length?`
    <div style="margin-bottom:20px">
      <div style="font-size:10px;font-weight:700;text-transform:uppercase;letter-spacing:1.5px;color:#7a7a8a;margin-bottom:12px">
        🗓 Eventos (${calEvs.length})
      </div>
      ${calEvs.map(e=>{
        const prio=CAL_PRIORITY[e.priority];
        const color=e.color||(prio?.color)||"#7c6eff";
        const span=e.dateEnd&&e.dateEnd!==e.dateStart;
        return`<div class="cal-day-event-card" data-eid="${e.id}" style="
          background:${color}10;
          border:1.5px solid ${color}35;
          border-left:4px solid ${color};
          border-radius:10px;padding:14px 16px;
          margin-bottom:10px;cursor:pointer;
          transition:all .13s;
        ">
          <div style="display:flex;align-items:flex-start;gap:10px;margin-bottom:6px">
            <div style="font-family:'Syne',sans-serif;font-size:16px;font-weight:700;color:#f0eff5;flex:1;line-height:1.3">${esc(e.title)}</div>
            ${prio?`<span style="font-size:11px;font-weight:700;color:${color};background:${color}18;padding:3px 10px;border-radius:20px;flex-shrink:0">${prio.label}</span>`:""}
          </div>
          <div style="display:flex;gap:8px;flex-wrap:wrap;align-items:center">
            ${span?`<span style="font-size:12px;color:#a0a0b0">📅 ${fmtDate(e.dateStart)} → ${fmtDate(e.dateEnd)}</span>`:""}
            ${e.person?`<span style="font-size:12px;color:#a0a0b0">👤 ${esc(e.person)}</span>`:""}
          </div>
          ${e.note?`<div style="font-size:13px;color:#a0a0b0;line-height:1.6;margin-top:8px">${esc(e.note.slice(0,100)+(e.note.length>100?"…":""))}</div>`:""}
        </div>`;
      }).join("")}
    </div>`:""

  const emptyHtml=totalItems===0?`
    <div style="text-align:center;padding:40px 20px;color:#5a5a6a">
      <div style="font-size:40px;margin-bottom:12px">${isPast?"📅":"🗓"}</div>
      <div style="font-size:15px;font-weight:600;color:#7a7a8a;margin-bottom:6px">Dia livre</div>
      <div style="font-size:13px">Nenhuma tarefa ou evento neste dia</div>
      <button class="btn-primary" id="m-add-event-day" style="margin-top:16px;font-size:13px">+ Criar evento</button>
    </div>`:""

  openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:580px">
    <div class="modal-header" style="padding:20px 24px 16px">
      <div>
        <div style="font-size:11px;color:#7a7a8a;text-transform:uppercase;letter-spacing:1.5px;margin-bottom:4px">${dayName}</div>
        <div style="font-family:'Syne',sans-serif;font-size:22px;font-weight:800;color:${isToday?"#c8f04e":"#f0eff5"}">${dayFmt}${isToday?' <span style="font-size:13px;color:#c8f04e;font-family:\'DM Sans\',sans-serif;font-weight:600;margin-left:8px">Hoje</span>':""}</div>
        ${totalItems>0?`<div style="font-size:12px;color:#7a7a8a;margin-top:4px">${totalItems} item${totalItems!==1?"s":""}</div>`:""}
      </div>
      <div style="display:flex;gap:8px;align-items:center">
        ${!isPast?`<button class="btn-small" id="m-add-task-day" style="border:1px solid #c8f04e44;color:#c8f04e;font-size:12px;padding:7px 14px">+ Tarefa</button>`:""}
        ${!isPast?`<button class="btn-primary" id="m-add-event-day" style="font-size:12px;padding:7px 14px">+ Evento</button>`:""}
        <button class="icon-btn" id="m-x">✕</button>
      </div>
    </div>
    <div class="modal-body" style="max-height:70vh;overflow-y:auto;padding:16px 24px">
      ${tasksHtml}${calHtml}${emptyHtml}
    </div>
  </div></div>`);

  document.getElementById("m-x").onclick=closeModal;
  document.getElementById("m-add-task-day")?.addEventListener("click",()=>{
    closeModal();
    openTaskModal({date:dateStr,status:"a-fazer",priority:"media",areaId:activeAreaId||""});
  });
  document.getElementById("m-add-event-day")?.addEventListener("click",()=>{closeModal();openCalEventModal(null,dateStr);});

  // Clicar na tarefa abre o detalhe
  document.querySelectorAll(".cal-day-task-card").forEach(c=>{
    c.addEventListener("mouseenter",()=>c.style.transform="translateY(-1px)");
    c.addEventListener("mouseleave",()=>c.style.transform="");
    c.addEventListener("click",()=>{closeModal();openDetailModal(c.dataset.tid);});
  });

  // Clicar no evento abre o detalhe do evento
  document.querySelectorAll(".cal-day-event-card").forEach(c=>{
    c.addEventListener("mouseenter",()=>c.style.transform="translateY(-1px)");
    c.addEventListener("mouseleave",()=>c.style.transform="");
    c.addEventListener("click",()=>{closeModal();openCalEventDetailModal(c.dataset.eid);});
  });

  overlayClose("ov");
}

// ── CALENDAR ALERTS (in-app notifications) ────────────────────────────────────
function checkCalAlerts(){
  const today=new Date(); today.setHours(0,0,0,0);
  const alerts=[];
  Object.entries(calEvents).forEach(([eid,e])=>{
    if(!e.dateStart||!e.priority)return;
    const eventDate=new Date(e.dateStart+"T00:00:00");
    const diffDays=Math.round((eventDate-today)/86400000);
    const prio=CAL_PRIORITY[e.priority];
    if(!prio||!prio.alertDays.includes(diffDays))return;
    const key=`${eid}-${diffDays}`;
    if(calAlertsSent[key])return;
    calAlertsSent[key]=true;
    const msg=diffDays===0?`Hoje: ${e.title}`
      :diffDays===1?`Amanhã: ${e.title}`
      :`${e.title} em ${diffDays} dias`;
    alerts.push({msg,color:prio.color,prio:prio.label});
  });
  // Show banners for active alerts
  if(alerts.length>0){
    alerts.forEach(a=>showCalBanner(a.msg,a.color,a.prio));
  }
}

function showCalBanner(msg,color,prioLabel){
  const el=document.createElement("div");
  el.style.cssText=`position:fixed;top:70px;right:20px;z-index:9999;background:#13131a;border:1px solid ${color};border-left:4px solid ${color};border-radius:10px;padding:12px 16px;max-width:320px;box-shadow:0 8px 24px rgba(0,0,0,.4);animation:slideIn .3s ease`;
  el.innerHTML=`<div style="display:flex;align-items:flex-start;gap:10px">
    <span style="font-size:18px;flex-shrink:0">📅</span>
    <div>
      <div style="font-size:10px;font-weight:700;text-transform:uppercase;color:${color};margin-bottom:2px">${prioLabel}</div>
      <div style="font-size:13px;color:#f0eff5;line-height:1.4">${msg}</div>
    </div>
    <button onclick="this.parentElement.parentElement.remove()" style="background:none;border:none;color:#5a5a6a;cursor:pointer;font-size:16px;flex-shrink:0;padding:0;margin-left:4px">✕</button>
  </div>`;
  document.body.appendChild(el);
  setTimeout(()=>{el.style.opacity="0";el.style.transform="translateX(20px)";el.style.transition="all .4s";setTimeout(()=>el.remove(),400);},6000);
}


let orgDragging=null, orgConnecting=null, orgSelEdge=null, orgMousePos={x:0,y:0};
let orgZoom=1, orgPan={x:0,y:0}, orgPanning=false, orgPanStart={x:0,y:0};
let orgSelectedNodes=new Set(), orgGroupDragging=null, orgSelBox=null;
let orgResizing=null; // escopo de módulo — não recriar a cada render
let _orgRafId=null;   // RAF handle para throttle

// ── Org mouse handlers — registrados UMA VEZ no módulo, nunca dentro de render ──
function _orgMouseMove(e){
  if(_orgRafId) return; // já tem frame agendado — descarta eventos intermediários
  _orgRafId=requestAnimationFrame(()=>{
    _orgRafId=null;
    const svg=document.getElementById("org-svg"); if(!svg)return;
    const r=svg.getBoundingClientRect();
    orgMousePos={x:(e.clientX-r.left-orgPan.x)/orgZoom,y:(e.clientY-r.top-orgPan.y)/orgZoom};
    if(orgPanning){
      orgPan.x=e.clientX-orgPanStart.x;
      orgPan.y=e.clientY-orgPanStart.y;
      // Pan: só move o grupo SVG diretamente, sem re-render completo
      const g=document.getElementById("org-zoom-group");
      if(g) g.setAttribute("transform",`translate(${orgPan.x},${orgPan.y}) scale(${orgZoom})`);
      else render();
      return;
    }
    if(orgResizing){
      const dx=(e.clientX-orgResizing.startX)/orgZoom;
      const dy=(e.clientY-orgResizing.startY)/orgZoom;
      orgResizing.curW=Math.max(80,Math.round(orgResizing.startW+dx));
      orgResizing.curH=Math.max(44,Math.round(orgResizing.startH+dy));
      if(orgData.nodes[orgResizing.id]){
        orgData.nodes[orgResizing.id].w=orgResizing.curW;
        orgData.nodes[orgResizing.id].h=orgResizing.curH;
      }
      render(); return;
    }
    if(orgGroupDragging){
      const dx=(e.clientX-orgGroupDragging.startClientX)/orgZoom;
      const dy=(e.clientY-orgGroupDragging.startClientY)/orgZoom;
      [...orgSelectedNodes].forEach(id=>{
        const orig=orgGroupDragging.origPos[id];if(!orig)return;
        if(orgData.nodes[id]){
          orgData.nodes[id].x=Math.max(0,orig.x+dx);
          orgData.nodes[id].y=Math.max(0,orig.y+dy);
        }
      });
      orgGroupDragging.lastDx=dx; orgGroupDragging.lastDy=dy;
      render(); return;
    }
    if(orgSelBox){
      orgSelBox.x2=(e.clientX-r.left-orgPan.x)/orgZoom;
      orgSelBox.y2=(e.clientY-r.top-orgPan.y)/orgZoom;
      render(); return;
    }
    if(orgConnecting){render();return;}
    if(!orgDragging)return;
    const nx=Math.max(0,(e.clientX-r.left-orgPan.x)/orgZoom-orgDragging.ox);
    const ny=Math.max(0,(e.clientY-r.top-orgPan.y)/orgZoom-orgDragging.oy);
    if(orgData.nodes[orgDragging.id]){orgData.nodes[orgDragging.id].x=nx;orgData.nodes[orgDragging.id].y=ny;}
    render();
  });
}
function _orgMouseUp(){
  if(orgPanning){
    orgPanning=false;
    const svg=document.getElementById("org-svg");
    if(svg) svg.style.cursor=orgSelectMode?"crosshair":"grab";
    render(); return;
  }
  if(orgSelBox){
    const x1=Math.min(orgSelBox.x1,orgSelBox.x2), x2=Math.max(orgSelBox.x1,orgSelBox.x2);
    const y1=Math.min(orgSelBox.y1,orgSelBox.y2), y2=Math.max(orgSelBox.y1,orgSelBox.y2);
    if(Math.abs(x2-x1)>5||Math.abs(y2-y1)>5){
      Object.entries(orgData.nodes||{}).forEach(([id,n])=>{
        const W=n.w||170, H=n.h||68;
        if(n.x+W/2>=x1&&n.x+W/2<=x2&&n.y+H/2>=y1&&n.y+H/2<=y2) orgSelectedNodes.add(id);
      });
    }
    orgSelBox=null; render(); return;
  }
  if(orgResizing){
    dbSet(`org/nodes/${orgResizing.id}/w`,orgResizing.curW||orgResizing.startW);
    dbSet(`org/nodes/${orgResizing.id}/h`,orgResizing.curH||orgResizing.startH);
    orgResizing=null; render(); return;
  }
  if(orgGroupDragging&&orgGroupDragging.lastDx!=null){
    [...orgSelectedNodes].forEach(id=>{
      const orig=orgGroupDragging.origPos[id];if(!orig)return;
      dbSet(`org/nodes/${id}/x`,Math.max(0,orig.x+orgGroupDragging.lastDx));
      dbSet(`org/nodes/${id}/y`,Math.max(0,orig.y+orgGroupDragging.lastDy));
    });
    orgGroupDragging=null; render(); return;
  }
  if(orgDragging&&orgData.nodes[orgDragging.id]){
    const n=orgData.nodes[orgDragging.id];
    dbSet(`org/nodes/${orgDragging.id}/x`,n.x);
    dbSet(`org/nodes/${orgDragging.id}/y`,n.y);
    orgDragging=null; render(); return;
  }
}
// Registra UMA VEZ — nunca dentro de render/attachOrgEvents
document.addEventListener("mousemove",_orgMouseMove);
document.addEventListener("mouseup",_orgMouseUp);
let orgStickies={};
let fyiNotes={};
let flowZoom=1, flowPan={x:0,y:0}, flowPanning=false, flowPanStart={x:0,y:0};
let flowStickies={};
let orgExpanded={}; // {nodeId: true/false} — expanded state per group

// ── ORGANOGRAMA ───────────────────────────────────────────────────────────────
function renderOrgPage(){
  if(!orgData){return`<div style="padding:40px;color:#7a7a8a">Carregando...</div>`;}
  if(!orgData){return`<div style="padding:40px;color:#7a7a8a">Carregando organograma...</div>`;}
  const allNodes=Object.entries(orgData.nodes||{}).map(([id,n])=>({id,...n}));
  const allEdges=Object.entries(orgData.edges||{}).map(([id,e])=>({id,...e}));
  const areaColors=Object.fromEntries(Object.entries(areas).map(([id,a])=>[a.name,a.color]));

  // Compute which nodes are children (have a parentId set)
  // Visible nodes: root nodes always visible; children only visible if parent is expanded
  function isVisible(n){
    if(!n.parentId) return true;
    // parent must be expanded
    if(!orgExpanded[n.parentId]) return false;
    // check recursively (grandparent etc)
    const parent=allNodes.find(p=>p.id===n.parentId);
    return parent?isVisible(parent):true;
  }

  const nodes=allNodes.filter(n=>isVisible(n));
  const nodeIds=new Set(nodes.map(n=>n.id));
  const edges=allEdges.filter(e=>nodeIds.has(e.from)&&nodeIds.has(e.to));

  // For each node, count direct children
  function childCount(nid){return allNodes.filter(c=>c.parentId===nid).length;}
  function visibleChildCount(nid){return allNodes.filter(c=>c.parentId===nid&&isVisible(c)).length;}

  const W=170, H=68; // defaults; individual nodes may override via n.w/n.h

  // Edges
  const svgEdges=edges.map(e=>{
    const fn=nodes.find(n=>n.id===e.from),tn=nodes.find(n=>n.id===e.to);if(!fn||!tn)return"";
    let fx,fy,tx2,ty;
    const mode=e.mode||"hierarchy";
    const fWo=fn.w||W,fHo=fn.h||H,tWo=tn.w||W,tHo=tn.h||H;
    if(mode==="hierarchy"){fx=fn.x+fWo/2;fy=fn.y+fHo;tx2=tn.x+tWo/2;ty=tn.y;}
    else{
      const fs2=e.fromSide||"right",ts2=e.toSide||"left";
      fx=fs2==="right"?fn.x+fWo:fs2==="left"?fn.x:fn.x+fWo/2;
      fy=fs2==="bottom"?fn.y+fHo:fs2==="top"?fn.y:fn.y+fHo/2;
      tx2=ts2==="right"?tn.x+tWo:ts2==="left"?tn.x:tn.x+tWo/2;
      ty=ts2==="bottom"?tn.y+tHo:ts2==="top"?tn.y:tn.y+tHo/2;
    }
    const mx=(fx+tx2)/2,my=(fy+ty)/2;
    const isSel=orgSelEdge===e.id;
    const sc=isSel?"#c8f04e":"#3e3e52";
    const path=mode==="hierarchy"
      ?`M${fx},${fy} C${fx},${fy+40} ${tx2},${ty-40} ${tx2},${ty}`
      :`M${fx},${fy} C${fx+50},${fy} ${tx2-50},${ty} ${tx2},${ty}`;
    const labelHtml=e.label?`<rect x="${mx-44}" y="${my-11}" width="88" height="20" rx="5" fill="#13131a" stroke="${sc}" stroke-width="1" style="pointer-events:none"/><text x="${mx}" y="${my}" text-anchor="middle" dominant-baseline="middle" fill="${sc}" font-size="10" font-family="DM Sans,sans-serif" style="pointer-events:none">${esc(e.label.slice(0,16)+(e.label.length>16?"...":""))}</text>`:"";
    const selBtns=isSel?`
      <rect x="${mx-54}" y="${my+14}" width="50" height="20" rx="4" fill="#ff6b6b18" stroke="#ff6b6b" stroke-width="1" class="org-del-edge" data-eid="${e.id}" style="cursor:pointer"/>
      <text x="${mx-29}" y="${my+24}" text-anchor="middle" dominant-baseline="middle" fill="#ff6b6b" font-size="9" font-family="DM Sans,sans-serif" style="pointer-events:none">Excluir</text>
      <rect x="${mx+4}" y="${my+14}" width="52" height="20" rx="4" fill="#7c6eff18" stroke="#7c6eff" stroke-width="1" class="org-edit-edge" data-eid="${e.id}" style="cursor:pointer"/>
      <text x="${mx+30}" y="${my+24}" text-anchor="middle" dominant-baseline="middle" fill="#9d93ff" font-size="9" font-family="DM Sans,sans-serif" style="pointer-events:none">Editar</text>
    `:"";
    return`<g>
      <path d="${path}" fill="none" stroke="${sc}" stroke-width="${isSel?2.2:1.5}"/>
      <path d="${path}" fill="none" stroke="transparent" stroke-width="18" class="org-edge-hit" data-eid="${e.id}" style="cursor:pointer"/>
      ${labelHtml}${selBtns}
    </g>`;}).join("");

  const liveEdge=orgConnecting?(()=>{
    const fn=nodes.find(n=>n.id===orgConnecting.fromId);if(!fn)return"";
    return`<path d="M${fn.x+W/2},${fn.y+H} L${orgMousePos.x},${orgMousePos.y}" fill="none" stroke="#c8f04e" stroke-width="1.5" stroke-dasharray="5,3"/>`;
  })():"";

  // Draw group background for expanded groups
  const groupBgs=allNodes.filter(n=>childCount(n.id)>0&&orgExpanded[n.id]).map(n=>{
    const children=allNodes.filter(c=>c.parentId===n.id&&isVisible(c));
    if(!children.length) return"";
    const allInGroup=[n,...children];
    const xs=allInGroup.map(c=>c.x), ys=allInGroup.map(c=>c.y);
    const minX=Math.min(...xs)-16, minY=Math.min(...ys)-16;
    const maxX=Math.max(...xs)+W+16, maxY=Math.max(...ys)+H+16;
    const aColor=n.areaName&&areaColors[n.areaName]?areaColors[n.areaName]:n.color||"#7c6eff";
    return`<rect x="${minX}" y="${minY}" width="${maxX-minX}" height="${maxY-minY}" rx="14" fill="${aColor}08" stroke="${aColor}30" stroke-width="1.5" stroke-dasharray="6,3" style="pointer-events:none"/>`;
  }).join("");

  // Nodes
  // Build gradient defs for multi-area org nodes
  const orgGradDefs=nodes.filter(n=>Array.isArray(n.areaIds)&&n.areaIds.length>1).map(n=>{
    const colors=n.areaIds.map(id=>areas[id]?.color||"#7c6eff");
    const stops=colors.map((c,i)=>{
      const pct=Math.round(i/(colors.length)*100);
      const pct2=Math.round((i+1)/(colors.length)*100);
      return`<stop offset="${pct}%" stop-color="${c}"/><stop offset="${pct2}%" stop-color="${c}"/>`;
    }).join("");
    return`<linearGradient id="org-grad-${n.id}" x1="0%" y1="0%" x2="100%" y2="0%">${stops}</linearGradient>`;
  }).join("");

  const svgNodes=nodes.map(n=>{
    const areaIdList=Array.isArray(n.areaIds)&&n.areaIds.length>0?n.areaIds:(n.areaName?Object.entries(areas).filter(([,a])=>a.name===n.areaName).map(([id])=>id):[]);
    const isMultiOrg=areaIdList.length>1;
    const aColor=isMultiOrg?areas[areaIdList[0]]?.color||"#7c6eff":(n.areaName&&areaColors[n.areaName]?areaColors[n.areaName]:n.color||"#7c6eff");
    const orgFill=isMultiOrg?`url(#org-grad-${n.id})`:`${aColor}18`;
    const orgStroke=isMultiOrg?`url(#org-grad-${n.id})`:aColor;
    const hasChildren=childCount(n.id)>0;
    const isExp=!!orgExpanded[n.id];
    const cc=childCount(n.id);
    const nameTxt=n.name?n.name.slice(0,20)+(n.name.length>20?"...":""):"";
    const roleTxt=n.role?n.role.slice(0,24)+(n.role.length>24?"...":""):"";
    const areaTxt=n.areaName?n.areaName.slice(0,20)+(n.areaName.length>20?"...":""):"";
    // Expand/collapse button bottom-center
    const expandBtn=hasChildren?`
      <g class="org-toggle" data-nid="${n.id}" style="cursor:pointer">
        <rect x="${W/2-20}" y="${H+4}" width="40" height="18" rx="9" fill="${isExp?"#c8f04e22":"#1e1e28"}" stroke="${isExp?"#c8f04e":"#3e3e52"}" stroke-width="1.2"/>
        <text x="${W/2}" y="${H+13}" text-anchor="middle" dominant-baseline="middle" fill="${isExp?"#c8f04e":"#7a7a8a"}" font-size="9" font-family="DM Sans,sans-serif" style="pointer-events:none">${isExp?`▲ ${cc}`:`▼ ${cc}`}</text>
      </g>`:"";
    // Add child button (admin only)
    const addChildBtn=isAdmin1?`
      <g class="org-add-child" data-nid="${n.id}" style="cursor:pointer" title="Adicionar membro ao grupo">
        <circle cx="${W+10}" cy="${H+4}" r="9" fill="#c8f04e18" stroke="#c8f04e44" stroke-width="1.2"/>
        <text x="${W+10}" y="${H+4}" text-anchor="middle" dominant-baseline="middle" fill="#c8f04e" font-size="13" style="pointer-events:none">+</text>
      </g>`:"";
    // Parent indicator badge
    const parentBadge=n.parentId?`<rect x="0" y="0" width="${W}" height="4" rx="2" fill="${aColor}60" style="pointer-events:none"/>`:"";
    const nW=n.w||W, nH=n.h||H, nFs=n.fsize||12;
    return`<g class="org-node" data-nid="${n.id}" transform="translate(${n.x},${n.y})" style="cursor:grab">
      <rect x="0" y="0" width="${nW}" height="${nH}" rx="10" fill="${orgFill}" stroke="${orgStroke}" stroke-width="${n.parentId?"1.2":"1.8"}"/>
      <rect x="0" y="0" width="6" height="${H}" rx="3" fill="${aColor}"/>
      ${parentBadge}
      ${nameTxt?`<text x="16" y="22" fill="#f0eff5" font-size="${n.parentId?"11":"12"}" font-weight="700" font-family="Syne,sans-serif" style="pointer-events:none">${esc(nameTxt)}</text>`:""}
      ${roleTxt?`<text x="16" y="38" fill="${aColor}" font-size="10" font-weight="500" font-family="DM Sans,sans-serif" style="pointer-events:none">${esc(roleTxt)}</text>`:""}
      ${areaTxt?`<text x="16" y="54" fill="#7a7a8a" font-size="9" font-family="DM Sans,sans-serif" style="pointer-events:none">${esc(areaTxt)}</text>`:""}
      ${expandBtn}
      ${addChildBtn}
      <circle cx="${W/2}" cy="0" r="6" fill="${orgConnecting?.fromId===n.id?"#c8f04e":"#16161e"}" stroke="${aColor}" stroke-width="1.5" class="org-conn-handle" data-nid="${n.id}" data-side="top" style="cursor:crosshair"/>
      <circle cx="${W}" cy="${H/2}" r="6" fill="${orgConnecting?.fromId===n.id?"#c8f04e":"#16161e"}" stroke="${aColor}" stroke-width="1.5" class="org-conn-handle" data-nid="${n.id}" data-side="right" style="cursor:crosshair"/>
      <circle cx="${W/2}" cy="${H}" r="6" fill="${orgConnecting?.fromId===n.id?"#c8f04e":"#16161e"}" stroke="${aColor}" stroke-width="1.5" class="org-conn-handle" data-nid="${n.id}" data-side="bottom" style="cursor:crosshair"/>
      <circle cx="0" cy="${H/2}" r="6" fill="${orgConnecting?.fromId===n.id?"#c8f04e":"#16161e"}" stroke="${aColor}" stroke-width="1.5" class="org-conn-handle" data-nid="${n.id}" data-side="left" style="cursor:crosshair"/>
      ${isAdmin1?`<g class="org-edit-node" data-nid="${n.id}" style="cursor:pointer"><circle cx="${W-10}" cy="10" r="9" fill="#1e1e28" stroke="${aColor}" stroke-width="1"/><text x="${W-10}" y="10" text-anchor="middle" dominant-baseline="middle" fill="${aColor}" font-size="10" style="pointer-events:none">✏</text></g>`:""}
      ${isAdmin1?`<g class="org-del-node" data-nid="${n.id}" style="cursor:pointer"><circle cx="-8" cy="-8" r="8" fill="#ff6b6b1a" stroke="#ff6b6b" stroke-width="1.2"/><text x="-8" y="-8" text-anchor="middle" dominant-baseline="middle" fill="#ff6b6b" font-size="11" style="pointer-events:none">✕</text></g>`:""}
      <rect x="${nW-6}" y="${nH-6}" width="10" height="10" rx="2" fill="${aColor}44" stroke="${aColor}" stroke-width="1" class="org-resize-handle" data-nid="${n.id}" style="cursor:se-resize"/>
    </g>`;}).join("");

  const nodeCount=allNodes.length;
  const limitWarn=nodeCount>=LIMITS.MAX_ORG_NODES?`<div style="background:rgba(240,168,50,.12);border:1px solid rgba(240,168,50,.3);color:#f0a832;padding:8px 14px;border-radius:8px;font-size:12px;margin-bottom:12px">Limite de ${LIMITS.MAX_ORG_NODES} blocos atingido.</div>`:"";

  return`<div class="page-header">
    <div><div class="page-title">Organograma</div><div class="page-sub">Estrutura da equipe — grupos expansíveis, hierarquias visuais</div></div>
    ${orgConnecting?`<div class="connecting-hint">Clique em outro bloco para conectar <span id="org-cancel-connect" style="cursor:pointer;text-decoration:underline;margin-left:8px">cancelar</span></div>`:""}
  </div>
  ${limitWarn}
  ${isAdmin1?`<div style="display:flex;gap:10px;margin-bottom:14px;flex-wrap:wrap;align-items:flex-end">
    <div class="flow-toolbar">
      <input id="org-name" placeholder="Nome…" style="width:120px;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none"/>
      <input id="org-role" placeholder="Cargo…" style="width:130px;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none"/>
      <select id="org-area" style="background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:12px;outline:none">
        <option value="">Área (opcional)</option>
        ${Object.values(areas).map(a=>`<option value="${esc(a.name)}">${esc(a.name)}</option>`).join("")}
        <option value="__new__">+ Criar nova área…</option>
      </select>
      <input type="color" id="org-color" value="#7c6eff" style="width:32px;height:32px;border:none;background:none;cursor:pointer;border-radius:6px"/>
      <button class="btn-primary" id="btn-add-org-node" ${nodeCount>=LIMITS.MAX_ORG_NODES?"disabled":""}>+ Bloco raiz</button>
      <button class="btn-small" id="btn-add-org-sticky" style="border:1px solid #f0a83244;color:#f0a832;background:#f0a83212">📝 Nota</button>
      <button class="btn-small" id="btn-org-select-mode" style="border:1px solid ${orgSelectMode?"#c8f04e":"#2e2e3a"};color:${orgSelectMode?"#c8f04e":"#7a7a8a"};background:${orgSelectMode?"#c8f04e12":"transparent"}">${orgSelectMode?"✅ Selecionar":"⬜ Selecionar"}</button>
    </div>
  </div>`:""}
  <div class="flow-canvas" style="position:relative">
    <div id="org-stickies-layer" style="position:absolute;inset:0;pointer-events:none;z-index:10;overflow:hidden"></div>
    <svg id="org-svg" width="100%" height="650" style="display:block;cursor:${orgConnecting?"crosshair":orgSelectMode?"crosshair":"grab"}">
      <defs>
        ${orgGradDefs}
        <pattern id="org-grid" width="28" height="28" patternUnits="userSpaceOnUse">
          <path d="M28 0 L0 0 0 28" fill="none" stroke="#18182a" stroke-width="1"/>
        </pattern>
      </defs>
      <rect width="100%" height="100%" fill="url(#org-grid)"/>
      <g id="org-zoom-group" transform="translate(${orgPan.x},${orgPan.y}) scale(${orgZoom})">${groupBgs}${svgEdges}${liveEdge}${svgNodes}${orgSelBox?`<rect x="${Math.min(orgSelBox.x1,orgSelBox.x2)}" y="${Math.min(orgSelBox.y1,orgSelBox.y2)}" width="${Math.abs(orgSelBox.x2-orgSelBox.x1)}" height="${Math.abs(orgSelBox.y2-orgSelBox.y1)}" fill="#7c6eff08" stroke="#7c6eff" stroke-width="1" stroke-dasharray="5,3" style="pointer-events:none"/>`:""}</g>
      ${allNodes.length===0?`<text x="50%" y="45%" text-anchor="middle" dominant-baseline="middle" fill="#2e2e42" font-size="15" font-family="DM Sans,sans-serif">Adicione blocos usando o formulário acima</text>`:""}
    </svg>
  </div>
  ${orgSelectedNodes.size>1?`
  <div id="org-group-bar" style="margin-top:10px;background:#1a1a22;border:1px solid #7c6eff33;border-radius:10px;padding:10px 14px;display:flex;align-items:center;gap:12px;flex-wrap:wrap">
    <span style="font-size:12px;color:#9d93ff;font-weight:700">${orgSelectedNodes.size} blocos selecionados</span>
    <span style="font-size:12px;color:#7a7a8a">Mover para dentro de:</span>
    <select id="org-group-parent" style="background:#13131a;border:1px solid #2e2e3a;border-radius:7px;padding:6px 10px;color:#f0eff5;font-family:inherit;font-size:12px;outline:none;min-width:140px">
      <option value="">— Escolher bloco pai —</option>
      <option value="__remove__">✕ Remover do grupo</option>
      ${allNodes.filter(n=>!orgSelectedNodes.has(n.id)).map(n=>`<option value="${n.id}">${esc(n.name||n.role||"?")}</option>`).join("")}
    </select>
    <button id="org-group-apply" class="btn-primary" style="font-size:12px;padding:6px 14px;background:#7c6eff">Aplicar</button>
    <button id="org-group-clear" class="btn-ghost" style="font-size:12px;padding:6px 10px">Limpar seleção</button>
  </div>`:""}
  <div style="display:flex;align-items:center;justify-content:space-between;margin-top:8px;flex-wrap:wrap;gap:8px">
    <div style="font-size:11px;color:#4a4a5a;display:flex;gap:16px;flex-wrap:wrap">
      <span>🖱 Arraste no fundo para mover a tela</span>
      <span>⬜ Botão "Selecionar" para selecionar vários blocos</span>
      <span>▼ N = expandir grupo (N filhos)</span>
      <span>⭕ Círculo = conectar com linha</span>
      <span>✏ Lápis = editar bloco</span>
    </div>
    <div class="zoom-controls">
      <button class="zoom-btn" id="org-zoom-out">−</button>
      <span id="org-zoom-label" style="font-size:11px;color:#7a7a8a;min-width:38px;text-align:center">${Math.round(orgZoom*100)}%</span>
      <button class="zoom-btn" id="org-zoom-in">+</button>
      <button class="zoom-btn" id="org-zoom-reset" style="font-size:10px;padding:0 8px">Reset</button>
    </div>
  </div>`;
}

// ── ORGANOGRAMA EVENTS ────────────────────────────────────────────────────────
function attachOrgEvents(){
  const svg=document.getElementById("org-svg");if(!svg)return;
  const allNodes=Object.entries(orgData.nodes||{}).map(([id,n])=>({id,...n}));

  document.getElementById("org-cancel-connect")?.addEventListener("click",()=>{orgConnecting=null;render();});

  // Add root node
  document.getElementById("btn-add-org-node")?.addEventListener("click",()=>{
    const name=document.getElementById("org-name")?.value.trim();
    const role=document.getElementById("org-role")?.value.trim();
    const areaName=document.getElementById("org-area")?.value||"";
    const color=document.getElementById("org-color")?.value||"#7c6eff";
    if(!name&&!role){toast("Digite nome ou cargo","error");return;}
    if(Object.keys(orgData.nodes||{}).length>=LIMITS.MAX_ORG_NODES){toast("Limite de blocos atingido","error");return;}
    dbSet(`org/nodes/${uid()}`,{name,role,areaName,color,x:80+Math.random()*400,y:60+Math.random()*200});
    if(document.getElementById("org-name"))document.getElementById("org-name").value="";
    if(document.getElementById("org-role"))document.getElementById("org-role").value="";
  });

  // Expand/collapse toggle
  document.querySelectorAll(".org-toggle").forEach(el=>el.addEventListener("click",e=>{
    e.stopPropagation();
    const nid=el.dataset.nid;
    orgExpanded[nid]=!orgExpanded[nid];
    render();
  }));

  // Add child button — opens modal pre-filled with parentId
  document.querySelectorAll(".org-add-child").forEach(el=>el.addEventListener("click",e=>{
    e.stopPropagation();
    const parentId=el.dataset.nid;
    orgExpanded[parentId]=true; // auto-expand when adding child
    openOrgNodeModal(null, parentId);
  }));

  // Edit node
  document.querySelectorAll(".org-edit-node").forEach(el=>el.addEventListener("click",e=>{e.stopPropagation();openOrgNodeModal(el.dataset.nid,null);}));

  // Delete node (also removes children recursively)
  document.querySelectorAll(".org-del-node").forEach(el=>el.addEventListener("click",e=>{
    e.stopPropagation();
    const id=el.dataset.nid;
    const n=orgData.nodes[id];
    const hasKids=allNodes.filter(c=>c.parentId===id).length>0;
    const msg=hasKids?`Excluir "${n?.name||n?.role||"bloco"}" e todos os seus membros?`:`Excluir este bloco?`;
    if(!confirm(msg))return;
    // Collect all descendants
    function descendants(pid){
      const kids=allNodes.filter(c=>c.parentId===pid).map(c=>c.id);
      return[...kids,...kids.flatMap(k=>descendants(k))];
    }
    const toDelete=[id,...descendants(id)];
    const nn={...orgData.nodes};
    toDelete.forEach(did=>delete nn[did]);
    const ne=Object.fromEntries(Object.entries(orgData.edges||{}).filter(([,ed])=>!toDelete.includes(ed.from)&&!toDelete.includes(ed.to)));
    dbSet("org/nodes",Object.keys(nn).length?nn:null);
    dbSet("org/edges",Object.keys(ne).length?ne:null);
  }));

  // Edge interactions
  document.querySelectorAll(".org-edge-hit").forEach(el=>el.addEventListener("click",e=>{e.stopPropagation();orgSelEdge=orgSelEdge===el.dataset.eid?null:el.dataset.eid;render();}));
  document.querySelectorAll(".org-del-edge").forEach(el=>el.addEventListener("click",e=>{e.stopPropagation();if(confirm("Excluir conexao?")){dbRemove(`org/edges/${el.dataset.eid}`);orgSelEdge=null;render();}}));
  document.querySelectorAll(".org-edit-edge").forEach(el=>el.addEventListener("click",e=>{e.stopPropagation();openOrgEdgeModal(el.dataset.eid);}));

  // Connect handles
  document.querySelectorAll(".org-conn-handle").forEach(el=>el.addEventListener("mousedown",e=>{
    e.stopPropagation();
    orgConnecting={fromId:el.dataset.nid, side:el.dataset.side||"right"};
    render();
  }));

  // Node drag + connect click
  function isVisible(n){
    if(!n.parentId)return true;
    if(!orgExpanded[n.parentId])return false;
    const parent=allNodes.find(p=>p.id===n.parentId);
    return parent?isVisible(parent):true;
  }
  const visNodes=allNodes.filter(n=>isVisible(n));
  document.querySelectorAll(".org-node").forEach(el=>{
    el.addEventListener("mousedown",e=>{
      // Verificar se o clique foi em um controle filho (usando closest para pegar filhos de <g>)
      const ignoredClasses=["org-conn-handle","org-conn-top","org-conn-right","org-del-node","org-edit-node","org-toggle","org-add-child","org-resize-handle"];
      if(ignoredClasses.some(c=>e.target.classList.contains(c)||e.target.closest?.("."+c)))return;
      e.stopPropagation();
      if(orgConnecting){
        const toId=el.dataset.nid;
        if(orgConnecting.fromId!==toId)dbSet(`org/edges/${uid()}`,{from:orgConnecting.fromId,to:toId,fromSide:orgConnecting.side||"right",toSide:"left",mode:orgConnecting.mode||"free",label:""});
        orgConnecting=null;render();return;
      }
      if(e.shiftKey){
        const nid=el.dataset.nid;
        orgSelectedNodes.has(nid)?orgSelectedNodes.delete(nid):orgSelectedNodes.add(nid);
        render();return;
      }
      const r=svg.getBoundingClientRect(),n=visNodes.find(n=>n.id===el.dataset.nid);
      if(n)orgDragging={id:el.dataset.nid,ox:(e.clientX-r.left-orgPan.x)/orgZoom-n.x,oy:(e.clientY-r.top-orgPan.y)/orgZoom-n.y};
    });
  });

  // ── Organograma: event listeners robustos (pan no document, não no SVG) ──
  // ── mousedown no SVG (pan/select) — mousemove/mouseup estão no módulo ──
  svg.addEventListener("mousedown",e=>{
    if(e.target.classList.contains("org-resize-handle")){
      e.stopPropagation();
      const nid=e.target.dataset.nid;
      const n=orgData.nodes?.[nid]; if(!n)return;
      orgResizing={id:nid,startX:e.clientX,startY:e.clientY,startW:n.w||170,startH:n.h||68};
      return;
    }
    if(e.target!==svg&&e.target.getAttribute("fill")!=="url(#org-grid)")return;
    if(orgConnecting)return;
    const r=svg.getBoundingClientRect();
    if(orgSelectMode){
      if(!e.shiftKey) orgSelectedNodes.clear();
      const cx=(e.clientX-r.left-orgPan.x)/orgZoom;
      const cy=(e.clientY-r.top-orgPan.y)/orgZoom;
      orgSelBox={x1:cx,y1:cy,x2:cx,y2:cy};
      render();
    } else {
      orgPanning=true;
      orgPanStart={x:e.clientX-orgPan.x, y:e.clientY-orgPan.y};
      svg.style.cursor="grabbing";
    }
  });
  svg.addEventListener("click",e=>{
    if(orgConnecting&&e.target===svg){orgConnecting=null;render();}
    if(e.target===svg&&orgSelEdge){orgSelEdge=null;render();}
  });
  // Zoom
  document.getElementById("org-zoom-in")?.addEventListener("click",()=>{orgZoom=Math.min(2.5,+(orgZoom+0.15).toFixed(2));render();});
  document.getElementById("org-zoom-out")?.addEventListener("click",()=>{orgZoom=Math.max(0.25,+(orgZoom-0.15).toFixed(2));render();});
  document.getElementById("org-zoom-reset")?.addEventListener("click",()=>{orgZoom=1;orgPan={x:0,y:0};render();});
  svg.addEventListener("wheel",e=>{
    e.preventDefault();
    const r=svg.getBoundingClientRect();
    const mx=e.clientX-r.left, my=e.clientY-r.top;
    const delta=e.deltaY>0?-0.1:0.1;
    const newZoom=Math.min(2.5,Math.max(0.25,+(orgZoom+delta).toFixed(2)));
    orgPan.x=mx-(mx-orgPan.x)*(newZoom/orgZoom);
    orgPan.y=my-(my-orgPan.y)*(newZoom/orgZoom);
    orgZoom=newZoom;
    render();
  },{passive:false});

  // ── Org group bar ──
  document.getElementById("org-group-apply")?.addEventListener("click",async()=>{
    const parentId=document.getElementById("org-group-parent")?.value;
    if(!parentId)return;
    if(parentId==="__remove__"){
      for(const id of orgSelectedNodes) await dbSet(`org/nodes/${id}/parentId`,null);
      toast("Blocos removidos do grupo","success");
    } else {
      for(const id of orgSelectedNodes){
        if(id===parentId)continue;
        await dbSet(`org/nodes/${id}/parentId`,parentId);
      }
      orgExpanded[parentId]=true;
      toast(`${orgSelectedNodes.size} bloco(s) agrupado(s)`,"success");
    }
    orgSelectedNodes.clear(); render();
  });
  document.getElementById("org-group-clear")?.addEventListener("click",()=>{orgSelectedNodes.clear();render();});

  // ── Org sticky notes ──
  document.getElementById("btn-org-select-mode")?.addEventListener("click",()=>{
    orgSelectMode=!orgSelectMode;
    if(!orgSelectMode){orgSelectedNodes.clear();}
    render();
  });
  document.getElementById("btn-add-org-sticky")?.addEventListener("click",()=>{
    const id=uid();
    dbSet(`org/stickies/${id}`,{id,text:"",color:"#f0a832",x:80+Math.random()*300,y:60+Math.random()*200,expanded:true,createdAt:new Date().toISOString()});
  });
  renderOrgStickies();

  // ── Touch events mobile — Organograma (só visualização + clique nos blocos) ──
  (function attachOrgTouch(){
    const svg=document.getElementById("org-svg"); if(!svg)return;
    let lastDist=0, touchStartX=0, touchStartY=0, panStartX=0, panStartY=0;
    svg.addEventListener("touchstart",e=>{
      if(e.touches.length===2){
        const dx=e.touches[0].clientX-e.touches[1].clientX;
        const dy=e.touches[0].clientY-e.touches[1].clientY;
        lastDist=Math.sqrt(dx*dx+dy*dy);
      } else if(e.touches.length===1){
        touchStartX=e.touches[0].clientX;
        touchStartY=e.touches[0].clientY;
        panStartX=orgPan.x;
        panStartY=orgPan.y;
      }
    },{passive:true});
    svg.addEventListener("touchmove",e=>{
      e.preventDefault();
      if(e.touches.length===2){
        const dx=e.touches[0].clientX-e.touches[1].clientX;
        const dy=e.touches[0].clientY-e.touches[1].clientY;
        const dist=Math.sqrt(dx*dx+dy*dy);
        if(lastDist>0){
          const scale=dist/lastDist;
          orgZoom=Math.min(2.5,Math.max(0.25,+(orgZoom*scale).toFixed(2)));
          render();
        }
        lastDist=dist;
      } else if(e.touches.length===1){
        orgPan.x=panStartX+(e.touches[0].clientX-touchStartX);
        orgPan.y=panStartY+(e.touches[0].clientY-touchStartY);
        render();
      }
    },{passive:false});
    svg.addEventListener("touchend",()=>{lastDist=0;},{passive:true});
  })();
} // fim attachOrgEvents

function renderOrgStickies(){
  const layer=document.getElementById("org-stickies-layer"); if(!layer)return;
  layer.innerHTML="";
  Object.entries(orgStickies).forEach(([sid,s])=>{
    const div=document.createElement("div");
    div.dataset.sid=sid;
    div.style.cssText=`position:absolute;left:${s.x}px;top:${s.y}px;width:200px;pointer-events:all;z-index:20;`;
    const color=s.color||"#f0a832";
    const expanded=s.expanded!==false;
    div.innerHTML=`
      <div class="sticky-note" style="background:${color}18;border:1.5px solid ${color}55;border-radius:10px;box-shadow:0 4px 18px rgba(0,0,0,.35);overflow:hidden;user-select:none">
        <div class="sticky-header" style="display:flex;align-items:center;gap:6px;padding:6px 8px;background:${color}30;cursor:grab;border-bottom:1px solid ${color}33">
          <span style="font-size:13px">📝</span>
          <span style="flex:1;font-size:11px;font-weight:700;color:${color};font-family:'Syne',sans-serif;white-space:nowrap;overflow:hidden;text-overflow:ellipsis">${s.text?s.text.slice(0,28)+(s.text.length>28?"…":""):"Nova nota"}</span>
          <div style="display:flex;gap:4px">
            ${isAdmin()?`<div class="org-sticky-color-btn" data-sid="${sid}" title="Cor" style="width:14px;height:14px;border-radius:50%;background:${color};cursor:pointer;border:2px solid ${color}88"></div>`:""}
            <div class="org-sticky-toggle" data-sid="${sid}" title="${expanded?"Minimizar":"Expandir"}" style="width:18px;height:18px;display:flex;align-items:center;justify-content:center;cursor:pointer;color:${color};font-size:12px;border-radius:4px">${expanded?"▲":"▼"}</div>
            ${isAdmin()?`<div class="org-sticky-del" data-sid="${sid}" title="Excluir" style="width:18px;height:18px;display:flex;align-items:center;justify-content:center;cursor:pointer;color:#ff6b6b;font-size:12px;border-radius:4px">✕</div>`:""}
          </div>
        </div>
        ${expanded?`<div style="padding:10px">
          <div class="org-sticky-body" data-sid="${sid}" contenteditable="true" spellcheck="false" style="font-size:12px;color:#d0d0d8;line-height:1.7;min-height:60px;outline:none;word-break:break-word;white-space:pre-wrap;font-family:'DM Sans',sans-serif">${esc(s.text||"")}</div>
        </div>`:""}
      </div>`;
    layer.appendChild(div);

    // Drag
    const header=div.querySelector(".sticky-header");
    let dsx=0,dsy=0,startX=0,startY=0,draggingS=false;
    header.addEventListener("mousedown",e=>{
      if(e.target.classList.contains("org-sticky-toggle")||e.target.classList.contains("org-sticky-del")||e.target.classList.contains("org-sticky-color-btn"))return;
      e.preventDefault(); e.stopPropagation();
      draggingS=true; startX=e.clientX; startY=e.clientY; dsx=s.x; dsy=s.y;
      header.style.cursor="grabbing";
      function onMove(ev){
        if(!draggingS)return;
        div.style.left=Math.max(0,dsx+(ev.clientX-startX))+"px";
        div.style.top=Math.max(0,dsy+(ev.clientY-startY))+"px";
      }
      function onUp(ev){
        draggingS=false; header.style.cursor="grab";
        dbSet(`org/stickies/${sid}/x`,Math.max(0,dsx+(ev.clientX-startX)));
        dbSet(`org/stickies/${sid}/y`,Math.max(0,dsy+(ev.clientY-startY)));
        document.removeEventListener("mousemove",onMove);
        document.removeEventListener("mouseup",onUp);
      }
      document.addEventListener("mousemove",onMove);
      document.addEventListener("mouseup",onUp);
    });

    // Toggle expand/collapse
    div.querySelector(".org-sticky-toggle")?.addEventListener("click",e=>{
      e.stopPropagation();
      dbSet(`org/stickies/${sid}/expanded`,!expanded);
    });

    // Delete
    div.querySelector(".org-sticky-del")?.addEventListener("click",e=>{
      e.stopPropagation();
      if(confirm("Excluir esta nota?")) dbRemove(`org/stickies/${sid}`);
    });

    // Save text on blur
    div.querySelector(".org-sticky-body")?.addEventListener("blur",e=>{
      dbSet(`org/stickies/${sid}/text`,e.target.innerText.trim());
    });
    div.querySelector(".org-sticky-body")?.addEventListener("click",e=>e.stopPropagation());

    // Color picker
    div.querySelector(".org-sticky-color-btn")?.addEventListener("click",e=>{
      e.stopPropagation();
      const STICKY_COLORS=["#f0a832","#c8f04e","#7c6eff","#4ac8e8","#ff6b6b","#4ae89c","#e84ab8"];
      showCtxMenu(e.clientX,e.clientY,STICKY_COLORS.map((c,i)=>({
        action:c,
        icon:`<span style="display:inline-block;width:12px;height:12px;border-radius:50%;background:${c};margin-right:2px;vertical-align:middle"></span>`,
        label:["Laranja","Verde","Roxo","Azul","Vermelho","Verde-água","Rosa"][i],
        fn:()=>dbSet(`org/stickies/${sid}/color`,c)
      })));
    });
  });
}

function openOrgNodeModal(nodeId, parentId=null){
  const n=nodeId?{id:nodeId,...orgData.nodes[nodeId]}:{};
  const parentNode=parentId?orgData.nodes[parentId]:null;
  const parentLabel=parentNode?(parentNode.name||parentNode.role||"grupo"):"";
  openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:440px"><div class="modal-header"><div class="modal-title">${nodeId?"Editar":"Novo"} Bloco${parentLabel?" em "+esc(parentLabel):""}</div><button class="icon-btn" id="m-x">✕</button></div><div class="modal-body">
    ${parentLabel?`<div style="font-size:11px;color:#7a7a8a;background:#1a1a22;border:1px solid #2e2e3a;padding:7px 10px;border-radius:7px;margin-bottom:12px">Será adicionado como membro de: <strong style="color:#c8f04e">${esc(parentLabel)}</strong></div>`:""}
    <div class="field"><label>Nome</label><input id="m-oname" value="${esc(n.name||"")}" placeholder="Nome do colaborador…" autofocus/></div>
    <div style="font-size:11px;color:#4a4a5a;background:#13131a;border:1px solid #2e2e3a;border-radius:6px;padding:7px 10px;margin-bottom:12px">💡 Redimensione o bloco arrastando o canto inferior direito diretamente no canvas.</div>
    <div class="field">
      <label>Criar nova área e vincular <span style="color:#7a7a8a;font-size:10px">(opcional)</span></label>
      <div style="display:flex;gap:8px">
        <input id="m-onewarea" placeholder="Nome da nova área…" style="flex:1;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none"/>
        <input type="color" id="m-onewareacolor" value="#7c6eff" style="width:38px;height:38px;border:none;background:none;cursor:pointer;border-radius:6px"/>
      </div>
    </div>
    <div class="field"><label>Cargo / Função</label><input id="m-orole" value="${esc(n.role||"")}" placeholder="Ex: Gerente Comercial, Designer…"/></div>
    <div class="field">
      <label>Áreas / Departamentos <span style="color:#7a7a8a;font-size:10px">(cor dividida verticalmente)</span></label>
      <div id="m-org-area-chips" style="display:flex;gap:6px;flex-wrap:wrap;min-height:24px;margin-bottom:6px"></div>
      <select id="m-oarea" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none">
        <option value="">+ Adicionar área…</option>
        ${Object.values(areas).map(a=>`<option value="${a.id||esc(a.name)}">${esc(a.name)}</option>`).join("")}
      </select>
    </div>
    <div class="field"><label>Cor personalizada <span style="color:#7a7a8a;font-size:11px">(usado quando sem área)</span></label>
      <input type="color" id="m-ocolor" value="${n.color||"#7c6eff"}" style="width:40px;height:32px;border:none;background:none;cursor:pointer;border-radius:6px"/>
    </div>
  </div><div class="modal-footer"><button class="btn-ghost" id="m-cancel">Cancelar</button><button class="btn-primary" id="m-save">Salvar</button></div></div></div>`);
  document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;

  // Multi-area chips for org
  const areaById=Object.entries(areas).reduce((acc,[id,a])=>{acc[id]=a;return acc;},{});
  let selOrgAreaIds=Array.isArray(n.areaIds)?[...n.areaIds]:(n.areaId?[n.areaId]:[]);
  function refreshOrgAreaChips(){
    const el=document.getElementById("m-org-area-chips");if(!el)return;
    el.innerHTML=selOrgAreaIds.map(aid=>{
      const a=areaById[aid];if(!a)return"";
      return`<span style="background:${a.color}22;color:${a.color};border:1px solid ${a.color}55;padding:3px 10px;border-radius:20px;font-size:12px;cursor:pointer" data-oid="${aid}">✕ ${esc(a.name)}</span>`;
    }).join("")||`<span style="font-size:12px;color:#5a5a6a">Nenhuma área</span>`;
    el.querySelectorAll("[data-oid]").forEach(ch=>ch.addEventListener("click",()=>{selOrgAreaIds=selOrgAreaIds.filter(id=>id!==ch.dataset.oid);refreshOrgAreaChips();}));
  }
  refreshOrgAreaChips();
  document.getElementById("m-oarea")?.addEventListener("change",e=>{
    const val=e.target.value;
    if(val&&!selOrgAreaIds.includes(val)){selOrgAreaIds.push(val);refreshOrgAreaChips();}
    e.target.value="";
  });

  document.getElementById("m-save").onclick=async()=>{
    const name=document.getElementById("m-oname").value.trim();
    const role=document.getElementById("m-orole").value.trim();
    const areaName=selOrgAreaIds.length?Object.values(areas).find(a=>Object.keys(areas).find(k=>k===selOrgAreaIds[0]))?.name||"":"";
    const color=document.getElementById("m-ocolor").value;
    const fsize=12; // fixed font size — resize via drag
    if(!name&&!role){toast("Preencha nome ou cargo","error");return;}
    // Position child near parent
    const px=parentNode?parentNode.x:null, py=parentNode?parentNode.y:null;
    const defaultX=px!=null?px+(Object.values(orgData.nodes||{}).filter(c=>c.parentId===parentId).length*190):80+Math.random()*400;
    const defaultY=py!=null?py+110:60+Math.random()*300;
    const existingNode=nodeId?orgData.nodes[nodeId]:{};
    const areaNameFirst=selOrgAreaIds.length?(Object.entries(areas).find(([id])=>id===selOrgAreaIds[0])?.[1]?.name||""):"";
    const data={...existingNode,name,role,areaName:areaNameFirst||areaName,color,
      areaIds:selOrgAreaIds.length?selOrgAreaIds:null,
      areaId:selOrgAreaIds[0]||null,
      w:existingNode.w,h:existingNode.h,
      parentId:nodeId?(n.parentId||null):parentId,
      x:n.x||defaultX,y:n.y||defaultY};
    await dbSet(`org/nodes/${nodeId||uid()}`,data);
    await logAction("editar_org",`Bloco organograma: ${name||role}${parentLabel?" (em "+parentLabel+")":""}`);
    toast("Salvo!","success");closeModal();
  };
  overlayClose("ov");
}

function openOrgEdgeModal(edgeId){
  const e=orgData.edges?.[edgeId];if(!e)return;
  const fromN=orgData.nodes?.[e.from],toN=orgData.nodes?.[e.to];
  openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:420px"><div class="modal-header"><div class="modal-title">Editar conexão</div><button class="icon-btn" id="m-x">✕</button></div><div class="modal-body">
    <div style="display:flex;align-items:center;gap:8px;margin-bottom:16px;font-size:12px;color:#7a7a8a">
      <span style="background:#1e1e28;border:1px solid #2e2e3a;padding:4px 10px;border-radius:6px;color:#f0eff5">${esc(fromN?.name||fromN?.role||"?")}</span>
      <span style="color:#7c6eff;font-size:16px">${e.mode==="hierarchy"?"↓":"→"}</span>
      <span style="background:#1e1e28;border:1px solid #2e2e3a;padding:4px 10px;border-radius:6px;color:#f0eff5">${esc(toN?.name||toN?.role||"?")}</span>
    </div>
    <div class="field"><label>Tipo de conexão</label>
      <select id="m-emode" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none">
        <option value="hierarchy" ${e.mode==="hierarchy"?"selected":""}>Hierarquia (cima para baixo)</option>
        <option value="free" ${e.mode==="free"?"selected":""}>Livre (lateral)</option>
      </select>
    </div>
    <div class="field"><label>Rótulo <span style="color:#7a7a8a;font-size:11px">(opcional)</span></label>
      <input id="m-elabel" value="${esc(e.label||"")}" placeholder="Ex: reporta a, substitui, colabora com…"/>
    </div>
  </div><div class="modal-footer"><button class="btn-ghost" id="m-cancel">Cancelar</button><button class="btn-primary" id="m-save">Salvar</button></div></div></div>`);
  document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;
  document.getElementById("m-save").onclick=async()=>{
    await dbSet(`org/edges/${edgeId}/mode`,document.getElementById("m-emode").value);
    await dbSet(`org/edges/${edgeId}/label`,document.getElementById("m-elabel").value.trim()||null);
    orgSelEdge=edgeId;closeModal();render();toast("Conexao atualizada!","success");
  };
  overlayClose("ov");
}

// ── AREA CRUD ─────────────────────────────────────────────────────────────────
async function deleteArea(id){
  const name=areas[id]?.name||"";
  await dbRemove(`areas/${id}`);
  for(const[tid,t]of Object.entries(tasks))if(t.areaId===id)await dbRemove(`tasks/${tid}`);
  await logAction("excluir_area",`Área excluída: ${name}`);
  if(activeAreaId===id){activeAreaId=null;page="dashboard";}
}

// ── MODALS ────────────────────────────────────────────────────────────────────
function openModal(html){document.getElementById("modals").innerHTML=html;}
function closeModal(){document.getElementById("modals").innerHTML="";}
function overlayClose(id){document.getElementById(id)?.addEventListener("click",e=>{if(e.target.id===id)closeModal();});}

function openAreaModal(prefillParentId=""){
  if(Object.keys(areas).length>=LIMITS.MAX_AREAS){toast(`Limite de ${LIMITS.MAX_AREAS} áreas atingido`,"error");return;}
  const parentName=prefillParentId&&areas[prefillParentId]?.name;
  const title=parentName?`Nova subárea de "${esc(parentName)}"`:("Nova área");
  openModal(`<div class="overlay" id="ov"><div class="modal"><div class="modal-header"><div class="modal-title">${title}</div><button class="icon-btn" id="m-x">✕</button></div><div class="modal-body"><div class="field"><label>Nome *</label><input id="m-name" placeholder="${parentName?`Subárea de ${esc(parentName)}…`:"Ex: Comercial, TI, RH…"}" autofocus/></div><div class="field"><label>Cor</label><div style="display:flex;gap:8px;flex-wrap:wrap;align-items:center">${AREA_COLORS.map(c=>`<div class="color-pick" data-color="${c}" style="width:28px;height:28px;border-radius:6px;background:${c};cursor:pointer"></div>`).join("")}<input type="color" id="m-cc" value="${areas[prefillParentId]?.color||AREA_COLORS[0]}" style="width:28px;height:28px;border:none;background:none;cursor:pointer"/></div></div></div><div class="modal-footer"><button class="btn-ghost" id="m-cancel">Cancelar</button><button class="btn-primary" id="m-save">Criar</button></div></div></div>`);
  let col=areas[prefillParentId]?.color||AREA_COLORS[0];
  document.querySelectorAll(".color-pick").forEach(el=>{if(el.dataset.color===col)el.style.boxShadow=`0 0 0 3px #0c0c0f,0 0 0 5px ${col}`;el.addEventListener("click",()=>{col=el.dataset.color;document.querySelectorAll(".color-pick").forEach(e=>e.style.boxShadow="none");el.style.boxShadow=`0 0 0 3px #0c0c0f,0 0 0 5px ${col}`;});});
  document.getElementById("m-cc").addEventListener("input",e=>col=e.target.value);
  document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;
  document.getElementById("m-save").onclick=async()=>{
    const name=document.getElementById("m-name").value.trim();
    if(!name){toast("Digite um nome","error");return;}
    const id=uid();
    await dbSet(`areas/${id}`,{id,name,color:col,parentId:prefillParentId||null,createdAt:new Date().toISOString()});
    await logAction("criar_area",`Área criada: ${name}${prefillParentId?" (subárea de "+areas[prefillParentId]?.name+")":""}`);
    if(prefillParentId)expandedAreas.add(prefillParentId);
    toast("Área criada!","success");closeModal();
  };
  document.getElementById("m-name").addEventListener("keydown",e=>{if(e.key==="Enter")document.getElementById("m-save").click();});
  overlayClose("ov");
}

function openEditAreaModal(areaId){
  const a=areas[areaId];if(!a)return;
  const rootAreas=Object.entries(areas).map(([id,ar])=>({id,...ar})).filter(ar=>!ar.parentId&&ar.id!==areaId);
  const parentOpts=`<option value="">— Área raiz (nível principal) —</option>`+rootAreas.map(ar=>`<option value="${ar.id}" ${ar.id===a.parentId?"selected":""}>${esc(ar.name)}</option>`).join("");
  openModal(`<div class="overlay" id="ov"><div class="modal"><div class="modal-header"><div class="modal-title">Editar Área</div><button class="icon-btn" id="m-x">✕</button></div><div class="modal-body"><div class="field"><label>Nome *</label><input id="m-name" value="${esc(a.name)}" autofocus/></div><div class="field"><label>Cor</label><div style="display:flex;gap:8px;flex-wrap:wrap;align-items:center">${AREA_COLORS.map(c=>`<div class="color-pick" data-color="${c}" style="width:28px;height:28px;border-radius:6px;background:${c};cursor:pointer"></div>`).join("")}<input type="color" id="m-cc" value="${a.color}" style="width:28px;height:28px;border:none;background:none;cursor:pointer"/></div></div><div class="field"><label>Pertence a (subárea de)</label><select id="m-parent" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none">${parentOpts}</select></div></div><div class="modal-footer"><button class="btn-danger" id="m-del">Excluir</button><button class="btn-ghost" id="m-cancel">Cancelar</button><button class="btn-primary" id="m-save">Salvar</button></div></div></div>`);
  let col=a.color;
  document.querySelectorAll(".color-pick").forEach(el=>{
    if(el.dataset.color===col)el.style.boxShadow=`0 0 0 3px #0c0c0f,0 0 0 5px ${col}`;
    el.addEventListener("click",()=>{col=el.dataset.color;document.querySelectorAll(".color-pick").forEach(e=>e.style.boxShadow="none");el.style.boxShadow=`0 0 0 3px #0c0c0f,0 0 0 5px ${col}`;});
  });
  document.getElementById("m-cc").addEventListener("input",e=>col=e.target.value);
  document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;
  document.getElementById("m-save").onclick=async()=>{
    const name=document.getElementById("m-name").value.trim();
    if(!name){toast("Digite um nome","error");return;}
    const parentId=document.getElementById("m-parent").value||null;
    await dbSet(`areas/${areaId}/name`,name);
    await dbSet(`areas/${areaId}/color`,col);
    await dbSet(`areas/${areaId}/parentId`,parentId);
    if(parentId)expandedAreas.add(parentId);
    await logAction("editar_area",`Área editada: ${a.name} → ${name}`);
    toast("Área atualizada!","success");closeModal();
  };
  document.getElementById("m-del").onclick=async()=>{
    if(!confirm(`Excluir "${a.name}"? As subáreas se tornarão áreas raiz.`))return;
    Object.entries(areas).forEach(([id,ar])=>{if(ar.parentId===areaId)dbSet(`areas/${id}/parentId`,null);});
    await dbRemove(`areas/${areaId}`);
    await logAction("excluir_area",`Área excluída: ${a.name}`);
    toast("Área excluída","warning");closeModal();
    if(page==="area"&&activeAreaId===areaId)nav("dashboard");
  };
  document.getElementById("m-name").addEventListener("keydown",e=>{if(e.key==="Enter")document.getElementById("m-save").click();});
  overlayClose("ov");
}

const CELEBRATION_GIFS=[
  {url:"https://media.tenor.com/qCfbcDGPAaYAAAAC/confetti-congratulations.gif",msg:"🎉 Arrasou! Tarefa concluída!",color:"#c8f04e"},
  {url:"https://media.tenor.com/ZCZTSNZczWgAAAAC/you-did-it-congratulations.gif",msg:"💪 Missão cumprida! Continue assim!",color:"#7c6eff"},
  {url:"https://media.tenor.com/NkEwMGCPuLAAAAAC/minions-banana.gif",msg:"🍌 BANANA! Tarefa destruída!",color:"#f0a832"},
];

function showCelebrationModal(taskTitle){
  const g=CELEBRATION_GIFS[Math.floor(Math.random()*CELEBRATION_GIFS.length)];
  openModal(`<div class="overlay" id="ov" style="background:rgba(0,0,0,.75)"><div class="modal" style="max-width:420px;text-align:center;padding:0;overflow:hidden;border:2px solid ${g.color}40">
    <div style="padding:20px 24px 12px">
      <div style="font-size:13px;font-weight:700;text-transform:uppercase;letter-spacing:1px;color:${g.color};margin-bottom:8px">Concluído!</div>
      <div style="font-family:'Syne',sans-serif;font-size:16px;font-weight:700;color:#f0eff5;margin-bottom:4px">${esc(taskTitle)}</div>
      <div style="font-size:13px;color:#a0a0b0">${g.msg}</div>
    </div>
    <div style="width:100%;max-height:240px;overflow:hidden;display:flex;align-items:center;justify-content:center;background:#0c0c0f">
      <img src="${g.url}" alt="celebração" style="width:100%;max-height:240px;object-fit:cover" onerror="this.style.display='none';this.nextElementSibling.style.display='block'"/>
      <div style="display:none;font-size:60px;padding:30px">🎉</div>
    </div>
    <div style="padding:16px 24px">
      <button class="btn-primary" id="m-cel-close" style="width:100%;background:${g.color};color:#0c0c0f;font-weight:700">Continuar 🚀</button>
    </div>
  </div></div>`);
  document.getElementById("m-cel-close").onclick=closeModal;
  overlayClose("ov");
  // Auto-close after 8s
  setTimeout(()=>{if(document.getElementById("m-cel-close"))closeModal();},8000);
}

function openTaskModal(init={}){
  if(!init.id&&Object.keys(tasks).length>=LIMITS.MAX_TASKS){
    safePurgeTasks().then(ok=>{if(ok)openTaskModal(init);});return;
  }
  const isCreator=!init.id||(init.creatorId===currentUser?.uid)||isAdmin();
  const existingResps=Array.isArray(init.resps)?init.resps:(init.resp?[init.resp]:[]);

  // Filtro: usuários com permissão na área selecionada
  function buildRespOptions(areaId){
    let filtered;
    if(!areaId){
      filtered=Object.values(users);
    } else {
      filtered=Object.values(users).filter(u=>{
        // Admins sempre aparecem
        if(u.role==="admin1"||u.role==="admin") return true;
        // Usuário aparece se tiver a área nas suas permissões
        const perms=u.permissions||[];
        return perms.includes(areaId);
      });
      // Se nenhum usuário comum tem permissão ainda, mostra todos (segurança)
      const nonAdmins=filtered.filter(u=>u.role==="user");
      if(!nonAdmins.length) filtered=Object.values(users);
    }
    return filtered.filter(u=>u.name).map(u=>`<option value="${esc(u.name)}">${esc(u.name)}${u.email?" ("+esc(u.email)+")":""}</option>`).join("");
  }
  openModal(`<div class="overlay" id="ov"><div class="modal"><div class="modal-header"><div class="modal-title">${init.id?"Editar":"Nova"} Tarefa</div><button class="icon-btn" id="m-x">\u2715</button></div><div class="modal-body">
    <div class="field"><label>T\u00edtulo *</label><input id="m-title" value="${esc(init.title||"")}" placeholder="Descreva a tarefa\u2026"/></div>
    <div class="field"><label>Descri\u00e7\u00e3o</label><textarea id="m-desc" rows="3">${esc(init.desc||"")}</textarea></div>
    <div class="field-row">
      <div class="field"><label>\u00c1rea</label><select id="m-area">${Object.entries(areas).map(([id,a])=>`<option value="${id}" ${init.areaId===id?"selected":""}>${esc(a.name)}</option>`).join("")}</select></div>
      <div class="field"><label>Prioridade</label><select id="m-priority">${Object.entries(PRIORITY).map(([k,v])=>`<option value="${k}" ${(init.priority||"media")===k?"selected":""}>${v.label}</option>`).join("")}</select></div>
    </div>
    <div class="field">
      <label>Respons\u00e1veis <span style="color:#7a7a8a;font-size:11px">${isCreator?"(voc\u00ea pode alterar — \u00e9 o criador)":"(somente o criador pode alterar)"}</span></label>
      <div id="resp-chips" style="display:flex;gap:6px;flex-wrap:wrap;min-height:28px;margin-bottom:8px"></div>
      ${isCreator?`<div style="display:flex;gap:6px;flex-wrap:wrap;align-items:center">
        <select id="m-resp-sel" style="flex:1;min-width:130px;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:7px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none">
          <option value="">Selecionar usu\u00e1rio\u2026</option>
          ${buildRespOptions(init.areaId)}
        </select>
        <input id="m-resp-manual" placeholder="Ou digitar nome\u2026" style="flex:1;min-width:100px;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:7px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none"/>
        <button class="btn-small" id="m-resp-add" style="border:1px solid #2e2e3a;color:#c8f04e;white-space:nowrap">+ Add</button>
        <button class="btn-small" id="m-resp-all" title="Adicionar todos os membros da área selecionada" style="border:1px solid #7c6eff44;color:#9d93ff;white-space:nowrap">👥 Área</button>
        <button class="btn-small" id="m-resp-org" title="Adicionar toda a organização" style="border:1px solid #c8f04e44;color:#c8f04e;white-space:nowrap">📢 Toda org</button>
      </div>`:""}
    </div>
    <div class="field-row">
      <div class="field"><label>Status</label><select id="m-status">${Object.entries(STATUS).map(([k,v])=>`<option value="${k}" ${(init.status||"a-fazer")===k?"selected":""}>${v.label}</option>`).join("")}</select></div>
      <div class="field"><label>Prazo</label><input type="date" id="m-date" value="${init.date||""}"/></div>
    </div>
    ${init.creatorName?`<div style="font-size:11px;color:#5a5a6a;margin-top:4px">\u270f Criada por: ${esc(init.creatorName)}</div>`:""}
    <div class="field" style="margin-top:8px">
      <label>Também aparece em <span style="color:#7a7a8a;font-size:11px">(opcional — a tarefa será visível nessas áreas também)</span></label>
      <div id="extra-areas-chips" style="display:flex;gap:6px;flex-wrap:wrap;min-height:24px;margin-bottom:6px"></div>
      <select id="m-extra-area-sel" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:7px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none">
        <option value="">+ Adicionar outra área…</option>
        ${Object.entries(areas).map(([id,a])=>`<option value="${id}">${esc(a.name)}</option>`).join("")}
      </select>
    </div>
    <div class="field" style="display:flex;align-items:center;gap:10px;margin-top:8px">
      <input type="checkbox" id="m-allusers" style="width:16px;height:16px;accent-color:#c8f04e" ${init.allUsers?"checked":""}/>
      <label for="m-allusers" style="font-size:13px;color:#a0a0b0;cursor:pointer">Tarefa coletiva — todos os usuários devem marcar como concluída</label>
    </div>
    <div class="field" style="margin-top:10px;border-top:1px solid #1e1e28;padding-top:12px">
      <label style="display:flex;align-items:center;gap:8px;cursor:pointer">
        <input type="checkbox" id="m-recur-on" style="width:16px;height:16px;accent-color:#c8f04e" ${init.recurrence?"checked":""}/>
        <span style="font-size:13px;color:#a0a0b0">Tarefa recorrente</span>
      </label>
      <div id="m-recur-fields" style="margin-top:10px;display:${init.recurrence?"flex":"none"};flex-direction:column;gap:8px;background:#13131a;border:1px solid #2e2e3a;border-radius:8px;padding:12px">
        <div class="field-row">
          <div class="field">
            <label>Frequência</label>
            <select id="m-recur-freq" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:7px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none">
              <option value="diaria" ${init.recurrence?.freq==="diaria"?"selected":""}>Diária</option>
              <option value="semanal" ${(init.recurrence?.freq==="semanal"||!init.recurrence?.freq)?"selected":""}>Semanal</option>
              <option value="quinzenal" ${init.recurrence?.freq==="quinzenal"?"selected":""}>Quinzenal (15 dias)</option>
              <option value="mensal" ${init.recurrence?.freq==="mensal"?"selected":""}>Mensal</option>
              <option value="anual" ${init.recurrence?.freq==="anual"?"selected":""}>Anual</option>
              <option value="custom" ${init.recurrence?.freq==="custom"?"selected":""}>Intervalo personalizado</option>
            </select>
          </div>
          <div class="field" id="m-recur-custom-wrap" style="display:${init.recurrence?.freq==="custom"?"block":"none"}">
            <label>A cada (dias)</label>
            <input type="number" id="m-recur-interval" min="1" max="365" value="${init.recurrence?.interval||7}" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:7px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none"/>
          </div>
        </div>
        <div class="field-row">
          <div class="field">
            <label>Condição de criação</label>
            <select id="m-recur-cond" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:7px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none">
              <option value="after_complete" ${(init.recurrence?.cond==="after_complete"||!init.recurrence?.cond)?"selected":""}>Criar nova após concluir</option>
              <option value="fixed_date" ${init.recurrence?.cond==="fixed_date"?"selected":""}>Data fixa (independente da conclusão)</option>
            </select>
          </div>
        </div>
        <div style="font-size:11px;color:#5a5a6a">🔁 A próxima ocorrência será criada automaticamente ao concluir esta tarefa</div>
      </div>
    </div>
  </div><div class="modal-footer"><button class="btn-ghost" id="m-cancel">Cancelar</button><button class="btn-primary" id="m-save">Salvar</button></div></div></div>`);

  let selResps=[...existingResps];
  function refreshRespChips(){
    const el=document.getElementById("resp-chips");if(!el)return;
    el.innerHTML=selResps.map(r=>`<span style="background:#7c6eff22;color:#9d93ff;border:1px solid #7c6eff44;padding:4px 10px;border-radius:20px;font-size:12px;${isCreator?"cursor:pointer":""}" data-r="${esc(r)}">${isCreator?"\u2715 ":""}${esc(r)}</span>`).join("")||`<span style="font-size:12px;color:#5a5a6a">Nenhum respons\u00e1vel</span>`;
    if(isCreator) el.querySelectorAll("[data-r]").forEach(ch=>ch.addEventListener("click",()=>{selResps=selResps.filter(r=>r!==ch.dataset.r);refreshRespChips();}));
  }
  refreshRespChips();

  // Atualiza o select de responsáveis quando a área principal muda
  if(isCreator){
    document.getElementById("m-area")?.addEventListener("change",e=>{
      const sel=document.getElementById("m-resp-sel"); if(!sel)return;
      const cur=sel.value;
      sel.innerHTML=`<option value="">Selecionar usuário…</option>${buildRespOptions(e.target.value)}`;
      sel.value=cur;
    });
  }

  // Extra areas chips
  let extraAreaIds=Array.isArray(init.extraAreaIds)?[...init.extraAreaIds]:[];
  function refreshExtraAreaChips(){
    const el=document.getElementById("extra-areas-chips");if(!el)return;
    el.innerHTML=extraAreaIds.map(aid=>{
      const a=areas[aid];if(!a)return"";
      return`<span style="background:${a.color}18;color:${a.color};border:1px solid ${a.color}44;padding:4px 10px;border-radius:20px;font-size:12px;cursor:pointer" data-eid="${aid}">✕ ${esc(a.name)}</span>`;
    }).join("")||`<span style="font-size:12px;color:#5a5a6a">Nenhuma área extra</span>`;
    el.querySelectorAll("[data-eid]").forEach(ch=>ch.addEventListener("click",()=>{extraAreaIds=extraAreaIds.filter(id=>id!==ch.dataset.eid);refreshExtraAreaChips();}));
  }
  refreshExtraAreaChips();
  document.getElementById("m-extra-area-sel")?.addEventListener("change",e=>{
    const val=e.target.value;
    const mainArea=document.getElementById("m-area")?.value;
    if(val&&val!==mainArea&&!extraAreaIds.includes(val)){extraAreaIds.push(val);refreshExtraAreaChips();}
    e.target.value="";
  });

  if(isCreator){
    document.getElementById("m-resp-add")?.addEventListener("click",()=>{
      const sel=document.getElementById("m-resp-sel")?.value;
      const manual=document.getElementById("m-resp-manual")?.value.trim();
      const name=manual||sel;
      if(name&&!selResps.includes(name)){selResps.push(name);refreshRespChips();}
      if(document.getElementById("m-resp-manual"))document.getElementById("m-resp-manual").value="";
      if(document.getElementById("m-resp-sel"))document.getElementById("m-resp-sel").value="";
    });
    document.getElementById("m-resp-manual")?.addEventListener("keydown",e=>{if(e.key==="Enter"){e.preventDefault();document.getElementById("m-resp-add").click();}});
    document.getElementById("m-resp-all")?.addEventListener("click",()=>{
      const areaId=document.getElementById("m-area")?.value;
      const area=areas[areaId];
      if(!area){toast("Selecione uma área primeiro","error");return;}
      const members=Array.isArray(area.members)?area.members:(typeof area.members==="object"&&area.members?Object.values(area.members):[]);
      // Adiciona todos os usuários que são membros da área
      const areaUsers=Object.values(users).filter(u=>u.name&&members.includes(u.name));
      if(!areaUsers.length){
        // fallback: usuários com permissão na área
        const permUsers=Object.values(users).filter(u=>u.name&&(u.role==="admin1"||(u.permissions||[]).includes(areaId)));
        permUsers.forEach(u=>{if(!selResps.includes(u.name))selResps.push(u.name);});
      } else {
        areaUsers.forEach(u=>{if(!selResps.includes(u.name))selResps.push(u.name);});
      }
      refreshRespChips();
      toast("Membros da área adicionados — remova quem não deve receber","success");
    });
    document.getElementById("m-resp-org")?.addEventListener("click",()=>{
      // All users including admin1 — full org broadcast
      const allNames=Object.values(users).filter(u=>u.name).map(u=>u.name);
      selResps=[];
      allNames.forEach(name=>selResps.push(name));
      refreshRespChips();
      toast("Toda a organização adicionada — remova quem não deve receber","success");
    });
  }
  document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;

  // Toggle recorrência
  document.getElementById("m-recur-on")?.addEventListener("change",e=>{
    document.getElementById("m-recur-fields").style.display=e.target.checked?"flex":"none";
  });
  document.getElementById("m-recur-freq")?.addEventListener("change",e=>{
    document.getElementById("m-recur-custom-wrap").style.display=e.target.value==="custom"?"block":"none";
  });

  document.getElementById("m-save").onclick=async()=>{
    const title=document.getElementById("m-title").value.trim();
    if(!title){toast("Digite um t\u00edtulo","error");return;}
    const isEdit=!!init.id;
    const respsToSave=isCreator?selResps:(init.resps||[]);
    const recurOn=document.getElementById("m-recur-on")?.checked||false;
    const recurrence=recurOn?{
      freq:document.getElementById("m-recur-freq")?.value||"semanal",
      interval:parseInt(document.getElementById("m-recur-interval")?.value||"7"),
      cond:document.getElementById("m-recur-cond")?.value||"after_complete"
    }:null;
    const data={
      id:init.id||uid(),title,
      desc:document.getElementById("m-desc").value.trim(),
      areaId:document.getElementById("m-area").value,
      resps:respsToSave,
      status:document.getElementById("m-status").value,
      priority:document.getElementById("m-priority").value,
      date:document.getElementById("m-date").value,
      pinned:init.pinned||false,
      allUsers:document.getElementById("m-allusers")?.checked||false,
      extraAreaIds:extraAreaIds.length?extraAreaIds:null,
      recurrence:recurrence||null,
      creatorId:init.creatorId||currentUser.uid,
      creatorName:init.creatorName||currentProfile.name,
      createdAt:init.createdAt||new Date().toISOString()
    };
    await dbSet(`tasks/${data.id}`,data);
    await logAction(isEdit?"editar_tarefa":"criar_tarefa",`${isEdit?"Editada":"Criada"} por ${currentProfile.name}: ${title}`);
    toast(isEdit?"Atualizada!":"Tarefa criada!","success");closeModal();
  };
  overlayClose("ov");
  setTimeout(()=>document.getElementById("m-title")?.focus(),80);
}

// ── ABA MEMBROS DA ÁREA ───────────────────────────────────────────────────────
function renderAreaMembersTab(task){
  const container=document.getElementById("area-members-list"); if(!container)return;
  container.innerHTML="";
  const taskAreaIds=[
    ...(task.areaId?[task.areaId]:[]),
    ...(Array.isArray(task.extraAreaIds)?task.extraAreaIds:[])
  ];

  if(!taskAreaIds.length){
    container.innerHTML='<p style="color:#7a7a8a;padding:8px 0;font-size:13px">Nenhuma área associada a esta tarefa.</p>';
    return;
  }

  // Coleta membros: usuários que têm pelo menos uma das áreas nas suas permissões
  const memberUids=new Set();
  Object.entries(users).forEach(([uid2,u])=>{
    // Admins sempre aparecem
    if(u.role==="admin1"||u.role==="admin"){memberUids.add(uid2);return;}
    // Usuário comum: aparece se tiver qualquer área da tarefa nas permissões
    const perms=u.permissions||[];
    if(taskAreaIds.some(aid=>perms.includes(aid))) memberUids.add(uid2);
  });

  if(!memberUids.size){
    container.innerHTML='<p style="color:#7a7a8a;padding:8px 0;font-size:13px">Nenhum membro com acesso a estas áreas ainda.<br><span style="font-size:11px;color:#5a5a6a">Configure as permissões na aba Administração.</span></p>';
    return;
  }

  const assigneeNames=new Set(Array.isArray(task.resps)?task.resps:(task.resp?[task.resp]:[]));
  const COLORS=["#c8f04e","#4ec8f0","#f04ec8","#f0c84e","#4ef0c8","#c84ef0","#f04e4e","#4e4ef0"];
  function avatarColor(uid2){let h=0;for(let i=0;i<uid2.length;i++)h=uid2.charCodeAt(i)+((h<<5)-h);return COLORS[Math.abs(h)%COLORS.length];}

  // Ordena: responsáveis atribuídos primeiro
  const sorted=[...memberUids].sort((a,b)=>{
    const ua=users[a],ub=users[b];
    const aA=assigneeNames.has(ua?.name)?0:1, bB=assigneeNames.has(ub?.name)?0:1;
    return aA-bB;
  });

  sorted.forEach(uid2=>{
    const u=users[uid2]; if(!u)return;
    const name=u.name||u.email||uid2;
    const init2=name.split(" ").map(p=>p[0]).join("").toUpperCase().slice(0,2);
    const color=u.color||avatarColor(uid2);
    const isAss=assigneeNames.has(name);
    const roleLabel={admin1:"👑 Super Admin",admin:"Admin",user:"Membro"}[u.role]||"Membro";
    const card=document.createElement("div");
    card.className="member-card"+(isAss?" is-assignee":"");
    card.innerHTML=`<div class="member-avatar-sm" style="background:${color}">${init2}</div>
      <div class="member-info">
        <span class="member-name">${esc(name)}</span>
        <span class="member-role-badge">${roleLabel}</span>
      </div>`;
    container.appendChild(card);
  });
}

function openDetailModal(taskId){
  const t={id:taskId,...tasks[taskId]};if(!t.title)return;
  const area=areas[t.areaId],st=STATUS[t.status];
  const resps=Array.isArray(t.resps)?t.resps:(t.resp?[t.resp]:[]);
  const canPin=isAdmin();
  const canDelete=isAdmin()||(t.creatorId===currentUser?.uid);
  const priorityChip=t.priority?'<span class="chip" style="background:'+PRIORITY[t.priority].color+'18;color:'+PRIORITY[t.priority].color+';border:1px solid '+PRIORITY[t.priority].color+'30;padding:4px 12px;text-transform:capitalize">'+t.priority+'</span>':"";
  const areaChip=(area?'<span class="chip" style="background:'+area.color+'18;color:'+area.color+';border:1px solid '+area.color+'30;padding:4px 12px">'+esc(area.name)+'</span>':"")
    +(Array.isArray(t.extraAreaIds)?t.extraAreaIds.map(eid=>{const ea=areas[eid];return ea?'<span class="chip" style="background:'+ea.color+'18;color:'+ea.color+';border:1px solid '+ea.color+'30;padding:4px 12px">'+esc(ea.name)+'</span>':"";}).join(""):"");
  const descBlock=t.desc?'<div style="font-size:13px;color:#a0a0b0;line-height:1.6;background:#18181c;padding:12px;border-radius:8px;margin-bottom:14px">'+esc(t.desc)+'</div>':"";
  function personAvatar(name, color, role=""){
    const u=Object.values(users).find(u=>u.name===name);
    const c=u?.color||color||"#7c6eff";
    return`<div style="display:flex;align-items:center;gap:8px;padding:6px 10px;background:${c}12;border:1px solid ${c}33;border-radius:10px">
      <div style="width:32px;height:32px;border-radius:50%;background:${c};display:flex;align-items:center;justify-content:center;font-size:12px;font-weight:700;color:#0c0c0f;flex-shrink:0">${initials(name)}</div>
      <div><div style="font-size:13px;font-weight:600;color:#f0eff5">${esc(name)}</div>${role?`<div style="font-size:10px;color:${c};margin-top:1px">${esc(role)}</div>`:""}</div>
    </div>`;
  }
  const respBlock=resps.length?`<div style="margin-bottom:14px">
    <div style="font-size:10px;color:#7a7a8a;text-transform:uppercase;letter-spacing:1px;margin-bottom:8px">&#128100; Responsáveis (${resps.length})</div>
    <div style="display:flex;gap:8px;flex-wrap:wrap">${resps.map(r=>personAvatar(r,"#7c6eff","Responsável")).join("")}</div>
  </div>`:"";
  const dateBlock=t.date?'<div><div style="font-size:10px;color:#7a7a8a;text-transform:uppercase;letter-spacing:1px;margin-bottom:3px">Prazo</div><div>'+fmtDate(t.date)+'</div></div>':"";
  const creatorBlock=t.creatorName?`<div style="margin-top:12px;padding-top:12px;border-top:1px solid #1e1e28">
    <div style="font-size:10px;color:#7a7a8a;text-transform:uppercase;letter-spacing:1px;margin-bottom:8px">✏ Criada por</div>
    <div style="display:flex;gap:8px;flex-wrap:wrap">${personAvatar(t.creatorName,"#4ac8e8","Criador(a)")}</div>
  </div>`:"";
  const statusBtns=Object.entries(STATUS).map(([k,v])=>{
    const sel=t.status===k;
    const s=sel?'background:'+v.color+'22;color:'+v.color+';border:1px solid '+v.color+'60':'border:1px solid #2e2e3a;color:#7a7a8a';
    return'<button class="btn-small move-status" data-status="'+k+'" style="'+s+'">'+v.label+'</button>';
  }).join("");
  const pinLabel=t.pinned?'Fixada (desfixar)':'Fixar tarefa';
  const delAttrs=t.pinned?'disabled title="Desfixe antes de excluir"':"";
  const delLabel=t.pinned?'Fixada':'Excluir';
  const pinTitlePrefix=t.pinned?'[Fixada] ':'';
  const collectiveBlock=(t.allUsers||resps.length>1)&&resps.length?`<div style="margin-bottom:14px;background:#1a1a22;border:1px solid #2e2e3a;border-radius:8px;padding:10px 14px">
    <div style="font-size:10px;color:#7a7a8a;text-transform:uppercase;letter-spacing:1px;margin-bottom:8px">⚙ ${t.allUsers?"Tarefa coletiva":"Progresso individual"} — conclusões</div>
    ${Object.entries(users).filter(([,u])=>resps.includes(u.name)).map(([uid2,u])=>{
      const done=!!(t.completions||{})[uid2];
      return`<div style="display:flex;align-items:center;gap:8px;margin-bottom:4px">
        <span style="width:14px;height:14px;border-radius:50%;background:${done?"#c8f04e":"#1e1e28"};border:2px solid ${done?"#c8f04e":"#3e3e4a"};flex-shrink:0"></span>
        <span style="font-size:12px;color:${done?"#c8f04e":"#a0a0b0"}">${esc(u.name)}${done?" ✓":""}</span>
      </div>`;}).join("")}
  </div>`:"";  const pinBtn=canPin?'<button id="m-pin" class="btn-small" style="border:1px solid '+(t.pinned?'#c8f04e':'#2e2e3a')+';color:'+(t.pinned?'#c8f04e':'#7a7a8a')+'">'+pinLabel+'</button>':"";
  openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:860px;width:95vw">
    <div class="modal-header">
      <div class="modal-title">${pinTitlePrefix}Detalhe</div>
      <button class="icon-btn" id="m-x">✕</button>
    </div>
    <div style="display:flex;gap:0;min-height:400px">
      <div class="modal-body" style="flex:1;min-width:0;border-right:1px solid #1e1e28;padding-right:20px;display:block;overflow-y:auto">
        <div class="modal-tabs">
          <button class="modal-tab-btn active" id="dtab-detail">📋 Detalhes</button>
          <button class="modal-tab-btn" id="dtab-members">👥 Membros</button>
        </div>
        <div id="dtab-panel-detail">
        <div style="font-family:'Syne',sans-serif;font-size:18px;font-weight:700;line-height:1.3;margin-bottom:10px">${esc(t.title)}</div>
        <div style="display:flex;gap:8px;flex-wrap:wrap;margin-bottom:14px">
          <span class="chip" style="background:${st.color}22;color:${st.color};border:1px solid ${st.color}40;padding:4px 12px">${st.label}</span>
          ${priorityChip}${areaChip}${deadlineBadge(t.date)}
        </div>
        ${collectiveBlock}${descBlock}${respBlock}
        <div style="display:grid;grid-template-columns:1fr 1fr;gap:12px;margin-bottom:16px">${dateBlock}</div>
        <div>
          <div style="font-size:10px;color:#7a7a8a;text-transform:uppercase;letter-spacing:1px;margin-bottom:8px">Mover para</div>
          <div style="display:flex;gap:6px;flex-wrap:wrap">${statusBtns}</div>
        </div>
        ${creatorBlock}
        <div style="margin-top:14px;padding-top:12px;border-top:1px solid #1a1a22">
          <button id="m-send-alert" class="btn-small" style="border:1px solid #f0a83244;color:#f0a832;font-size:12px">🔔 Enviar alerta aos responsáveis</button>
        </div>
        </div>
        <div id="dtab-panel-members" style="display:none">
          <div class="members-grid" id="area-members-list"></div>
        </div>
      </div>
      <div style="width:280px;min-width:240px;display:flex;flex-direction:column;padding-left:18px">
        <div style="font-size:11px;color:#7a7a8a;text-transform:uppercase;letter-spacing:1px;margin-bottom:10px;padding-top:18px">💬 Comentários</div>
        <div id="comments-list" style="flex:1;overflow-y:auto;max-height:340px;display:flex;flex-direction:column;gap:8px;margin-bottom:10px">
          <div style="font-size:12px;color:#3a3a4a;text-align:center;padding:20px 0">Carregando…</div>
        </div>
        <div style="border-top:1px solid #1e1e28;padding-top:10px">
          <textarea id="comment-input" placeholder="Escrever comentário…" rows="2" style="width:100%;box-sizing:border-box;background:#13131a;border:1px solid #1e1e28;border-radius:7px;padding:8px 10px;color:#d0d0e0;font-family:'DM Sans',sans-serif;font-size:12px;outline:none;resize:none;transition:border-color .15s"></textarea>
          <button id="comment-submit" class="btn-primary" style="width:100%;margin-top:6px;font-size:12px;padding:7px">Comentar</button>
        </div>
      </div>
    </div>
    <div class="modal-footer">
      ${pinBtn}
      ${canDelete?`<button class="btn-danger" id="m-del" ${delAttrs}>${delLabel}</button>`:""}
      <button class="btn-ghost" id="m-x2">Fechar</button>
      <button class="btn-primary" id="m-edit">Editar</button>
    </div>
  </div></div>`);
  document.getElementById("m-edit").onclick=()=>{closeModal();openTaskModal({...t});};

  // ── Handlers das abas Detalhes / Membros ──
  document.getElementById("dtab-detail")?.addEventListener("click",()=>{
    document.getElementById("dtab-panel-detail").style.display="";
    document.getElementById("dtab-panel-members").style.display="none";
    document.getElementById("dtab-detail").classList.add("active");
    document.getElementById("dtab-members").classList.remove("active");
  });
  document.getElementById("dtab-members")?.addEventListener("click",()=>{
    document.getElementById("dtab-panel-detail").style.display="none";
    document.getElementById("dtab-panel-members").style.display="";
    document.getElementById("dtab-members").classList.add("active");
    document.getElementById("dtab-detail").classList.remove("active");
    renderAreaMembersTab(t);
  });

  // ── Comments — real-time listener ──
  const commentsPath=`task_comments/${taskId}`;
  let commentsUnsub=null;
  function renderComments(commentsObj){
    const el=document.getElementById("comments-list"); if(!el)return;
    const list=Object.entries(commentsObj||{}).map(([id,c])=>({id,...c})).sort((a,b)=>new Date(a.ts)-new Date(b.ts));
    if(!list.length){el.innerHTML='<div style="font-size:12px;color:#3a3a4a;text-align:center;padding:20px 0">Sem comentários ainda.</div>';return;}
    el.innerHTML=list.map(c=>{
      const isMe=c.authorId===currentUser?.uid;
      const canDel=isMe||isAdmin();
      const uColor=Object.values(users).find(u=>u.name===c.authorName)?.color||"#7c6eff";
      return`<div style="background:#13131a;border:1px solid #1e1e28;border-radius:8px;padding:8px 10px;position:relative" data-cid="${c.id}">
        <div style="display:flex;align-items:center;gap:6px;margin-bottom:4px">
          <div style="width:20px;height:20px;border-radius:50%;background:${uColor};display:flex;align-items:center;justify-content:center;font-size:9px;font-weight:700;color:#13131a;flex-shrink:0">${initials(c.authorName)}</div>
          <span style="font-size:11px;font-weight:600;color:#d0d0e0">${esc(c.authorName||"?")}</span>
          <span style="font-size:10px;color:#4a4a5a;margin-left:auto">${fmtTs(c.ts)}</span>
          ${canDel?`<button class="btn-del-comment" data-cid="${c.id}" style="background:none;border:none;color:#ff6b6b;cursor:pointer;font-size:11px;padding:0 2px;opacity:0.5">✕</button>`:""}
        </div>
        <div style="font-size:12px;color:#a0a0b0;line-height:1.5;word-break:break-word">${linkify(c.text||"")}</div>
      </div>`;
    }).join("");
    // wire delete buttons
    el.querySelectorAll(".btn-del-comment").forEach(btn=>{
      btn.addEventListener("click",async()=>{
        if(!confirm("Excluir comentário?"))return;
        await dbRemove(`${commentsPath}/${btn.dataset.cid}`);
      });
    });
    // auto scroll to bottom
    el.scrollTop=el.scrollHeight;
  }
  // Start listener
  commentsUnsub=onValue(dbRef(commentsPath),snap=>renderComments(snap.val()||{}));
  // Clean up listener when modal closes
  const origCloseModal=window._origCloseForComments;
  const _closeAndUnsub=()=>{if(commentsUnsub){commentsUnsub();commentsUnsub=null;}closeModal();};

  // Submit comment
  const commentInput=document.getElementById("comment-input");
  commentInput?.addEventListener("focus",e=>{e.target.style.borderColor="#c8f04e44";});
  commentInput?.addEventListener("blur",e=>{e.target.style.borderColor="#1e1e28";});
  commentInput?.addEventListener("keydown",e=>{if(e.key==="Enter"&&!e.shiftKey){e.preventDefault();document.getElementById("comment-submit")?.click();}});
  document.getElementById("comment-submit")?.addEventListener("click",async()=>{
    const text=commentInput?.value.trim(); if(!text)return;
    const cid=uid();
    await dbSet(`${commentsPath}/${cid}`,{
      id:cid, text, authorId:currentUser.uid, authorName:currentProfile.name,
      ts:new Date().toISOString()
    });
    if(commentInput)commentInput.value="";
    await logAction("comentar_tarefa",`Comentou em: ${t.title}`);
    // Notificar responsáveis + criador + membros da área (exceto quem comentou)
    const toNotify=new Set();
    // Responsáveis
    Object.entries(users).filter(([,u])=>resps.includes(u.name)&&u.name!==currentProfile.name).forEach(([uid2])=>toNotify.add(uid2));
    // Criador
    if(t.creatorId&&t.creatorId!==currentUser.uid) toNotify.add(t.creatorId);
    // Membros das áreas da tarefa (areaId principal + extraAreaIds)
    const taskAreaIds=[t.areaId,...(Array.isArray(t.extraAreaIds)?t.extraAreaIds:[])].filter(Boolean);
    taskAreaIds.forEach(aId=>{
      const area=areas[aId]; if(!area)return;
      // Membros = usuários com permissão nessa área
      Object.entries(users).forEach(([uid2,u])=>{
        if(uid2===currentUser.uid)return;
        const hasPerm=u.role==="admin1"||u.role==="admin"||(u.permissions||[]).includes(aId);
        if(hasPerm) toNotify.add(uid2);
      });
    });
    for(const uid2 of toNotify){
      await dbSet(`user_notifs/${uid2}/${uid()}`,{
        type:"new_comment", msg:`💬 ${currentProfile.name} comentou em "${t.title}"`,
        taskId, ts:new Date().toISOString(), read:false
      });
    }
  });

  // Manual alert button
  document.getElementById("m-send-alert")?.addEventListener("click",async()=>{
    if(!resps.length){toast("Tarefa sem responsáveis","error");return;}
    const msg=prompt("Mensagem do alerta (opcional):")||`🔔 Atenção: ${t.title}`;
    const respUsers=Object.entries(users).filter(([,u])=>resps.includes(u.name));
    for(const [uid2] of respUsers){
      await dbSet(`user_notifs/${uid2}/${uid()}`,{
        type:"manual_alert", msg, taskId, ts:new Date().toISOString(), read:false
      });
    }
    await logAction("alerta_manual",`Alerta enviado para ${resps.join(", ")}: ${t.title}`);
    toast(`Alerta enviado para ${resps.length} responsável(is)`,"success");
  });

  // Override close buttons to also unsub
  document.getElementById("m-x").onclick=document.getElementById("m-x2").onclick=_closeAndUnsub;

  document.getElementById("m-pin")?.addEventListener("click",async()=>{
    await dbSet(`tasks/${taskId}/pinned`,!t.pinned);
    await logAction(t.pinned?"desfixar_tarefa":"fixar_tarefa",(t.pinned?"Desfixada":"Fixada")+": "+t.title);
    toast(t.pinned?"Tarefa desfixada":"Tarefa fixada","success");closeModal();
  });
  document.getElementById("m-del")?.addEventListener("click",async()=>{
    if(t.pinned){toast("Desfixe a tarefa antes de excluir","error");return;}
    if(!canDelete){toast("Apenas o criador ou admin pode excluir","error");return;}
    if(confirm("Excluir tarefa?")){await dbRemove(`tasks/${taskId}`);await logAction("excluir_tarefa","Excluida: "+t.title);closeModal();toast("Tarefa excluida","warning");}
  });
  document.querySelectorAll(".move-status").forEach(b=>b.addEventListener("click",async()=>{
    // Conclusão individual: ativa para allUsers OU para qualquer tarefa com 2+ responsáveis
    const isMultiResp=resps.length>1;
    const isResponsavel=resps.includes(currentProfile.name);
    if((t.allUsers||isMultiResp)&&isResponsavel){
      // Ao clicar em Concluído, registra apenas a conclusão deste usuário
      if(b.dataset.status==="concluido"){
        closeModal();
        await markUserCompletion(taskId);
        return;
      }
    }
    const newStatus=b.dataset.status;
    await dbSet(`tasks/${taskId}/status`,newStatus);
    await logAction("editar_tarefa","Status: "+STATUS[newStatus].label+": "+t.title);
    // Notify admin1 when any user marks task complete
    if(newStatus==="concluido"&&!isAdmin1){
      const admin1Id=Object.entries(users).find(([,u])=>u.role==="admin1")?.[0];
      if(admin1Id){
        const notifKey=currentUser.uid+Date.now().toString(36);
        await dbSet(`user_notifs/${admin1Id}/${notifKey}`,{
          type:"task_completed",
          msg:`✅ ${currentProfile.name} concluiu: "${t.title}"`,
          taskId,ts:new Date().toISOString(),read:false
        });
      }
    }
    closeModal();
    toast("Status atualizado","success");
    if(newStatus==="concluido") openRepeatTaskModal(t);
  }));
  overlayClose("ov");
}


function openNoteModal(noteId,personal){
  if(!noteId&&!personal&&Object.keys(notes).length>=LIMITS.MAX_NOTES){toast(`Limite de ${LIMITS.MAX_NOTES} notas atingido`,"error");return;}
  if(!noteId&&personal&&Object.keys(personalNotes).length>=LIMITS.MAX_PERSONAL_NOTES){toast(`Limite de ${LIMITS.MAX_PERSONAL_NOTES} rascunhos atingido`,"error");return;}
  const n=noteId?(personal?{id:noteId,...personalNotes[noteId]}:{id:noteId,...notes[noteId]}):{};
  openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:560px"><div class="modal-header"><div class="modal-title">${noteId?"Editar":"Nova"} ${personal?"Nota Pessoal":"Nota"}</div><button class="icon-btn" id="m-x">✕</button></div><div class="modal-body"><div class="field"><label>Título *</label><input id="m-nt" value="${esc(n.title||"")}" placeholder="Título…" autofocus/></div><div class="field-row"><div class="field"><label>Tag</label><input id="m-ntag" value="${esc(n.tag||"")}" placeholder="Ex: Referência…"/></div><div class="field"><label>Cor</label><div style="display:flex;gap:6px;align-items:center;padding-top:4px">${NOTE_COLORS.map(c=>`<div class="note-color-pick" data-color="${c}" style="width:22px;height:22px;border-radius:5px;background:${c};cursor:pointer;outline:${(n.color||NOTE_COLORS[0])===c?`2px solid ${c}`:"none"}"></div>`).join("")}</div></div></div><div class="field"><label>Anotação</label><textarea id="m-nb" rows="5" placeholder="Texto livre…">${esc(n.body||"")}</textarea></div><div class="field"><label style="display:flex;align-items:center;justify-content:space-between">Imagens <span style="font-size:10px;color:#7a7a8a;font-weight:400">Cole (Ctrl+V) ou arraste</span></label><div id="img-drop-zone" style="border:1px dashed #2e2e3a;border-radius:8px;padding:12px;min-height:60px;position:relative"><div id="img-paste-hint" style="font-size:12px;color:#4a4a5a;text-align:center;padding:8px 0">📋 Cole uma imagem aqui (Ctrl+V)</div><div id="img-preview-list" style="display:flex;flex-wrap:wrap;gap:8px"></div></div></div></div><div class="modal-footer"><button class="btn-ghost" id="m-cancel">Cancelar</button><button class="btn-primary" id="m-save">Salvar</button></div></div></div>`);
  let col=n.color||NOTE_COLORS[0];
  document.querySelectorAll(".note-color-pick").forEach(el=>{el.addEventListener("click",()=>{col=el.dataset.color;document.querySelectorAll(".note-color-pick").forEach(e=>e.style.outline="none");el.style.outline=`2px solid ${col}`;});});
  document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;
  // Image paste for personal notes
  let pNoteImages=[...(n.images||[])];
  function renderPImgs(){const list=document.getElementById("img-preview-list");const hint=document.getElementById("img-paste-hint");if(!list)return;hint&&(hint.style.display=pNoteImages.length?"none":"");list.innerHTML=pNoteImages.map((img,i)=>`<div style="position:relative"><img src="${img.data}" style="max-width:${img.w||120}px;max-height:100px;border-radius:5px;border:1px solid #2e2e3a"/><button onclick="pNoteImages.splice(${i},1);renderPImgs()" style="position:absolute;top:-6px;right:-6px;width:18px;height:18px;border-radius:50%;background:#ff6b6b;border:none;color:#fff;cursor:pointer;font-size:11px;padding:0">✕</button></div>`).join("");}
  window.pNoteImages=pNoteImages;window.renderPImgs=renderPImgs;renderPImgs();
  function handlePImgFile(file){if(!file||!file.type.startsWith("image/"))return;const reader=new FileReader();reader.onload=ev=>{const img2=new Image();img2.onload=()=>{const maxW=800,sc=Math.min(1,maxW/img2.width);const cv=document.createElement("canvas");cv.width=Math.round(img2.width*sc);cv.height=Math.round(img2.height*sc);cv.getContext("2d").drawImage(img2,0,0,cv.width,cv.height);pNoteImages.push({data:cv.toDataURL("image/webp",0.82),w:Math.min(cv.width,300)});renderPImgs();};img2.src=ev.target.result;};reader.readAsDataURL(file);}
  document.addEventListener("paste",function onPasteP(e){if(!document.getElementById("img-drop-zone"))return document.removeEventListener("paste",onPasteP);[...(e.clipboardData?.items||[])].forEach(it=>{if(it.type.startsWith("image/"))handlePImgFile(it.getAsFile());});});
  const dzP=document.getElementById("img-drop-zone");dzP?.addEventListener("dragover",e=>{e.preventDefault();dzP.style.borderColor="#c8f04e";});dzP?.addEventListener("dragleave",()=>{dzP.style.borderColor="#2e2e3a";});dzP?.addEventListener("drop",e=>{e.preventDefault();dzP.style.borderColor="#2e2e3a";[...(e.dataTransfer.files||[])].forEach(handlePImgFile);});
  document.getElementById("m-save").onclick=async()=>{const title=document.getElementById("m-nt").value.trim();if(!title){toast("Digite um título","error");return;}const data={id:n.id||uid(),title,tag:document.getElementById("m-ntag").value.trim(),body:document.getElementById("m-nb").value.trim(),color:col,links:[],images:pNoteImages,createdAt:n.createdAt||new Date().toISOString()};if(personal)await dbSet(`personal_notes/${currentUser.uid}/${data.id}`,data);else{await dbSet(`notes/${data.id}`,{...data,authorId:currentUser.uid});await logAction("criar_nota",`Nota: ${title}`);}toast(noteId?"Nota atualizada!":"Nota salva!","success");closeModal();};
  overlayClose("ov");
}

function openAreaNoteModal(noteId){
  const existing=areaNotes[activeAreaId]||{};
  if(!noteId&&Object.keys(existing).length>=LIMITS.MAX_AREA_NOTES){toast(`Limite de ${LIMITS.MAX_AREA_NOTES} notas atingido`,"error");return;}
  const n=noteId?{id:noteId,...existing[noteId]}:{};
  const area=areas[activeAreaId];
  openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:580px"><div class="modal-header"><div class="modal-title">${noteId?"Editar":"Nova"} Nota — ${esc(area?.name||"")}</div><button class="icon-btn" id="m-x">✕</button></div><div class="modal-body"><div class="field"><label>Título *</label><input id="m-nt" value="${esc(n.title||"")}" placeholder="Título da nota…" autofocus/></div><div class="field-row"><div class="field"><label>Tag</label><input id="m-ntag" value="${esc(n.tag||"")}" placeholder="Ex: Referência, Contato…"/></div><div class="field"><label>Cor</label><div style="display:flex;gap:6px;align-items:center;padding-top:4px">${NOTE_COLORS.map(c=>`<div class="note-color-pick" data-color="${c}" style="width:22px;height:22px;border-radius:5px;background:${c};cursor:pointer;outline:${(n.color||NOTE_COLORS[0])===c?`2px solid ${c}`:"none"}"></div>`).join("")}</div></div></div><div class="field"><label>Anotação</label><textarea id="m-nb" rows="5" placeholder="Texto livre…">${esc(n.body||"")}</textarea></div><div class="field"><label style="display:flex;align-items:center;justify-content:space-between">Imagens <span style="font-size:10px;color:#7a7a8a;font-weight:400">Cole (Ctrl+V) ou arraste uma imagem</span></label><div id="img-drop-zone" style="border:1px dashed #2e2e3a;border-radius:8px;padding:12px;min-height:60px;position:relative;transition:border-color .2s"><div id="img-paste-hint" style="font-size:12px;color:#4a4a5a;text-align:center;padding:8px 0">📋 Cole uma imagem aqui (Ctrl+V)</div><div id="img-preview-list" style="display:flex;flex-wrap:wrap;gap:8px"></div></div></div></div><div class="modal-footer"><button class="btn-ghost" id="m-cancel">Cancelar</button><button class="btn-primary" id="m-save">Salvar</button></div></div></div>`);
  let col=n.color||NOTE_COLORS[0];
  document.querySelectorAll(".note-color-pick").forEach(el=>{el.addEventListener("click",()=>{col=el.dataset.color;document.querySelectorAll(".note-color-pick").forEach(e=>e.style.outline="none");el.style.outline=`2px solid ${col}`;});});
  document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;
  // Image paste/drop handling
  let noteImages=[...(n.images||[])];
  function renderImgPreviews(){
    const list=document.getElementById("img-preview-list");
    const hint=document.getElementById("img-paste-hint");
    if(!list)return;
    if(noteImages.length){hint&&(hint.style.display="none");}else{hint&&(hint.style.display="");}
    list.innerHTML=noteImages.map((img,i)=>`<div style="position:relative;display:inline-block">
      <img src="${img.data}" style="max-width:${img.w||120}px;max-height:120px;border-radius:6px;display:block;border:1px solid #2e2e3a"/>
      <button onclick="noteImages.splice(${i},1);renderImgPreviews()" style="position:absolute;top:-6px;right:-6px;width:18px;height:18px;border-radius:50%;background:#ff6b6b;border:none;color:#fff;cursor:pointer;font-size:11px;line-height:1;padding:0">✕</button>
    </div>`).join("");
  }
  renderImgPreviews();
  function handleImageFile(file){
    if(!file||!file.type.startsWith("image/"))return;
    const reader=new FileReader();
    reader.onload=e=>{
      // Resize to max 800px
      const img2=new Image();
      img2.onload=()=>{
        const maxW=800,sc=Math.min(1,maxW/img2.width);
        const cv=document.createElement("canvas");
        cv.width=Math.round(img2.width*sc);cv.height=Math.round(img2.height*sc);
        cv.getContext("2d").drawImage(img2,0,0,cv.width,cv.height);
        noteImages.push({data:cv.toDataURL("image/webp",0.82),w:Math.min(cv.width,300)});
        renderImgPreviews();
      };
      img2.src=e.target.result;
    };
    reader.readAsDataURL(file);
  }
  document.addEventListener("paste",function onPaste(e){
    if(!document.getElementById("img-drop-zone"))return document.removeEventListener("paste",onPaste);
    const items=[...(e.clipboardData?.items||[])];
    items.forEach(it=>{if(it.type.startsWith("image/"))handleImageFile(it.getAsFile());});
  });
  const dz=document.getElementById("img-drop-zone");
  dz?.addEventListener("dragover",e=>{e.preventDefault();dz.style.borderColor="#c8f04e";});
  dz?.addEventListener("dragleave",()=>{dz.style.borderColor="#2e2e3a";});
  dz?.addEventListener("drop",e=>{e.preventDefault();dz.style.borderColor="#2e2e3a";[...(e.dataTransfer.files||[])].forEach(handleImageFile);});
  document.getElementById("m-save").onclick=async()=>{
    const title=document.getElementById("m-nt").value.trim();if(!title){toast("Digite um título","error");return;}
    const data={id:n.id||uid(),title,tag:document.getElementById("m-ntag").value.trim(),body:document.getElementById("m-nb").value.trim(),color:col,links:[],images:noteImages,authorId:currentUser.uid,createdAt:n.createdAt||new Date().toISOString()};
    await dbSet(`area_notes/${activeAreaId}/${data.id}`,data);
    await logAction(noteId?"editar_nota":"criar_nota",`Nota "${title}" em: ${area?.name}`);
    toast(noteId?"Nota atualizada!":"Nota criada!","success");closeModal();
  };
  overlayClose("ov");
}

function openProfileModal(){
  openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:400px"><div class="modal-header"><div class="modal-title">Meu Perfil</div><button class="icon-btn" id="m-x">✕</button></div><div class="modal-body"><div class="field"><label>Nome</label><input id="m-pn" value="${esc(currentProfile.name||"")}"/></div><div style="font-size:12px;color:#7a7a8a">E-mail: ${esc(currentProfile.email)}</div><div style="font-size:12px;color:#7a7a8a">Função: ${{"admin1":"👑 Super Admin","admin":"Administrador","user":"Usuário"}[currentProfile.role]||currentProfile.role}</div></div><div class="modal-footer"><button class="btn-ghost" id="m-cancel">Cancelar</button><button class="btn-primary" id="m-save">Salvar</button></div></div></div>`);
  document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;
  document.getElementById("m-save").onclick=async()=>{const name=document.getElementById("m-pn").value.trim();if(!name)return;await dbSet(`users/${currentUser.uid}/name`,name);currentProfile.name=name;toast("Perfil atualizado!","success");closeModal();render();};
  overlayClose("ov");
}


// ── SHARED TASK COMPLETION ────────────────────────────────────────────────────
// Tasks with allUsers=true require every user to mark complete individually
// Status auto-advances to "em-andamento" when first person marks it, "concluido" when all do
async function markUserCompletion(taskId){
  const t=tasks[taskId]; if(!t)return;
  const uid=currentUser.uid;
  const completions={...(t.completions||{}),[uid]:{name:currentProfile.name,ts:new Date().toISOString()}};
  const allUsers=Object.values(users).filter(u=>u.role!=="admin1"||u.id===currentUser.uid);
  const allDone=allUsers.every(u=>(t.resps||[]).length===0||!(t.resps||[]).includes(u.name)||completions[u.id]);
  // Check if the current task resps list aligns with completions
  const resps=Array.isArray(t.resps)?t.resps:(t.resp?[t.resp]:[]);
  // find all user IDs that match resps
  const respUserIds=Object.entries(users).filter(([,u])=>resps.includes(u.name)).map(([id])=>id);
  const allRespsDone=respUserIds.length===0||respUserIds.every(id=>completions[id]);
  const newStatus=allRespsDone?"concluido":"em-andamento";
  await dbSet(`tasks/${taskId}/completions`,completions);
  await dbSet(`tasks/${taskId}/status`,newStatus);
  // Notify admin1 that someone completed
  const admin1Id=Object.entries(users).find(([,u])=>u.role==="admin1")?.[0];
  if(admin1Id&&admin1Id!==uid){
    const notifKey=uid+Date.now().toString(36);
    await dbSet(`user_notifs/${admin1Id}/${notifKey}`,{
      type:"task_completed",
      msg:`✅ ${currentProfile.name} concluiu: "${t.title}"`,
      taskId,ts:new Date().toISOString(),read:false
    });
  }
  await logAction("concluir_tarefa",`${currentProfile.name} marcou como concluído: ${t.title}`);
  toast(allRespsDone?"Tarefa totalmente concluída! 🎉":"Sua parte foi marcada!","success");
  if(allRespsDone) openRepeatTaskModal(t);
}

// ── EXPORT TASKS ─────────────────────────────────────────────────────────────
function exportAreaTasks(areaId){
  const area=areas[areaId]; if(!area)return;
  const areaTaskList=Object.entries(tasks)
    .filter(([,t])=>t.areaId===areaId)
    .map(([id,t])=>({id,...t}))
    .sort((a,b)=>new Date(a.createdAt||0)-new Date(b.createdAt||0));
  if(!areaTaskList.length){toast("Nenhuma tarefa nesta área","error");return;}

  // Build plain text content
  const lines=[];
  lines.push(`TAREFAS — ${area.name.toUpperCase()}`);
  lines.push(`Exportado em: ${new Date().toLocaleString("pt-BR")}`);
  lines.push("=".repeat(60));
  lines.push("");
  areaTaskList.forEach((t,i)=>{
    const st=STATUS[t.status]?.label||t.status;
    const resps=Array.isArray(t.resps)?t.resps:(t.resp?[t.resp]:[]);
    lines.push(`${i+1}. ${t.title}`);
    lines.push(`   Status: ${st}`);
    if(t.priority) lines.push(`   Prioridade: ${PRIORITY[t.priority]?.label||t.priority}`);
    if(t.date) lines.push(`   Prazo: ${fmtDate(t.date)}`);
    if(resps.length) lines.push(`   Responsáveis: ${resps.join(", ")}`);
    if(t.creatorName) lines.push(`   Criado por: ${t.creatorName}`);
    if(t.desc) lines.push(`   Descrição: ${t.desc}`);
    lines.push("");
  });

  // Download as .txt (universal, opens in Word/any editor)
  const blob=new Blob([lines.join("\n")],{type:"text/plain;charset=utf-8"});
  const a=document.createElement("a");
  a.href=URL.createObjectURL(blob);
  a.download=`tarefas-${area.name.toLowerCase().replace(/\s+/g,"-")}.txt`;
  a.click(); URL.revokeObjectURL(a.href);
  toast("Exportado!","success");
}

// ── FULL BACKUP ───────────────────────────────────────────────────────────────
async function exportFullBackup(){
  if(!isAdmin1){toast("Apenas o Super Admin pode fazer backup","error");return;}
  toast("Gerando backup completo… aguarde","success");
  try{
    // Busca direta no Firebase para garantir dados completos
    const paths=["areas","tasks","notes","users","flow/nodes","flow/edges","flow/stickies",
      "org/nodes","org/edges","org/stickies","cal_events","freela_events","prosp_events",
      "fyi_notes","task_comments","personal_notes","area_notes","audit"];
    const results=await Promise.all(paths.map(p=>get(dbRef(p)).then(s=>s.val())));
    const [
      bAreas,bTasks,bNotes,bUsers,bFlowNodes,bFlowEdges,bFlowStickies,
      bOrgNodes,bOrgEdges,bOrgStickies,bCalEvents,bFreelaEvents,bProspEvents,
      bFyiNotes,bTaskComments,bPersonalNotes,bAreaNotes,bAudit
    ]=results;

    const backup={
      exportedAt:new Date().toISOString(),
      version:"v4-full",
      areas:bAreas||{},
      tasks:bTasks||{},
      notes:bNotes||{},
      users:Object.fromEntries(Object.entries(bUsers||{}).map(([id,u])=>[id,{...u}])),
      flowData:{nodes:bFlowNodes||{},edges:bFlowEdges||{},stickies:bFlowStickies||{}},
      orgData:{nodes:bOrgNodes||{},edges:bOrgEdges||{},stickies:bOrgStickies||{}},
      calEvents:bCalEvents||{},
      freelaEvents:bFreelaEvents||{},
      prospEvents:bProspEvents||{},
      fyiNotes:bFyiNotes||{},
      taskComments:bTaskComments||{},
      personalNotes:bPersonalNotes||{},
      areaNotes:bAreaNotes||{},
      auditLog:bAudit||{},
      _readme:{
        senhas:"Não exportadas — usuários precisam redefinir via Firebase Auth",
        authIds:"Os userId do backup correspondem aos UID do Firebase Auth",
        restauracao:"Importe cada chave no Firebase Realtime Database pelo console ou via script"
      }
    };
    const blob=new Blob([JSON.stringify(backup,null,2)],{type:"application/json"});
    const a=document.createElement("a");
    a.href=URL.createObjectURL(blob);
    a.download=`mineirart-backup-${new Date().toISOString().slice(0,10)}.json`;
    a.click(); URL.revokeObjectURL(a.href);
    await logAction("backup","Backup completo exportado");
    toast("✅ Backup completo baixado!","success");
  }catch(err){
    console.error("Backup error:",err);
    toast("Erro ao gerar backup: "+err.message,"error");
  }
}

// ── CONTEXT MENU FOR NOTES ────────────────────────────────────────────────────
let ctxMenu=null;
function showCtxMenu(x,y,items){
  removeCtxMenu();
  ctxMenu=document.createElement("div");
  ctxMenu.id="ctx-menu";
  ctxMenu.style.cssText=`position:fixed;top:${y}px;left:${x}px;background:#1a1a22;border:1px solid #2e2e3a;border-radius:8px;padding:4px;z-index:9999;min-width:180px;box-shadow:0 8px 24px rgba(0,0,0,.5);animation:slideIn .12s ease`;
  ctxMenu.innerHTML=items.map(it=>it==="---"
    ?`<div style="height:1px;background:#2e2e3a;margin:3px 0"></div>`
    :`<div class="ctx-item" data-action="${it.action}" style="padding:8px 14px;font-size:13px;cursor:pointer;border-radius:5px;color:#d0d0e0;transition:background .1s">${it.icon||""} ${it.label}</div>`
  ).join("");
  document.body.appendChild(ctxMenu);
  ctxMenu.querySelectorAll(".ctx-item").forEach(el=>{
    el.addEventListener("mouseenter",()=>el.style.background="#2a2a34");
    el.addEventListener("mouseleave",()=>el.style.background="");
    el.addEventListener("click",()=>{const act=el.dataset.action;removeCtxMenu();items.find(i=>i.action===act)?.fn?.();});
  });
  setTimeout(()=>document.addEventListener("click",removeCtxMenu,{once:true}),10);
}
function removeCtxMenu(){if(ctxMenu){ctxMenu.remove();ctxMenu=null;}}

// ── USER NOTIFICATIONS LISTENER ──────────────────────────────────────────────
let userNotifsUnread=0;
function listenUserNotifs(){
  if(!currentUser)return;
  let _shownBanners=new Set();
  onValue(dbRef(`user_notifs/${currentUser.uid}`),snap=>{
    const notifs=snap.val()||{};
    window._myNotifs=notifs;
    userNotifsUnread=Object.values(notifs).filter(n=>!n.read).length;
    // Mostra banner apenas uma vez por notificação nova, sem marcar como lida
    // (o usuário lê na aba Alertas e clica em Limpar para remover)
    Object.entries(notifs).filter(([nid,n])=>!n.read&&!_shownBanners.has(nid)).forEach(([nid,n])=>{
      _shownBanners.add(nid);
      showCalBanner(n.msg,"#c8f04e","Atualização");
    });
    render();
  });
}



// ── BLOCK NOTES EDITOR ────────────────────────────────────────────────────────
// Replaces the old note card system with an inline block editor per area
// Each "note" is now a doc with an array of blocks: {id, type:'text'|'toggle', text, done?, color?}

function renderAreaFYI(areaId){
  const aFyi=Object.values(fyiNotes).filter(n=>n.areaId===areaId).sort((a,b)=>(a.order||0)-(b.order||0));
  const color_=n=>n.color||"#c8f04e";
  const cards=aFyi.map(n=>`<div class="fyi-card area-fyi-card" data-fyi-open="${n.id}" draggable="true" data-fyi-id="${n.id}" data-area-id="${areaId}"
    style="background:${color_(n)}10;border:1.5px solid ${color_(n)}33;border-radius:10px;padding:12px 14px;margin-bottom:10px;cursor:pointer;position:relative">
    <div style="display:flex;align-items:flex-start;justify-content:space-between;gap:8px">
      <div style="font-size:14px;font-weight:700;color:${color_(n)}">${esc(n.title||"")}</div>
      <div style="display:flex;gap:6px;flex-shrink:0">
        ${n.authorId===currentUser?.uid||isAdmin1?`<button class="btn-area-fyi-edit" data-id="${n.id}" style="background:none;border:none;color:#7a7a8a;cursor:pointer;font-size:13px">✏</button><button class="btn-area-fyi-del" data-id="${n.id}" style="background:none;border:none;color:#ff6b6b;cursor:pointer;font-size:13px">✕</button>`:""}
      </div>
    </div>
    ${n.body?`<div style="font-size:13px;color:#a0a0b0;margin-top:6px;line-height:1.6;white-space:pre-wrap">${linkify(n.body)}</div>`:""}
    ${n.syncCal&&n.date?`<div style="margin-top:8px;font-size:11px;color:#7c6eff">📅 ${fmtDate(n.date)}</div>`:""}
  </div>`).join("");
  return`<div>
    <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:12px">
      <div style="font-size:12px;color:#5a5a6a">${aFyi.length} nota${aFyi.length!==1?"s":""} nesta área</div>
      <button class="btn-primary btn-add-area-fyi" data-area-id="${areaId}" style="font-size:12px;padding:6px 14px">+ Nova nota FYI</button>
    </div>
    <div id="area-fyi-list">${cards||'<div style="font-size:13px;color:#3a3a4a;padding:20px 0">Nenhuma nota FYI nesta área ainda.</div>'}</div>
  </div>`;
}

function renderAreaNotesEditor(areaId){
  // Find the block-doc (has a blocks array). Ignore legacy title/body notes.
  const allDocs=Object.values(areaNotes[areaId]||{});
  const areaDoc=allDocs.find(d=>Array.isArray(d.blocks))||null;
  const docId=areaDoc?.id||null;
  const blocks=areaDoc?.blocks||[];

  // Legacy notes (old format with title/body) — show as read-only info
  const legacyNotes=allDocs.filter(d=>!Array.isArray(d.blocks)&&d.title);

  function renderBlock(b){
    const color=b.color||"#d0d0e0";
    if(b.type==="image"){
      return`<div class="note-block" data-bid="${b.id}" style="display:flex;align-items:flex-start;gap:8px;padding:6px 0;border-radius:6px">
        <div class="block-handle" data-bid="${b.id}" style="width:20px;min-width:20px;height:20px;display:flex;align-items:center;justify-content:center;border-radius:4px;cursor:pointer;color:#3a3a4a;font-size:15px;margin-top:2px">⋮</div>
        <img src="${b.data}" style="max-width:${b.w||220}px;max-height:200px;border-radius:6px;border:1px solid #2e2e3a;cursor:pointer" onclick="openImgModal(this.src)"/>
        <button class="block-del" data-bid="${b.id}" style="opacity:0;background:none;border:none;color:#ff6b6b;cursor:pointer;font-size:15px;padding:0;margin-top:2px;transition:opacity .15s">✕</button>
      </div>`;
    }
    if(b.type==="toggle"){
      const isOpen=b.open!==false;
      const children=(b.children||[]);
      // Render children recursively — each child can be text or nested toggle
      function renderChild(c, parentBid, depth=1){
        const ccolor=c.color||"#a0a0b0";
        const indent=depth*20;
        if(c.type==="toggle"){
          const cOpen=c.open!==false;
          const grandChildren=(c.children||[]).map(gc=>renderChild(gc,c.id,depth+1)).join("");
          const gcInput=cOpen?`<div style="margin-left:${indent+20}px;margin-top:2px">
            <input class="toggle-add-child" data-bid="${c.id}" data-parentbid="${parentBid}" placeholder="Adicionar item…" style="width:100%;box-sizing:border-box;background:transparent;border:none;border-bottom:1px dashed #2e2e3a;color:#7a7a8a;font-family:'DM Sans',sans-serif;font-size:12px;padding:3px 2px;outline:none"/>
          </div>`:"";
          return`<div class="toggle-child-row" data-bid="${parentBid}" data-cid="${c.id}" style="padding:2px 0;margin-left:${indent}px">
            <div style="display:flex;align-items:center;gap:6px">
              <span class="nested-toggle-arrow" data-bid="${c.id}" data-parentbid="${parentBid}" style="font-size:10px;color:#7a7a8a;cursor:pointer;user-select:none;display:inline-block;transform:${cOpen?"rotate(90deg)":"rotate(0deg)"};width:14px;text-align:center">▶</span>
              <span contenteditable="true" data-bid="${parentBid}" data-cid="${c.id}" class="toggle-child-text" spellcheck="false" style="flex:1;font-size:13px;font-weight:600;color:${ccolor};outline:none;word-break:break-word;line-height:1.6;min-height:16px">${esc(c.text||"")}</span>
              <button class="toggle-child-add-nested" data-bid="${c.id}" data-parentbid="${parentBid}" title="Adicionar subtoggle" style="opacity:0;background:none;border:none;color:#7c6eff;cursor:pointer;font-size:12px;padding:0 3px;transition:opacity .15s">▶+</button>
              <button class="toggle-child-del" data-bid="${parentBid}" data-cid="${c.id}" style="opacity:0;background:none;border:none;color:#ff6b6b;cursor:pointer;font-size:13px;padding:0;transition:opacity .15s">✕</button>
            </div>
            <div class="nested-toggle-body" data-bid="${c.id}" style="display:${cOpen?"block":"none"};border-left:2px solid ${ccolor}33;padding-left:4px">
              ${grandChildren}
              ${gcInput}
            </div>
          </div>`;
        }
        return`<div class="toggle-child-row" data-bid="${parentBid}" data-cid="${c.id}" style="display:flex;align-items:center;gap:8px;padding:3px 0;margin-left:${indent}px">
          <span contenteditable="true" data-bid="${parentBid}" data-cid="${c.id}" class="toggle-child-text" spellcheck="false" style="flex:1;font-size:13px;color:${ccolor};outline:none;word-break:break-word;line-height:1.6;min-height:16px">${esc(c.text||"")}</span>
          <button class="toggle-child-add-nested" data-bid="${c.id}" data-parentbid="${parentBid}" title="Converter em toggle" style="opacity:0;background:none;border:none;color:#7c6eff;cursor:pointer;font-size:12px;padding:0 3px;transition:opacity .15s">▶+</button>
          <button class="toggle-child-del" data-bid="${parentBid}" data-cid="${c.id}" style="opacity:0;background:none;border:none;color:#ff6b6b;cursor:pointer;font-size:13px;padding:0;transition:opacity .15s">✕</button>
        </div>`;
      }
      const childrenHtml=children.map(c=>renderChild(c,b.id,1)).join("");
      const childInput=isOpen?`<div style="margin-left:20px;margin-top:4px;display:flex;gap:6px">
        <input class="toggle-add-child" data-bid="${b.id}" placeholder="Adicionar item… (Enter)" style="flex:1;box-sizing:border-box;background:transparent;border:none;border-bottom:1px dashed #2e2e3a;color:#7a7a8a;font-family:'DM Sans',sans-serif;font-size:12px;padding:4px 2px;outline:none"/>
        <button class="toggle-add-subtoggle" data-bid="${b.id}" title="Adicionar subtoggle" style="background:none;border:1px solid #7c6eff44;color:#9d93ff;cursor:pointer;font-size:11px;padding:2px 7px;border-radius:4px;white-space:nowrap">▶ Toggle</button>
      </div>`:"";
      return`<div class="note-block" data-bid="${b.id}" style="padding:4px 0;border-radius:6px">
        <div style="display:flex;align-items:center;gap:6px">
          <div class="block-handle" data-bid="${b.id}" style="width:20px;min-width:20px;height:20px;display:flex;align-items:center;justify-content:center;border-radius:4px;cursor:pointer;color:#3a3a4a;font-size:15px">⋮</div>
          <span class="toggle-arrow" data-bid="${b.id}" style="font-size:11px;color:#7a7a8a;cursor:pointer;user-select:none;transition:transform .15s;display:inline-block;transform:${isOpen?"rotate(90deg)":"rotate(0deg)"};width:16px;text-align:center">▶</span>
          <span contenteditable="true" data-bid="${b.id}" class="block-text" spellcheck="false" style="flex:1;font-size:13px;font-weight:600;color:${color};outline:none;word-break:break-word;line-height:1.7;min-height:18px">${esc(b.text||"")}</span>
          <button class="block-del" data-bid="${b.id}" style="opacity:0;background:none;border:none;color:#ff6b6b;cursor:pointer;font-size:15px;padding:0;transition:opacity .15s">✕</button>
        </div>
        <div class="toggle-body" data-bid="${b.id}" style="display:${isOpen?"block":"none"};margin-top:4px;padding-left:4px;border-left:2px solid ${color}44">
          ${childrenHtml}
          ${childInput}
        </div>
      </div>`;
    }
    // default: text
    return`<div class="note-block" data-bid="${b.id}" style="display:flex;align-items:center;gap:8px;padding:6px 0;border-radius:6px">
      <div class="block-handle" data-bid="${b.id}" style="width:20px;min-width:20px;height:20px;display:flex;align-items:center;justify-content:center;border-radius:4px;cursor:pointer;color:#3a3a4a;font-size:15px">⋮</div>
      <span contenteditable="true" data-bid="${b.id}" class="block-text" spellcheck="false" style="flex:1;font-size:13px;color:${color};outline:none;word-break:break-word;line-height:1.7;min-height:18px">${linkify(b.text||"")}</span>
      <button class="block-del" data-bid="${b.id}" style="opacity:0;background:none;border:none;color:#ff6b6b;cursor:pointer;font-size:15px;padding:0;transition:opacity .15s">✕</button>
    </div>`;
  }

  const blocksHtml=blocks.length
    ?blocks.map(b=>renderBlock(b)).join("")
    :`<div style="font-size:13px;color:#3a3a4a;padding:6px 0 10px">Nenhuma linha ainda. Use o campo abaixo para começar…</div>`;

  const legacyHtml=legacyNotes.length
    ?`<div style="margin-bottom:16px;padding:10px 12px;background:#1a1a22;border:1px solid #2a2a34;border-radius:8px">
        <div style="font-size:10px;color:#5a5a6a;text-transform:uppercase;letter-spacing:1px;margin-bottom:8px">Notas antigas (formato anterior)</div>
        ${legacyNotes.map(n=>`<div style="margin-bottom:8px;padding:8px;background:#13131a;border-left:3px solid ${n.color||"#c8f04e"};border-radius:4px">
          <div style="font-size:12px;font-weight:600;color:#d0d0e0;margin-bottom:2px">${esc(n.title||"")}</div>
          ${n.body?`<div style="font-size:11px;color:#7a7a8a;line-height:1.5">${esc(n.body)}</div>`:""}
          ${isAdmin1||(n.authorId===currentUser?.uid)?`<button class="btn-del-legacy-note" data-nid="${n.id}" style="margin-top:6px;font-size:10px;color:#ff6b6b;background:none;border:none;cursor:pointer">✕ remover</button>`:""}
        </div>`).join("")}
      </div>`
    :"";

  return`<div class="area-notes-section" id="notes-editor-wrap">
    <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:10px">
      <div style="font-family:'Syne',sans-serif;font-size:15px;font-weight:700">📌 Notas</div>
      <div style="font-size:11px;color:#4a4a5a">⋮ opções &nbsp;·&nbsp; Cole imagem com Ctrl+V</div>
    </div>
    ${legacyHtml}
    <div id="blocks-list">${blocksHtml}</div>
    <div style="margin-top:14px;padding-top:10px;border-top:1px solid #1a1a22">
      <input id="new-block-input" placeholder="Nova linha… (Enter para adicionar)" style="width:100%;box-sizing:border-box;background:#13131a;border:1px solid #1e1e28;border-radius:7px;padding:9px 12px;color:#d0d0e0;font-family:'DM Sans',sans-serif;font-size:13px;outline:none;transition:border-color .15s"/>
    </div>
  </div>`;
}

function attachAreaNotesEditorEvents(areaId){
  const existing=areaNotes[areaId]||{};
  const areaDoc=Object.values(existing).find(d=>Array.isArray(d.blocks))||null;
  let docId=areaDoc?.id||null;
  let blocks=[...(areaDoc?.blocks||[])];

  // Remove legacy notes
  document.querySelectorAll(".btn-del-legacy-note").forEach(b=>{
    b.addEventListener("click",async()=>{
      if(!confirm("Remover nota antiga?"))return;
      await dbRemove(`area_notes/${areaId}/${b.dataset.nid}`);
      toast("Nota removida","warning");
    });
  });

  async function saveBlocks(){
    if(!docId){docId=uid();}
    await dbSet(`area_notes/${areaId}/${docId}`,{
      id:docId,areaId,blocks,
      authorId:currentUser.uid,
      createdAt:areaDoc?.createdAt||new Date().toISOString(),
      updatedAt:new Date().toISOString()
    });
  }

  async function addBlock(text){
    if(!text.trim())return;
    blocks.push({id:uid(),type:"text",text:text.trim(),done:false,color:"#d0d0e0"});
    await saveBlocks();
  }

  // Add block via input
  const inp=document.getElementById("new-block-input");
  inp?.addEventListener("focus",e=>{e.target.style.borderColor="#c8f04e44";});
  inp?.addEventListener("blur",e=>{e.target.style.borderColor="#1e1e28";});
  inp?.addEventListener("keydown",async e=>{
    if(e.key==="Enter"){e.preventDefault();const v=inp.value.trim();if(v){await addBlock(v);inp.value="";}}
  });

  // ── Image paste into area notes editor ──
  function processImgFile(file){
    if(!file||!file.type.startsWith("image/"))return;
    const reader=new FileReader();
    reader.onload=ev=>{
      const img2=new Image();
      img2.onload=async()=>{
        const maxW=800,sc=Math.min(1,maxW/img2.width);
        const cv=document.createElement("canvas");
        cv.width=Math.round(img2.width*sc);cv.height=Math.round(img2.height*sc);
        cv.getContext("2d").drawImage(img2,0,0,cv.width,cv.height);
        blocks.push({id:uid(),type:"image",data:cv.toDataURL("image/webp",0.82),w:Math.min(cv.width,300)});
        await saveBlocks();
      };
      img2.src=ev.target.result;
    };
    reader.readAsDataURL(file);
  }
  const wrap=document.getElementById("notes-editor-wrap");
  wrap?.addEventListener("paste",e=>{
    const items=[...(e.clipboardData?.items||[])];
    if(items.some(it=>it.type.startsWith("image/"))){
      e.preventDefault();
      items.forEach(it=>{if(it.type.startsWith("image/"))processImgFile(it.getAsFile());});
    }
  });
  wrap?.addEventListener("dragover",e=>e.preventDefault());
  wrap?.addEventListener("drop",e=>{e.preventDefault();[...(e.dataTransfer.files||[])].forEach(processImgFile);});

  // Toggle arrow — open/close
  document.querySelectorAll(".toggle-arrow").forEach(arrow=>{
    arrow.addEventListener("click",async()=>{
      const bid=arrow.dataset.bid;
      blocks=blocks.map(b=>b.id===bid?{...b,open:b.open===false}:b);
      await saveBlocks();
    });
  });

  // Helper: deep update child in tree (handles nested toggles)
  function deepUpdateChild(children, cid, updater){
    return children.map(c=>{
      if(c.id===cid)return updater(c);
      if(c.children)return{...c,children:deepUpdateChild(c.children,cid,updater)};
      return c;
    });
  }
  function deepDeleteChild(children, cid){
    return children.filter(c=>c.id!==cid).map(c=>c.children?{...c,children:deepDeleteChild(c.children,cid)}:c);
  }
  function deepAddChild(children, parentCid, newChild){
    return children.map(c=>{
      if(c.id===parentCid)return{...c,children:[...(c.children||[]),newChild]};
      if(c.children)return{...c,children:deepAddChild(c.children,parentCid,newChild)};
      return c;
    });
  }

  // Add child to toggle (first level or nested)
  document.querySelectorAll(".toggle-add-child").forEach(inp2=>{
    inp2.addEventListener("keydown",async e=>{
      if(e.key!=="Enter")return;
      e.preventDefault();
      const text=inp2.value.trim(); if(!text)return;
      const bid=inp2.dataset.bid; // direct parent block id
      const parentBid=inp2.dataset.parentbid; // if nested, the top-level block id
      if(parentBid){
        // nested — add child to cid=bid within parentBid's tree
        blocks=blocks.map(b=>b.id===parentBid?{...b,children:deepAddChild(b.children||[],bid,{id:uid(),type:"text",text,color:"#a0a0b0"})}:b);
      } else {
        blocks=blocks.map(b=>b.id===bid?{...b,children:[...(b.children||[]),{id:uid(),type:"text",text,color:"#a0a0b0"}]}:b);
      }
      await saveBlocks();
    });
  });

  // Add subtoggle button
  document.querySelectorAll(".toggle-add-subtoggle").forEach(btn=>{
    btn.addEventListener("click",async()=>{
      const bid=btn.dataset.bid;
      blocks=blocks.map(b=>b.id===bid?{...b,children:[...(b.children||[]),{id:uid(),type:"toggle",text:"Novo grupo",open:true,color:"#9d93ff",children:[]}]}:b);
      await saveBlocks();
    });
  });

  // Convert child to nested toggle (▶+ button)
  document.querySelectorAll(".toggle-child-add-nested").forEach(btn=>{
    btn.addEventListener("click",async()=>{
      const cid=btn.dataset.bid; // the child to convert
      const parentBid=btn.dataset.parentbid;
      if(!parentBid)return;
      blocks=blocks.map(b=>b.id===parentBid?{...b,children:deepUpdateChild(b.children||[],cid,c=>({...c,type:"toggle",open:true,children:c.children||[]}))}:b);
      await saveBlocks();
    });
  });

  // Nested toggle arrow
  document.querySelectorAll(".nested-toggle-arrow").forEach(arrow=>{
    arrow.addEventListener("click",async()=>{
      const cid=arrow.dataset.bid;
      const parentBid=arrow.dataset.parentbid;
      if(!parentBid)return;
      blocks=blocks.map(b=>b.id===parentBid?{...b,children:deepUpdateChild(b.children||[],cid,c=>({...c,open:c.open===false}))}:b);
      await saveBlocks();
    });
  });

  // Edit child text on blur
  document.querySelectorAll(".toggle-child-text").forEach(el=>{
    el.addEventListener("blur",async()=>{
      const bid=el.dataset.bid, cid=el.dataset.cid;
      const newText=el.innerText.trim();
      blocks=blocks.map(b=>b.id===bid?{...b,children:deepUpdateChild(b.children||[],cid,c=>({...c,text:newText}))}:b);
      await saveBlocks();
    });
    el.addEventListener("keydown",e=>{if(e.key==="Enter"){e.preventDefault();el.blur();}});
  });

  // Delete child (any depth)
  document.querySelectorAll(".toggle-child-del").forEach(btn=>{
    btn.addEventListener("click",async()=>{
      const bid=btn.dataset.bid, cid=btn.dataset.cid;
      blocks=blocks.map(b=>b.id===bid?{...b,children:deepDeleteChild(b.children||[],cid)}:b);
      await saveBlocks();
    });
  });

  // Hover on child rows — show del + nested buttons
  document.querySelectorAll(".toggle-child-row").forEach(row=>{
    const del=row.querySelector(".toggle-child-del");
    const nested=row.querySelector(".toggle-child-add-nested");
    row.addEventListener("mouseenter",()=>{if(del)del.style.opacity="1";if(nested)nested.style.opacity="1";});
    row.addEventListener("mouseleave",()=>{if(del)del.style.opacity="0";if(nested)nested.style.opacity="0";});
  });

  // Inline text editing — save on blur
  document.querySelectorAll(".block-text").forEach(el=>{
    el.addEventListener("blur",async()=>{
      const bid=el.dataset.bid;
      const newText=el.innerText.trim();
      blocks=blocks.map(b=>b.id===bid?{...b,text:newText}:b);
      await saveBlocks();
    });
    el.addEventListener("keydown",e=>{
      if(e.key==="Enter"){e.preventDefault();el.blur();inp?.focus();}
    });
  });

  // Delete block
  document.querySelectorAll(".block-del").forEach(btn=>{
    btn.addEventListener("click",async()=>{
      const bid=btn.dataset.bid;
      if(!confirm("Remover esta linha?"))return;
      blocks=blocks.filter(b=>b.id!==bid);
      await saveBlocks();
    });
  });

  // Show/hide delete button on hover
  document.querySelectorAll(".note-block").forEach(row=>{
    const del=row.querySelector(".block-del");
    const handle=row.querySelector(".block-handle");
    row.addEventListener("mouseenter",()=>{if(del)del.style.opacity="1";if(handle)handle.style.color="#7a7a8a";});
    row.addEventListener("mouseleave",()=>{if(del)del.style.opacity="0";if(handle)handle.style.color="#3a3a4a";});
  });

  // ⋮ handle — show context menu
  document.querySelectorAll(".block-handle").forEach(h=>{
    h.addEventListener("click",e=>{
      e.stopPropagation();
      const bid=h.dataset.bid;
      const block=blocks.find(b=>b.id===bid); if(!block)return;
      const rect=h.getBoundingClientRect();
      showCtxMenu(rect.right+6, rect.top, [
        block.type==="image" ? null :
        block.type==="text"
          ? {action:"to-toggle",icon:"▶",label:"Converter para toggle",fn:async()=>{blocks=blocks.map(b=>b.id===bid?{...b,type:"toggle",open:true,children:b.children||[]}:b);await saveBlocks();}}
          : {action:"to-text",icon:"Aa",label:"Converter para texto",fn:async()=>{blocks=blocks.map(b=>b.id===bid?{...b,type:"text"}:b);await saveBlocks();}},
        "---",
        {action:"color",icon:"🎨",label:"Cor: verde",fn:async()=>{blocks=blocks.map(b=>b.id===bid?{...b,color:"#c8f04e"}:b);await saveBlocks();}},
        {action:"color2",icon:"🎨",label:"Cor: roxo",fn:async()=>{blocks=blocks.map(b=>b.id===bid?{...b,color:"#9d93ff"}:b);await saveBlocks();}},
        {action:"color3",icon:"🎨",label:"Cor: laranja",fn:async()=>{blocks=blocks.map(b=>b.id===bid?{...b,color:"#f0a832"}:b);await saveBlocks();}},
        {action:"color4",icon:"🎨",label:"Cor: vermelho",fn:async()=>{blocks=blocks.map(b=>b.id===bid?{...b,color:"#ff6b6b"}:b);await saveBlocks();}},
        {action:"color5",icon:"🎨",label:"Cor: padrão",fn:async()=>{blocks=blocks.map(b=>b.id===bid?{...b,color:"#d0d0e0"}:b);await saveBlocks();}},
        "---",
        {action:"del",icon:"🗑",label:"Excluir linha",fn:async()=>{blocks=blocks.filter(b=>b.id!==bid);await saveBlocks();}},
      ].filter(Boolean));
    });
  });

  // ── Tab switching ──
  document.getElementById("tab-blocks")?.addEventListener("click",()=>{
    document.getElementById("area-tab-blocks").style.display="";
    document.getElementById("area-tab-fyi").style.display="none";
    document.getElementById("tab-blocks").style.borderBottomColor="#c8f04e";document.getElementById("tab-blocks").style.color="#c8f04e";
    document.getElementById("tab-fyi").style.borderBottomColor="transparent";document.getElementById("tab-fyi").style.color="#7a7a8a";
  });
  document.getElementById("tab-fyi")?.addEventListener("click",()=>{
    document.getElementById("area-tab-blocks").style.display="none";
    document.getElementById("area-tab-fyi").style.display="";
    document.getElementById("tab-fyi").style.borderBottomColor="#c8f04e";document.getElementById("tab-fyi").style.color="#c8f04e";
    document.getElementById("tab-blocks").style.borderBottomColor="transparent";document.getElementById("tab-blocks").style.color="#7a7a8a";
  });

  // ── Area FYI events ──
  document.querySelector(".btn-add-area-fyi")?.addEventListener("click",()=>openAreaFYIModal(null,areaId));
  document.querySelectorAll(".btn-area-fyi-edit").forEach(b=>b.addEventListener("click",e=>{e.stopPropagation();openAreaFYIModal(b.dataset.id,areaId);}));
  document.querySelectorAll(".btn-area-fyi-del").forEach(b=>b.addEventListener("click",async e=>{
    e.stopPropagation();
    if(!confirm("Excluir esta nota FYI?"))return;
    const n=fyiNotes[b.dataset.id];
    await dbRemove(`fyi_notes/${b.dataset.id}`);
    if(n?.calEventId)await dbRemove(`cal_events/${n.calEventId}`);
    toast("Nota removida","warning");
  }));
  document.querySelectorAll(".area-fyi-card").forEach(card=>{
    card.addEventListener("click",e=>{
      if(e.target.classList.contains("btn-area-fyi-edit")||e.target.classList.contains("btn-area-fyi-del"))return;
      const canEdit=fyiNotes[card.dataset.fyiOpen]?.authorId===currentUser?.uid||isAdmin1;
      openAreaFYIModal(card.dataset.fyiOpen, areaId, !canEdit);
    });
    // Drag to reorder
    card.addEventListener("dragstart",e=>{e.dataTransfer.setData("text/plain",card.dataset.fyiId);card.style.opacity="0.5";});
    card.addEventListener("dragend",()=>card.style.opacity="1");
    card.addEventListener("dragover",e=>{e.preventDefault();card.style.background=fyiNotes[card.dataset.fyiOpen]?.color+"18"||"#1e1e28";});
    card.addEventListener("dragleave",()=>card.style.background="");
    card.addEventListener("drop",async e=>{
      e.preventDefault();card.style.background="";
      const srcId=e.dataTransfer.getData("text/plain");
      if(!srcId||srcId===card.dataset.fyiId)return;
      const list=Object.values(fyiNotes).filter(n=>n.areaId===areaId).sort((a,b)=>(a.order||0)-(b.order||0));
      const si=list.findIndex(n=>n.id===srcId), ti=list.findIndex(n=>n.id===card.dataset.fyiId);
      if(si<0||ti<0)return;
      const [moved]=list.splice(si,1); list.splice(ti,0,moved);
      for(let i=0;i<list.length;i++)await dbSet(`fyi_notes/${list[i].id}/order`,i);
    });
  });
}

function attachPersonalNotesEditorEvents(){
  const uid2=currentUser?.uid; if(!uid2)return;
  const doc=Object.values(personalNotes)[0];
  let docId=doc?.id||null;
  let blocks=[...(doc?.blocks||[])];

  async function saveBlocks(){
    if(!docId)docId=uid();
    await dbSet(`personal_notes/${uid2}/${docId}`,{
      id:docId,blocks,
      createdAt:doc?.createdAt||new Date().toISOString(),
      updatedAt:new Date().toISOString()
    });
  }

  async function addBlock(text){
    if(!text.trim())return;
    blocks.push({id:uid(),type:"text",text:text.trim(),done:false,color:"#d0d0e0"});
    await saveBlocks();
  }

  function processImgFileP(file){
    if(!file||!file.type.startsWith("image/"))return;
    const reader=new FileReader();
    reader.onload=ev=>{
      const img2=new Image();
      img2.onload=async()=>{
        const maxW=800,sc=Math.min(1,maxW/img2.width);
        const cv=document.createElement("canvas");
        cv.width=Math.round(img2.width*sc);cv.height=Math.round(img2.height*sc);
        cv.getContext("2d").drawImage(img2,0,0,cv.width,cv.height);
        blocks.push({id:uid(),type:"image",data:cv.toDataURL("image/webp",0.82),w:Math.min(cv.width,300)});
        await saveBlocks();
      };
      img2.src=ev.target.result;
    };
    reader.readAsDataURL(file);
  }

  const inp=document.getElementById("pnew-block-input");
  inp?.addEventListener("focus",e=>{e.target.style.borderColor="#7c6eff44";});
  inp?.addEventListener("blur",e=>{e.target.style.borderColor="#1e1e28";});
  inp?.addEventListener("keydown",async e=>{if(e.key==="Enter"){e.preventDefault();const v=inp.value.trim();if(v){await addBlock(v);inp.value="";}}}); 
;

  // Image paste/drop
  const wrap=document.getElementById("pnotes-editor-wrap");
  wrap?.addEventListener("paste",e=>{
    const items=[...(e.clipboardData?.items||[])];
    if(items.some(it=>it.type.startsWith("image/"))){
      e.preventDefault();
      items.forEach(it=>{if(it.type.startsWith("image/"))processImgFileP(it.getAsFile());});
    }
  });
  wrap?.addEventListener("dragover",e=>e.preventDefault());
  wrap?.addEventListener("drop",e=>{e.preventDefault();[...(e.dataTransfer.files||[])].forEach(processImgFileP);});

  // Toggle arrow — open/close
  document.querySelectorAll(".ptoggle-arrow").forEach(arrow=>{
    arrow.addEventListener("click",async()=>{
      const bid=arrow.dataset.bid;
      blocks=blocks.map(b=>b.id===bid?{...b,open:b.open===false}:b);
      await saveBlocks();
    });
  });

  // Add child to toggle
  document.querySelectorAll(".ptoggle-add-child").forEach(inp2=>{
    inp2.addEventListener("keydown",async e=>{
      if(e.key!=="Enter")return;
      e.preventDefault();
      const text=inp2.value.trim(); if(!text)return;
      const bid=inp2.dataset.bid;
      blocks=blocks.map(b=>b.id===bid?{...b,children:[...(b.children||[]),{id:uid(),text,color:"#a0a0b0"}]}:b);
      await saveBlocks();
    });
  });

  // Edit child text on blur
  document.querySelectorAll(".ptoggle-child-text").forEach(el=>{
    el.addEventListener("blur",async()=>{
      const bid=el.dataset.bid, cid=el.dataset.cid;
      blocks=blocks.map(b=>b.id===bid?{...b,children:(b.children||[]).map(c=>c.id===cid?{...c,text:el.innerText.trim()}:c)}:b);
      await saveBlocks();
    });
    el.addEventListener("keydown",e=>{if(e.key==="Enter"){e.preventDefault();el.blur();}});
  });

  // Delete child
  document.querySelectorAll(".ptoggle-child-del").forEach(btn=>{
    btn.addEventListener("click",async()=>{
      const bid=btn.dataset.bid, cid=btn.dataset.cid;
      blocks=blocks.map(b=>b.id===bid?{...b,children:(b.children||[]).filter(c=>c.id!==cid)}:b);
      await saveBlocks();
    });
  });
  document.querySelectorAll(".ptoggle-child-del").forEach(btn=>{
    const row=btn.parentElement;
    row?.addEventListener("mouseenter",()=>btn.style.opacity="1");
    row?.addEventListener("mouseleave",()=>btn.style.opacity="0");
  });

  // Text editing
  document.querySelectorAll(".pblock-text").forEach(el=>{
    el.addEventListener("blur",async()=>{
      const bid=el.dataset.bid;
      blocks=blocks.map(b=>b.id===bid?{...b,text:el.innerText.trim()}:b);
      await saveBlocks();
    });
    el.addEventListener("keydown",e=>{if(e.key==="Enter"){e.preventDefault();el.blur();inp?.focus();}});
  });

  // Delete
  document.querySelectorAll(".pblock-del").forEach(b=>{
    b.addEventListener("click",async()=>{
      const bid=b.dataset.bid;
      if(!confirm("Remover esta linha?"))return;
      blocks=blocks.filter(bl=>bl.id!==bid);
      await saveBlocks();
    });
  });

  // Hover show/hide
  document.querySelectorAll(".pnote-block").forEach(row=>{
    const del=row.querySelector(".pblock-del");
    const handle=row.querySelector(".pblock-handle");
    row.addEventListener("mouseenter",()=>{if(del)del.style.opacity="1";if(handle)handle.style.color="#7a7a8a";});
    row.addEventListener("mouseleave",()=>{if(del)del.style.opacity="0";if(handle)handle.style.color="#3a3a4a";});
  });

  // ⋮ context menu
  document.querySelectorAll(".pblock-handle").forEach(h=>{
    h.addEventListener("click",e=>{
      e.stopPropagation();
      const bid=h.dataset.bid;
      const block=blocks.find(b=>b.id===bid); if(!block)return;
      const rect=h.getBoundingClientRect();
      showCtxMenu(rect.right+6, rect.top, [
        block.type==="image" ? null :
        block.type==="text"
          ? {action:"to-toggle",icon:"▶",label:"Converter para toggle",fn:async()=>{blocks=blocks.map(b=>b.id===bid?{...b,type:"toggle",open:true,children:b.children||[]}:b);await saveBlocks();}}
          : {action:"to-text",icon:"Aa",label:"Converter para texto",fn:async()=>{blocks=blocks.map(b=>b.id===bid?{...b,type:"text"}:b);await saveBlocks();}},
        "---",
        {action:"color",icon:"🎨",label:"Cor: verde",fn:async()=>{blocks=blocks.map(b=>b.id===bid?{...b,color:"#c8f04e"}:b);await saveBlocks();}},
        {action:"color2",icon:"🎨",label:"Cor: roxo",fn:async()=>{blocks=blocks.map(b=>b.id===bid?{...b,color:"#9d93ff"}:b);await saveBlocks();}},
        {action:"color3",icon:"🎨",label:"Cor: laranja",fn:async()=>{blocks=blocks.map(b=>b.id===bid?{...b,color:"#f0a832"}:b);await saveBlocks();}},
        {action:"color4",icon:"🎨",label:"Cor: vermelho",fn:async()=>{blocks=blocks.map(b=>b.id===bid?{...b,color:"#ff6b6b"}:b);await saveBlocks();}},
        {action:"color5",icon:"🎨",label:"Cor: padrão",fn:async()=>{blocks=blocks.map(b=>b.id===bid?{...b,color:"#d0d0e0"}:b);await saveBlocks();}},
        "---",
        {action:"del",icon:"🗑",label:"Excluir linha",fn:async()=>{blocks=blocks.filter(b=>b.id!==bid);await saveBlocks();}},
      ].filter(Boolean));
    });
  });
}
window.openImgModal=function(src){
  const ov=document.createElement("div");
  ov.style.cssText="position:fixed;inset:0;background:rgba(0,0,0,.85);z-index:9999;display:flex;align-items:center;justify-content:center;cursor:zoom-out";
  ov.innerHTML=`<img src="${src}" style="max-width:90vw;max-height:90vh;border-radius:10px;box-shadow:0 20px 60px rgba(0,0,0,.6);user-select:none"/>`;
  ov.addEventListener("click",()=>ov.remove());
  document.body.appendChild(ov);
};

// ── TOAST ─────────────────────────────────────────────────────────────────────
function toast(msg,type="success"){const el=document.createElement("div");el.className=`toast ${type}`;el.innerHTML=`<span style="font-size:16px">${{success:"✓",error:"✕",warning:"⚠"}[type]||"ℹ"}</span><span>${esc(msg)}</span>`;document.getElementById("toast-container").appendChild(el);setTimeout(()=>{el.style.opacity="0";el.style.transform="translateX(20px)";el.style.transition="all .3s";setTimeout(()=>el.remove(),300);},3000);}

document.addEventListener("keydown",e=>{if(e.key==="Escape"){closeModal();connecting=null;selEdge=null;}});

// ── TOGGLE LIST (Notion-style) ──────────────────────────────────────────────
async function insertToggleItem(noteId){
  const note=(areaNotes[activeAreaId]||{})[noteId]; if(!note)return;
  const item=prompt("Texto do item de lista:");
  if(!item)return;
  const items=[...(note.toggleItems||[]),{id:uid(),text:item,done:false}];
  await dbSet(`area_notes/${activeAreaId}/${noteId}/toggleItems`,items);
  toast("Item adicionado!","success");
}
async function insertToggleItemPersonal(noteId){
  const note=personalNotes[noteId]; if(!note)return;
  const item=prompt("Texto do item de lista:");
  if(!item)return;
  const items=[...(note.toggleItems||[]),{id:uid(),text:item,done:false}];
  await dbSet(`personal_notes/${currentUser.uid}/${noteId}/toggleItems`,items);
  toast("Item adicionado!","success");
}
async function toggleNoteItem(path,items,itemId){
  const updated=items.map(it=>it.id===itemId?{...it,done:!it.done}:it);
  await dbSet(path,updated);
}
window.handleToggleItem=async function(el){
  const path=el.dataset.path;
  const itemId=el.dataset.itemid;
  const noteId=el.dataset.noteid;
  const areaId=el.dataset.areaid;
  if(areaId){
    const items=(areaNotes[areaId]||{})[noteId]?.toggleItems||[];
    await toggleNoteItem(`area_notes/${areaId}/${noteId}/toggleItems`,items,itemId);
  } else {
    const items=personalNotes[noteId]?.toggleItems||[];
    await toggleNoteItem(`personal_notes/${currentUser.uid}/${noteId}/toggleItems`,items,itemId);
  }
};
