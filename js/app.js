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

function uid(){return Date.now().toString(36)+Math.random().toString(36).slice(2);}
function fmtDate(d){if(!d)return"—";const[y,m,day]=d.split("-");return`${day}/${m}/${y}`;}
function fmtTs(ts){if(!ts)return"";const d=new Date(ts);return`${d.toLocaleDateString("pt-BR")} ${d.toLocaleTimeString("pt-BR",{hour:"2-digit",minute:"2-digit"})}`;}
function initials(n){return(n||"?").split(" ").map(w=>w[0]).join("").toUpperCase().slice(0,2);}
function esc(s){return String(s||"").replace(/&/g,"&amp;").replace(/</g,"&lt;").replace(/>/g,"&gt;");}

function deadlineClass(d){if(!d)return null;const diff=new Date(d+"T23:59:59")-new Date();if(diff<=0)return null;if(diff<=10800000)return"warn-now";if(diff<=86400000)return"warn-1";if(diff<=172800000)return"warn-2";if(diff<=259200000)return"warn-3";return null;}
function deadlineBadge(d){const c=deadlineClass(d);if(!c)return"";const m={"warn-now":"⚠️ <3h","warn-1":"🔴 Amanhã","warn-2":"🟠 2 dias","warn-3":"🟡 3 dias"},mp={"warn-now":"wnow","warn-1":"w1","warn-2":"w2","warn-3":"w3"};return`<span class="deadline-badge ${mp[c]}">${m[c]}</span>`;}

// ── STATE ─────────────────────────────────────────────────────────────────────
let currentUser=null, currentProfile=null, isAdmin1=false;
let page="dashboard", activeAreaId=null, dropdownOpen=false;
let areas={}, tasks={}, notes={}, users={}, flowData={nodes:{},edges:{}}, orgData={nodes:{},edges:{}}, calEvents={};
let auditLog={}, personalNotes={}, pendingUsers={}, areaNotes={};
let dragging=null, connecting=null, selEdge=null, mousePos={x:0,y:0};
let selectedNodes=new Set(), groupDragging=null, selBox=null;
let flowSelecting=false, flowSelStart={x:0,y:0}; // drag-to-select state
let expandedAreas=new Set(); // sidebar subarea toggle
let areaNotesListeners={};
let alertsSent={}, calAlertsSent={};

// ── DB HELPERS ────────────────────────────────────────────────────────────────
const dbRef=p=>ref(db,p);
function dbSet(p,v){return set(dbRef(p),v);}
function dbPush(p,v){return push(dbRef(p),v);}
function dbRemove(p){return remove(dbRef(p));}
function dbListen(p,cb){onValue(dbRef(p),s=>cb(s.val()||{}));}

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

// ── LISTENERS ─────────────────────────────────────────────────────────────────
let listenersReady=0;
function checkReady(){listenersReady++;if(listenersReady>=10){document.getElementById("loader").style.display="none";document.getElementById("app").style.display="flex";render();startAlertWatcher();}}

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
  if(currentUser) onValue(dbRef(`personal_notes/${currentUser.uid}`),s=>{personalNotes=s.val()||{};render();});
  checkReady();
}

// ── AUTH ──────────────────────────────────────────────────────────────────────
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

function nav(p,extra){page=p;dropdownOpen=false;if(p==="area")activeAreaId=extra;render();}

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
    let html=`<div class="nav-item area-row ${isCur?"active":""}" data-nav="area" data-id="${a.id}" style="${isCur?`color:${a.color}`:""};${indent}">`
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
  const rootAreas=allAreas.filter(a=>!a.parentId);
  const areaTreeHtml=rootAreas.map(a=>areaItem(a,0)).join("");

  sn.innerHTML=`
    ${ni("dashboard","⬡","Dashboard")}
    ${ni("fluxo","⟆","Fluxograma")}
    ${ni("calendario","📅","Calendário")}
    ${ni("organograma","🏢","Organograma")}
    ${ni("minhas-tarefas","📋","Minhas Tarefas")}
    ${ni("fyi","💡","FYI")}
    ${ni("alertas","🔔","Alertas",urgentCount>0?`<span class="nav-alert-count">${urgentCount}</span>`:"")}
    ${ni("notas-pessoais","📝","Rascunhos Pessoais")}
    ${(isAdmin()||currentProfile?.manageAreas)?ni("admin","⚙️","Administração",pendingCount>0?`<span class="nav-alert-count">${pendingCount}</span>`:""):""}
    ${ni("historico","🕵️","Histórico")}
    <div class="side-label">ÁREAS</div>
    ${areaTreeHtml}`;

  sb.innerHTML=isAdmin()?`<button id="btn-add-area" style="width:100%;padding:9px;border:1px dashed #2e2e3a;background:transparent;color:#7a7a8a;cursor:pointer;border-radius:8px;font-family:inherit;font-size:13px;transition:all .12s">+ Nova área raiz</button>`:"";

  // Nav click
  sn.querySelectorAll(".nav-item[data-nav]").forEach(el=>el.addEventListener("click",e=>{
    if(e.target.classList.contains("area-arrow")||e.target.classList.contains("area-add-sub"))return;
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
}

// ── TOPBAR ────────────────────────────────────────────────────────────────────
function renderTopbar(){
  const tb=document.getElementById("topbar");if(!tb)return;
  const titles={dashboard:"Dashboard",fluxo:"Fluxograma",organograma:"Organograma",calendario:"Calendário",freela:"Calendário",fyi:"FYI","minhas-tarefas":"Minhas Tarefas","notas-pessoais":"Rascunhos Pessoais",alertas:"Alertas",admin:"Administração",historico:"Histórico de Ações"};
  const label=page==="area"?(areas[activeAreaId]?.name||"Área"):(titles[page]||"");
  tb.innerHTML=`<div class="topbar-title">${esc(label)}</div>
    <div style="position:relative">
      <div class="topbar-user" id="user-btn"><div class="user-avatar">${initials(currentProfile.name)}</div><span class="topbar-user-name">${esc(currentProfile.name)}</span><span style="font-size:11px;color:#7a7a8a;margin-left:2px">▾</span></div>
      ${dropdownOpen?`<div class="user-dropdown"><div style="padding:8px 12px;font-size:11px;color:#5a5a6a">${esc(currentProfile.email)}</div><div style="padding:2px 12px 8px;font-size:10px;color:#7a7a8a">${{"admin1":"👑 Super Admin","admin":"Admin","user":"Usuário"}[currentProfile.role]||""}</div><hr class="divider"/><div class="user-dropdown-item" id="dd-profile">Meu perfil</div><div class="user-dropdown-item danger" id="dd-logout">Sair</div></div>`:""}
    </div>`;
  document.getElementById("user-btn").addEventListener("click",e=>{e.stopPropagation();dropdownOpen=!dropdownOpen;render();});
  document.getElementById("dd-logout")?.addEventListener("click",()=>signOut(auth));
  document.getElementById("dd-profile")?.addEventListener("click",()=>{dropdownOpen=false;openProfileModal();});
}
document.addEventListener("click",()=>{if(dropdownOpen){dropdownOpen=false;render();}});

// ── CONTENT ROUTER ────────────────────────────────────────────────────────────
function renderContent(){
  const mc=document.getElementById("main-content");if(!mc)return;
  const map={dashboard:renderDashboard,area:renderAreaPage,fluxo:renderFlowPage,organograma:renderOrgPage,calendario:renderCalPage,freela:renderCalPage,"minhas-tarefas":renderMyTasksPage,"notas-pessoais":renderPersonalNotesPage,fyi:renderFYIPage,alertas:renderAlertsPage,admin:renderAdminPage,historico:renderHistoricoPage};
  mc.innerHTML=(map[page]||renderDashboard)();
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
        ${t.resp?`<span class="chip" style="background:#7c6eff18;color:#9d93ff;border:1px solid #7c6eff30">${esc(t.resp)}</span>`:""}
        ${deadlineBadge(t.date)}
        ${t.date&&!deadlineClass(t.date)?`<span style="font-size:10px;color:#7a7a8a;margin-left:auto">${fmtDate(t.date)}</span>`:""}
      </div>
    </div>`).join(""):`<div style="font-size:12px;color:#4a4a5a;text-align:center;padding:20px 8px">Vazio</div>`;
    return`<div class="column"><div class="col-header" style="border-bottom:2px solid ${st.color}35"><div class="dot" style="background:${st.color}"></div><div style="font-family:'Syne',sans-serif;font-size:12px;font-weight:700;color:${st.color};flex:1">${st.label}</div><div class="col-count">${col.length}</div></div><div class="cards-list">${cards}</div><button class="add-card-btn btn-add-task-col" data-status="${key}">+ Adicionar</button></div>`;
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

  <!-- Area details block (compact, admin1 only edits) -->
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
  const nodes=Object.entries(flowData.nodes||{}).map(([id,n])=>({id,...n}));
  const edges=Object.entries(flowData.edges||{}).map(([id,e])=>({id,...e}));
  const myAreas=visibleAreas();
  const nodeCount=nodes.length;

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

  // SVG nodes
  const svgNodes=nodes.map(n=>{
    const W=n.w||150, H=n.h||48;
    const fsize=n.fontSize||18, ffam="Syne";
    const hasArea=n.areaId&&areas[n.areaId];
    const bc=hasArea?areas[n.areaId].color:(n.color||"#c8f04e");
    const isSel=selectedNodes.has(n.id);
    const lblFull=n.label||"";
    const lbl=lblFull.length>28?lblFull.slice(0,26)+"…":lblFull;
    const detail=n.detail||"";
    const shape=n.shape==="diamond"
      ?`<polygon points="${W/2},0 ${W},${H/2} ${W/2},${H} 0,${H/2}" fill="${bc}20" stroke="${isSel?"#c8f04e":bc}" stroke-width="${isSel?3:hasArea?2.5:1.5}"/>`
      :n.shape==="pill"
      ?`<rect x="0" y="0" width="${W}" height="${H}" rx="${H/2}" fill="${bc}20" stroke="${isSel?"#c8f04e":bc}" stroke-width="${isSel?3:1.5}"/>`
      :`<rect x="0" y="0" width="${W}" height="${H}" rx="10" fill="${bc}20" stroke="${isSel?"#c8f04e":bc}" stroke-width="${isSel?3:hasArea?2.5:1.5}"/>`;
    const textY=detail?(hasArea?H/2-14:H/2-8):( hasArea?H/2-9:H/2 );
    return`<g class="flow-node" data-node-id="${n.id}" data-area-id="${n.areaId||""}" transform="translate(${n.x},${n.y})" style="cursor:${hasArea&&!connecting?"pointer":"grab"}">
      ${shape}
      <text x="${W/2}" y="${textY}" text-anchor="middle" dominant-baseline="middle" fill="#f0eff5" font-size="${fsize}" font-weight="700" font-family="${ffam},sans-serif" style="pointer-events:none;user-select:none">${esc(lbl)}</text>
      ${detail?`<text x="${W/2}" y="${textY+fsize+4}" text-anchor="middle" dominant-baseline="middle" fill="${bc}" font-size="${Math.max(9,fsize-4)}" font-weight="400" font-family="DM Sans,sans-serif" style="pointer-events:none;opacity:.85">${esc(detail.slice(0,28)+(detail.length>28?"…":""))}</text>`:""}
      ${hasArea?`<text x="${W/2}" y="${H-6}" text-anchor="middle" dominant-baseline="middle" fill="${bc}" font-size="9" font-weight="400" style="pointer-events:none;opacity:.7">↗ ${esc(areas[n.areaId].name.slice(0,18))}</text>`:""}
      <!-- 4-side connection handles -->
      <circle cx="${W/2}" cy="0" r="6" fill="${connecting?.fromId===n.id?"#c8f04e":"#16161e"}" stroke="${bc}" stroke-width="1.5" class="conn-handle" data-node-id="${n.id}" data-side="top" style="cursor:crosshair"/>
      <circle cx="${W}" cy="${H/2}" r="6" fill="${connecting?.fromId===n.id?"#c8f04e":"#16161e"}" stroke="${bc}" stroke-width="1.5" class="conn-handle" data-node-id="${n.id}" data-side="right" style="cursor:crosshair"/>
      <circle cx="${W/2}" cy="${H}" r="6" fill="${connecting?.fromId===n.id?"#c8f04e":"#16161e"}" stroke="${bc}" stroke-width="1.5" class="conn-handle" data-node-id="${n.id}" data-side="bottom" style="cursor:crosshair"/>
      <circle cx="0" cy="${H/2}" r="6" fill="${connecting?.fromId===n.id?"#c8f04e":"#16161e"}" stroke="${bc}" stroke-width="1.5" class="conn-handle" data-node-id="${n.id}" data-side="left" style="cursor:crosshair"/>
      ${isAdmin1?`<circle cx="${W+4}" cy="-4" r="8" fill="#ff6b6b1a" stroke="#ff6b6b" stroke-width="1.2" class="del-node" data-node-id="${n.id}" style="cursor:pointer"/><text x="${W+4}" y="-4" text-anchor="middle" dominant-baseline="middle" fill="#ff6b6b" font-size="11" style="pointer-events:none">✕</text>`:""}
      ${isAdmin1?`<circle cx="-4" cy="${H+4}" r="8" fill="#7c6eff1a" stroke="#7c6eff" stroke-width="1.2" class="edit-flow-node" data-node-id="${n.id}" style="cursor:pointer"/><text x="-4" y="${H+4}" text-anchor="middle" dominant-baseline="middle" fill="#9d93ff" font-size="10" style="pointer-events:none">✏</text>`:""}
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
      </div>
      ${areaButtons?`<div style="display:flex;gap:6px;flex-wrap:wrap">${areaButtons}</div>`:""}
    </div>`:""}
    <div class="flow-canvas" style="position:relative">
      <div id="stickies-layer" style="position:absolute;inset:0;pointer-events:none;z-index:10;overflow:hidden"></div>
      <svg id="flow-svg" width="100%" height="560" style="display:block;cursor:${connecting?"crosshair":"default"}">
        <defs>
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
        <g id="flow-zoom-group" transform="translate(${flowPan.x},${flowPan.y}) scale(${flowZoom})">${svgGroups}${svgEdges}${liveEdge}${svgNodes}${selBox?`<rect x="${Math.min(selBox.x1,selBox.x2)}" y="${Math.min(selBox.y1,selBox.y2)}" width="${Math.abs(selBox.x2-selBox.x1)}" height="${Math.abs(selBox.y2-selBox.y1)}" fill="#c8f04e08" stroke="#c8f04e" stroke-width="1" stroke-dasharray="5,3" style="pointer-events:none"/>`:""}</g>
        ${nodes.length===0?`<text x="50%" y="50%" text-anchor="middle" dominant-baseline="middle" fill="#2e2e42" font-size="15" font-family="DM Sans,sans-serif">Use os botões acima para adicionar blocos e conectar áreas</text>`:""}
      </svg>
    </div>
    ${selectedNodes.size>1?`
    <div id="flow-group-bar" style="margin-top:10px;background:#1a1a22;border:1px solid #c8f04e33;border-radius:10px;padding:10px 14px;display:flex;align-items:center;gap:12px;flex-wrap:wrap">
      <span style="font-size:12px;color:#c8f04e;font-weight:700">${selectedNodes.size} blocos selecionados</span>
      <span style="font-size:12px;color:#7a7a8a">Mover para dentro de:</span>
      <select id="flow-group-parent" style="background:#13131a;border:1px solid #2e2e3a;border-radius:7px;padding:6px 10px;color:#f0eff5;font-family:inherit;font-size:12px;outline:none;min-width:140px">
        <option value="">— Escolher bloco pai —</option>
        <option value="__remove__">✕ Remover do grupo</option>
        ${nodes.filter(n=>!selectedNodes.has(n.id)).map(n=>`<option value="${n.id}">${esc(n.label||"?")}</option>`).join("")}
      </select>
      <button id="flow-group-apply" class="btn-primary" style="font-size:12px;padding:6px 14px">Aplicar</button>
      <button id="flow-group-clear" class="btn-ghost" style="font-size:12px;padding:6px 10px">Limpar seleção</button>
    </div>`:""}
    <div style="font-size:11px;color:#4a4a5a;margin-top:8px;display:flex;gap:20px;flex-wrap:wrap">
      <span>🖱 Arraste blocos · Shift+clique seleciona mais</span>
      <span>⬜ Arraste no fundo para selecionar vários</span>
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
      return`<div class="note-card">${n.tag?`<span class="note-tag" style="background:${n.color||"#c8f04e"}18;color:${n.color||"#c8f04e"};border:1px solid ${n.color||"#c8f04e"}30">${esc(n.tag)}</span>`:""}
        <div style="display:flex;align-items:flex-start;justify-content:space-between;gap:8px;margin-bottom:8px"><div class="note-title">${esc(n.title)}</div>${isAdmin()||n.authorId===currentUser?.uid?`<div style="display:flex;gap:6px"><button class="icon-btn btn-edit-note" data-id="${n.id}">✏</button><button class="icon-btn btn-del-note" data-id="${n.id}">✕</button></div>`:""}</div>
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
    .sort((a,b)=>new Date(b.createdAt)-new Date(a.createdAt));
  const noteCards=notes.map(n=>{
    const color=n.color||"#c8f04e";
    const syncBadge=n.syncCal?`<span style="font-size:10px;background:#7c6eff22;color:#9d93ff;border:1px solid #7c6eff44;border-radius:10px;padding:1px 7px">📅 no calendário</span>`:"";
    return`<div class="fyi-card" style="background:${color}10;border:1.5px solid ${color}33;border-radius:10px;padding:14px 16px;margin-bottom:12px;position:relative">
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

function openFYIModal(noteId){
  const n=noteId?fyiNotes[noteId]:{};
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

function renderAlertsPage(){
  const myAreas=visibleAreas().map(a=>a.id);
  const urgent=Object.entries(tasks).map(([id,t])=>({id,...t})).filter(t=>myAreas.includes(t.areaId)&&t.date&&t.status!=="concluido"&&deadlineClass(t.date)).sort((a,b)=>new Date(a.date)-new Date(b.date));
  if(!urgent.length)return`<div class="page-header"><div><div class="page-title">Alertas</div></div></div><div class="empty-state" style="padding:60px 20px"><div style="font-size:40px;margin-bottom:12px">✅</div><div class="empty-title">Tudo em dia!</div></div>`;
  const cc={"warn-now":"#ff2020","warn-1":"#e85030","warn-2":"#f09030","warn-3":"#e8c84a"};
  const cl={"warn-now":"⚠️ Menos de 3h","warn-1":"🔴 Amanhã","warn-2":"🟠 Em 2 dias","warn-3":"🟡 Em 3 dias"};
  const bm={"warn-now":"wnow","warn-1":"w1","warn-2":"w2","warn-3":"w3"};
  return`<div class="page-header"><div><div class="page-title">Alertas</div><div class="page-sub">${urgent.length} tarefa${urgent.length!==1?"s":""} com prazo próximo</div></div></div>
    ${urgent.map(t=>{const c=deadlineClass(t.date),ar=areas[t.areaId];return`<div class="alert-card" style="border-left:3px solid ${cc[c]}"><div class="alert-dot" style="background:${cc[c]}"></div><div style="flex:1"><div style="font-size:14px;font-weight:500;margin-bottom:4px">${esc(t.title)}</div><div style="display:flex;gap:10px;flex-wrap:wrap;font-size:12px;color:#7a7a8a">${ar?`<span>📁 ${esc(ar.name)}</span>`:""}${t.resp?`<span>👤 ${esc(t.resp)}</span>`:""}<span>📅 ${fmtDate(t.date)}</span></div></div><span class="deadline-badge ${bm[c]}">${cl[c]}</span><button class="btn-small btn-detail-alert" data-id="${t.id}" style="border:1px solid #2e2e3a;color:#7a7a8a">Ver</button></div>`;}).join("")}`;
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
  const areaList=Object.entries(areas).map(([id,a])=>({id,...a}));
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
  document.querySelectorAll(".btn-ghost-link").forEach(b=>b.addEventListener("click",()=>openGhostLinkModal(b.dataset.uid,b.dataset.name)));
  document.querySelectorAll(".btn-approve-user").forEach(b=>b.addEventListener("click",async()=>{const p=pendingUsers[b.dataset.id];if(!p)return;await dbSet(`users/${b.dataset.id}`,{name:p.name,email:p.email,role:"user",permissions:[],createdAt:new Date().toISOString()});await dbSet(`pending_users/${b.dataset.id}/status`,"approved");await logAction("aprovar_usuario",`Aprovado: ${p.name}`);toast(`${p.name} aprovado!`,"success");}));
  document.querySelectorAll(".btn-reject-user").forEach(b=>b.addEventListener("click",async()=>{const p=pendingUsers[b.dataset.id];if(!p)return;await dbSet(`pending_users/${b.dataset.id}/status`,"rejected");await logAction("rejeitar_usuario",`Rejeitado: ${p.name}`);toast(`${p.name} rejeitado`,"warning");}));
  document.querySelectorAll(".perm-toggle").forEach(b=>b.addEventListener("click",async()=>{
    const u=users[b.dataset.uid];if(!u||u.role==="admin1")return;
    // only admin1 OR users with manageAreas permission can toggle
    if(!isAdmin1&&!currentProfile?.manageAreas){toast("Sem permissão para alterar áreas de usuários","error");return;}
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
      // If clicking a conn-handle, del-node or edit button — let those handlers run, don't intercept
      if(e.target.classList.contains("conn-handle")||e.target.classList.contains("del-node")||e.target.classList.contains("edit-flow-node"))return;
      e.stopPropagation(); // prevent SVG background selBox from starting
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
        // group drag — store offsets for all selected
        groupDragging={startX:e.clientX,startY:e.clientY,nodes:Object.fromEntries([...selectedNodes].map(sid=>{const sn=allNodes2.find(x=>x.id===sid);return[sid,{x:sn.x,y:sn.y}];}))};
      } else {
        selectedNodes.clear();render();
        dragging={id:nid,ox:e.clientX-r.left-n.x,oy:e.clientY-r.top-n.y};
      }
    });
  });
  svg.addEventListener("mousemove",e=>{
    const r=svg.getBoundingClientRect();
    const cx=(e.clientX-r.left-flowPan.x)/flowZoom;
    const cy=(e.clientY-r.top-flowPan.y)/flowZoom;
    mousePos={x:cx,y:cy};
    if(connecting){render();return;}
    if(flowSelecting&&selBox){
      selBox.x2=cx; selBox.y2=cy;
      render(); return;
    }
    if(groupDragging){
      const dx=(e.clientX-groupDragging.startX)/flowZoom;
      const dy=(e.clientY-groupDragging.startY)/flowZoom;
      Object.entries(groupDragging.nodes).forEach(([sid,orig])=>{
        dbSet(`flow/nodes/${sid}/x`,Math.max(0,orig.x+dx));
        dbSet(`flow/nodes/${sid}/y`,Math.max(0,orig.y+dy));
      });
      return;
    }
    if(!dragging)return;
    dbSet(`flow/nodes/${dragging.id}/x`,Math.max(0,cx-dragging.ox));
    dbSet(`flow/nodes/${dragging.id}/y`,Math.max(0,cy-dragging.oy));
  });
  svg.addEventListener("mouseup",()=>{
    if(flowSelecting&&selBox){
      const x1=Math.min(selBox.x1,selBox.x2), x2=Math.max(selBox.x1,selBox.x2);
      const y1=Math.min(selBox.y1,selBox.y2), y2=Math.max(selBox.y1,selBox.y2);
      // Only select if dragged enough (avoid click)
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
    selBox=null; flowSelecting=false;
    dragging=null; groupDragging=null;
  });
  svg.addEventListener("click",e=>{if(connecting&&e.target===svg){connecting=null;render();return;}});
  svg.addEventListener("mousedown",e=>{
    // Only start selBox on direct SVG background click (not on nodes/edges)
    if(e.target!==svg&&e.target.getAttribute("fill")!=="url(#grid)")return;
    if(connecting)return;
    if(!e.shiftKey)selectedNodes.clear();
    const r=svg.getBoundingClientRect();
    const cx=(e.clientX-r.left-flowPan.x)/flowZoom;
    const cy=(e.clientY-r.top-flowPan.y)/flowZoom;
    selBox={x1:cx,y1:cy,x2:cx,y2:cy};
    flowSelecting=true;
    render();
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
    if(parentId==="__remove__"){
      // Remove groupParent from all selected nodes
      for(const id of selectedNodes){
        await dbSet(`flow/nodes/${id}/groupParent`,null);
      }
      toast("Blocos removidos do grupo","success");
    } else {
      // Assign selected nodes to parent
      for(const id of selectedNodes){
        if(id===parentId)continue; // don't make node parent of itself
        await dbSet(`flow/nodes/${id}/groupParent`,parentId);
      }
      toast(`${selectedNodes.size} bloco(s) agrupado(s)`,"success");
    }
    selectedNodes.clear();
    render();
  });
  document.getElementById("flow-group-clear")?.addEventListener("click",()=>{selectedNodes.clear();render();});

  // ── Sticky notes ──
  document.getElementById("btn-add-sticky")?.addEventListener("click",()=>{
    const id=uid();
    dbSet(`flow/stickies/${id}`,{id,text:"",color:"#f0a832",x:80+Math.random()*300,y:60+Math.random()*200,expanded:true,createdAt:new Date().toISOString()});
  });
  renderStickies();
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
      <div class="field-row">
        <div class="field"><label>Largura (px)</label><input type="number" id="m-nw" value="${n.w||150}" min="80" max="400" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none"/></div>
        <div class="field"><label>Altura (px)</label><input type="number" id="m-nh" value="${n.h||48}" min="32" max="200" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none"/></div>
        <div class="field"><label>Tamanho fonte</label><input type="number" id="m-nfsize" value="${n.fsize||14}" min="8" max="32" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none"/></div>
      </div>
      <div class="field">
        <label>Fonte</label>
        <select id="m-nffam" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none">
          ${["Syne","DM Sans","Arial","Georgia","Courier New","Impact"].map(f=>`<option value="${f}" ${(n.ffam||"Syne")===f?"selected":""}>${f}</option>`).join("")}
        </select>
      </div>
      <div class="field">
        <label>Vincular a área existente <span style="color:#7a7a8a;font-size:10px">(ou criar nova abaixo)</span></label>
        <select id="m-narea" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none">
          <option value="">Nenhuma</option>
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
  document.getElementById("m-save").onclick=async()=>{
    const label=document.getElementById("m-nlabel").value.trim(); if(!label){toast("Rótulo obrigatório","error");return;}
    let areaId=document.getElementById("m-narea").value||null;
    const newAreaName=document.getElementById("m-nnewarea").value.trim();
    if(newAreaName){
      const newColor=document.getElementById("m-nnewareacolor").value||"#c8f04e";
      const newAid=uid();
      await dbSet(`areas/${newAid}`,{name:newAreaName,color:newColor,createdAt:new Date().toISOString()});
      areaId=newAid;
      toast(`Área "${newAreaName}" criada!`,"success");
    }
    const updated={...n,
      label,
      detail:document.getElementById("m-ndetail").value.trim()||"",
      shape:document.getElementById("m-nshape").value,
      color:document.getElementById("m-ncolor").value,
      w:parseInt(document.getElementById("m-nw").value)||150,
      h:parseInt(document.getElementById("m-nh").value)||48,
      fsize:parseInt(document.getElementById("m-nfsize").value)||14,
      ffam:document.getElementById("m-nffam").value||"Syne",
      areaId:areaId||null
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
function openRepeatTaskModal(t){
  setTimeout(()=>{
    openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:420px">
      <div class="modal-header"><div class="modal-title">✅ Tarefa concluída!</div><button class="icon-btn" id="m-x">✕</button></div>
      <div class="modal-body">
        <div style="font-size:14px;color:#a0a0b0;margin-bottom:18px">Deseja repetir <strong style="color:#f0eff5">${esc(t.title)}</strong>?</div>
        <div class="field"><label>Novo prazo</label><input type="date" id="m-rdate" value=""/></div>
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
      const newTask={...t,id:newId,status:"a-fazer",pinned:false,date:newDate||null,createdAt:new Date().toISOString()};
      delete newTask.id;
      await dbSet(`tasks/${newId}`,{...newTask,id:newId});
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


// ── CALENDAR ──────────────────────────────────────────────────────────────────
let calYear=new Date().getFullYear(), calMonth=new Date().getMonth(); // 0-based month
let freelaYear=new Date().getFullYear(), freelaMonth=new Date().getMonth();
let freelaEvents={};

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
  // Task deadlines — only areas user can access
  const myVisibleAreaIds=visibleAreas().map(a=>a.id);
  Object.entries(tasks).forEach(([tid,t])=>{
    if(!t.date)return;
    if(!myVisibleAreaIds.includes(t.areaId))return;
    if(!eventMap[t.date])eventMap[t.date]=[];
    const resps=Array.isArray(t.resps)?t.resps:(t.resp?[t.resp]:[]);
    eventMap[t.date].push({type:"task",id:tid,title:t.title,color:STATUS[t.status]?.color||"#7c6eff",status:t.status,area:areas[t.areaId]?.name||"",resps});
  });
  // Calendar events + freela events (unified)
  const allCalEvents={...calEvents,...freelaEvents};
  Object.entries(allCalEvents).forEach(([eid,e])=>{
    if(!e.dateStart)return;
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
    const ms=new Date(e.dateStart+"T00:00:00").getTime();
    const diffDays=Math.round((ms-nowMs)/86400000);
    if(diffDays>=0&&diffDays<=3)upcoming.push({...e,id:eid,diffDays});
  });
  Object.entries(tasks).forEach(([tid,t])=>{
    if(!t.date||t.status==="concluido")return;
    if(!myVisibleAreaIds.includes(t.areaId))return;
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

  return`<div class="page-header">
    <div><div class="page-title">Calendário</div><div class="page-sub">Prazos, eventos e agendamentos da equipe</div></div>
    <button class="btn-primary" id="btn-new-event">+ Novo Evento</button>
  </div>
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
  // Use setTimeout to ensure DOM is ready after render
  setTimeout(()=>document.getElementById("btn-new-event")?.addEventListener("click",()=>openCalEventModal(null,null)),0);

  // Click on day cell to see events / add event
  document.querySelectorAll(".cal-cell[data-date]").forEach(el=>{
    el.addEventListener("click",e=>{
      if(e.target.classList.contains("cal-event-chip")||e.target.classList.contains("cal-task-count"))return;
      const ds=el.dataset.date; if(!ds)return;
      openCalEventModal(null,ds);
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

function openCalEventModal(eventId, prefillDate, isFreela=false){
  const ev=eventId?(calEvents[eventId]||freelaEvents[eventId]||{}):{}; 
  if(!ev&&eventId){toast("Evento não encontrado","error");return;}
  if(eventId&&!calEvents[eventId]&&freelaEvents[eventId])isFreela=true;
  const orgPersons=Object.values(orgData.nodes||{}).filter(n=>n.name).map(n=>n.name);
  const isEdit=!!eventId;
  openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:500px">
    <div class="modal-header"><div class="modal-title">${isEdit?"Editar":"Novo"} Evento</div><button class="icon-btn" id="m-x">✕</button></div>
    <div class="modal-body">
      <div class="field"><label>Título *</label><input id="m-etitle" value="${esc(ev.title||"")}" placeholder="Nome do evento…" autofocus/></div>
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
    if(!title||!dateStart){toast("Preencha título e data","error");return;}
    const dateEnd=document.getElementById("m-eend").value||null;
    const priority=document.getElementById("m-eprio").value||null;
    const person=document.getElementById("m-eperson").value||null;
    const note=document.getElementById("m-enote").value.trim()||null;
    const useColor=document.getElementById("m-ecolor-use")?.checked;
    const evColor=useColor?(document.getElementById("m-ecolor")?.value||null):null;
    const data={title,dateStart,dateEnd,priority,person,note,color:evColor||null,creatorId:currentUser.uid,creatorName:currentProfile.name,createdAt:ev.createdAt||new Date().toISOString()};
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
  const evs=Object.entries(tasks).filter(([,t])=>t.date===dateStr).map(([id,t])=>({...t,id,type:"task"}));
  const dayFmt=fmtDate(dateStr);
  openModal(`<div class="overlay" id="ov"><div class="modal" style="max-width:480px">
    <div class="modal-header"><div class="modal-title">Tarefas — ${dayFmt}</div><button class="icon-btn" id="m-x">✕</button></div>
    <div class="modal-body">
      ${evs.length===0?`<div style="color:#5a5a6a;text-align:center;padding:20px">Nenhuma tarefa neste dia</div>`
      :evs.map(t=>{
        const st=STATUS[t.status];
        const resps=Array.isArray(t.resps)?t.resps:(t.resp?[t.resp]:[]);
        return`<div style="padding:10px 0;border-bottom:1px solid #1e1e28">
          <div style="display:flex;align-items:center;gap:8px;margin-bottom:4px">
            <span style="width:8px;height:8px;border-radius:50%;background:${st?.color};flex-shrink:0"></span>
            <div style="font-size:13px;font-weight:600">${esc(t.title)}</div>
          </div>
          <div style="display:flex;gap:6px;flex-wrap:wrap">
            <span class="chip" style="background:${st?.color}18;color:${st?.color};border:1px solid ${st?.color}30;font-size:10px">${st?.label}</span>
            ${areas[t.areaId]?`<span class="chip" style="background:#1e1e28;color:#a0a0b0;font-size:10px">${esc(areas[t.areaId].name)}</span>`:""}
            ${resps.map(r=>`<span class="chip" style="background:#7c6eff18;color:#9d93ff;border:1px solid #7c6eff30;font-size:10px">${esc(r)}</span>`).join("")}
          </div>
        </div>`;}).join("")}
    </div>
    <div class="modal-footer"><button class="btn-ghost" id="m-x2">Fechar</button></div>
  </div></div>`);
  document.getElementById("m-x").onclick=document.getElementById("m-x2").onclick=closeModal;
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
let orgStickies={};
let fyiNotes={};
let flowZoom=1, flowPan={x:0,y:0}, flowPanning=false, flowPanStart={x:0,y:0};
let flowStickies={};
let orgExpanded={}; // {nodeId: true/false} — expanded state per group

// ── ORGANOGRAMA ───────────────────────────────────────────────────────────────
function renderOrgPage(){
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
  const svgNodes=nodes.map(n=>{
    const aColor=n.areaName&&areaColors[n.areaName]?areaColors[n.areaName]:n.color||"#7c6eff";
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
      <rect x="0" y="0" width="${nW}" height="${nH}" rx="10" fill="${aColor}18" stroke="${aColor}" stroke-width="${n.parentId?"1.2":"1.8"}"/>
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
    </div>
  </div>`:""}
  <div class="flow-canvas" style="position:relative">
    <div id="org-stickies-layer" style="position:absolute;inset:0;pointer-events:none;z-index:10;overflow:hidden"></div>
    <svg id="org-svg" width="100%" height="650" style="display:block;cursor:${orgConnecting?"crosshair":"default"}">
      <defs>
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
      <span>🖱 Arraste blocos · Shift+clique seleciona mais</span>
      <span>⬜ Arraste no fundo para selecionar vários</span>
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
      if(["org-conn-handle","org-conn-top","org-conn-right","org-del-node","org-edit-node","org-toggle","org-add-child"].some(c=>e.target.classList.contains(c)))return;
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
      if(n)orgDragging={id:el.dataset.nid,ox:e.clientX-r.left-n.x,oy:e.clientY-r.top-n.y};
    });
  });

  svg.addEventListener("mousemove",e=>{
    const r=svg.getBoundingClientRect();
    orgMousePos={x:(e.clientX-r.left-orgPan.x)/orgZoom,y:(e.clientY-r.top-orgPan.y)/orgZoom};
    if(orgGroupDragging){
      const dx=(e.clientX-orgGroupDragging.startClientX)/orgZoom;
      const dy=(e.clientY-orgGroupDragging.startClientY)/orgZoom;
      [...orgSelectedNodes].forEach(id=>{
        const orig=orgGroupDragging.origPos[id];if(!orig)return;
        dbSet(`org/nodes/${id}/x`,Math.max(0,orig.x+dx));
        dbSet(`org/nodes/${id}/y`,Math.max(0,orig.y+dy));
      });
      return;
    }
    if(orgSelBox){
      orgSelBox.x2=(e.clientX-r.left-orgPan.x)/orgZoom;
      orgSelBox.y2=(e.clientY-r.top-orgPan.y)/orgZoom;
      render();return;
    }
    if(orgConnecting){render();return;}
    if(!orgDragging)return;
    dbSet(`org/nodes/${orgDragging.id}/x`,Math.max(0,(e.clientX-r.left-orgPan.x)/orgZoom-orgDragging.ox));
    dbSet(`org/nodes/${orgDragging.id}/y`,Math.max(0,(e.clientY-r.top-orgPan.y)/orgZoom-orgDragging.oy));
  });
  svg.addEventListener("mouseup",()=>{
    if(orgSelBox){
      const x1=Math.min(orgSelBox.x1,orgSelBox.x2), x2=Math.max(orgSelBox.x1,orgSelBox.x2);
      const y1=Math.min(orgSelBox.y1,orgSelBox.y2), y2=Math.max(orgSelBox.y1,orgSelBox.y2);
      if(Math.abs(x2-x1)>8||Math.abs(y2-y1)>8){
        Object.entries(orgData.nodes||{}).forEach(([id,n])=>{
          const W=n.w||160, H=n.h||56;
          if(n.x+W/2>=x1&&n.x+W/2<=x2&&n.y+H/2>=y1&&n.y+H/2<=y2) orgSelectedNodes.add(id);
        });
      }
      orgSelBox=null; render(); return;
    }
    orgDragging=null; orgGroupDragging=null;
  });
  svg.addEventListener("mousedown",e=>{
    if(e.target!==svg&&e.target.getAttribute("fill")!=="url(#org-grid)")return;
    if(orgConnecting)return;
    if(!e.shiftKey) orgSelectedNodes.clear();
    const r=svg.getBoundingClientRect();
    const cx=(e.clientX-r.left-orgPan.x)/orgZoom;
    const cy=(e.clientY-r.top-orgPan.y)/orgZoom;
    orgSelBox={x1:cx,y1:cy,x2:cx,y2:cy};
    render();
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
  document.getElementById("btn-add-org-sticky")?.addEventListener("click",()=>{
    const id=uid();
    dbSet(`org/stickies/${id}`,{id,text:"",color:"#f0a832",x:80+Math.random()*300,y:60+Math.random()*200,expanded:true,createdAt:new Date().toISOString()});
  });
  renderOrgStickies();
}

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
    <div class="field-row">
      <div class="field"><label>Largura</label><input type="number" id="m-ow" value="${n.w||170}" min="80" max="400" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none"/></div>
      <div class="field"><label>Altura</label><input type="number" id="m-oh" value="${n.h||68}" min="32" max="200" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none"/></div>
      <div class="field"><label>Fonte (px)</label><input type="number" id="m-ofsize" value="${n.fsize||12}" min="8" max="28" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none"/></div>
    </div>
    <div class="field">
      <label>Criar nova área e vincular <span style="color:#7a7a8a;font-size:10px">(opcional)</span></label>
      <div style="display:flex;gap:8px">
        <input id="m-onewarea" placeholder="Nome da nova área…" style="flex:1;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none"/>
        <input type="color" id="m-onewareacolor" value="#7c6eff" style="width:38px;height:38px;border:none;background:none;cursor:pointer;border-radius:6px"/>
      </div>
    </div>
    <div class="field"><label>Cargo / Função</label><input id="m-orole" value="${esc(n.role||"")}" placeholder="Ex: Gerente Comercial, Designer…"/></div>
    <div class="field"><label>Área / Departamento</label>
      <select id="m-oarea" style="width:100%;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:8px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none">
        <option value="">Sem área</option>
        ${Object.values(areas).map(a=>`<option value="${esc(a.name)}" ${n.areaName===a.name?"selected":""}>${esc(a.name)}</option>`).join("")}
      </select>
    </div>
    <div class="field"><label>Cor personalizada <span style="color:#7a7a8a;font-size:11px">(usado quando sem área)</span></label>
      <input type="color" id="m-ocolor" value="${n.color||"#7c6eff"}" style="width:40px;height:32px;border:none;background:none;cursor:pointer;border-radius:6px"/>
    </div>
  </div><div class="modal-footer"><button class="btn-ghost" id="m-cancel">Cancelar</button><button class="btn-primary" id="m-save">Salvar</button></div></div></div>`);
  document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;
  document.getElementById("m-save").onclick=async()=>{
    const name=document.getElementById("m-oname").value.trim();
    const role=document.getElementById("m-orole").value.trim();
    const areaName=document.getElementById("m-oarea").value;
    const color=document.getElementById("m-ocolor").value;
    if(!name&&!role){toast("Preencha nome ou cargo","error");return;}
    // Position child near parent
    const px=parentNode?parentNode.x:null, py=parentNode?parentNode.y:null;
    const defaultX=px!=null?px+(Object.values(orgData.nodes||{}).filter(c=>c.parentId===parentId).length*190):80+Math.random()*400;
    const defaultY=py!=null?py+110:60+Math.random()*300;
    const data={...(nodeId?orgData.nodes[nodeId]:{}),name,role,areaName,color,
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
  const userNames=Object.values(users).map(u=>u.name).filter(Boolean);
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
      ${isCreator?`<div style="display:flex;gap:8px">
        <select id="m-resp-sel" style="flex:1;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:7px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none">
          <option value="">Selecionar usu\u00e1rio\u2026</option>
          ${Object.values(users).filter(u=>u.name).map(u=>`<option value="${esc(u.name)}">${esc(u.name)}${u.email?" (" + esc(u.email)+")":""}</option>`).join("")}
        </select>
        <input id="m-resp-manual" placeholder="Ou digitar nome\u2026" style="flex:1;background:#1a1a22;border:1px solid #2e2e3a;border-radius:7px;padding:7px 10px;color:#f0eff5;font-family:inherit;font-size:13px;outline:none"/>
        <button class="btn-small" id="m-resp-add" style="border:1px solid #2e2e3a;color:#c8f04e;white-space:nowrap">+ Add</button>
      </div>`:""}
    </div>
    <div class="field-row">
      <div class="field"><label>Status</label><select id="m-status">${Object.entries(STATUS).map(([k,v])=>`<option value="${k}" ${(init.status||"a-fazer")===k?"selected":""}>${v.label}</option>`).join("")}</select></div>
      <div class="field"><label>Prazo</label><input type="date" id="m-date" value="${init.date||""}"/></div>
    </div>
    ${init.creatorName?`<div style="font-size:11px;color:#5a5a6a;margin-top:4px">\u270f Criada por: ${esc(init.creatorName)}</div>`:""}
    <div class="field" style="display:flex;align-items:center;gap:10px;margin-top:8px">
      <input type="checkbox" id="m-allusers" style="width:16px;height:16px;accent-color:#c8f04e" ${init.allUsers?"checked":""}/>
      <label for="m-allusers" style="font-size:13px;color:#a0a0b0;cursor:pointer">Tarefa coletiva — todos os usuários devem marcar como concluída</label>
    </div>
  </div><div class="modal-footer"><button class="btn-ghost" id="m-cancel">Cancelar</button><button class="btn-primary" id="m-save">Salvar</button></div></div></div>`);

  let selResps=[...existingResps];
  function refreshRespChips(){
    const el=document.getElementById("resp-chips");if(!el)return;
    el.innerHTML=selResps.map(r=>`<span style="background:#7c6eff22;color:#9d93ff;border:1px solid #7c6eff44;padding:4px 10px;border-radius:20px;font-size:12px;${isCreator?"cursor:pointer":""}" data-r="${esc(r)}">${isCreator?"\u2715 ":""}${esc(r)}</span>`).join("")||`<span style="font-size:12px;color:#5a5a6a">Nenhum respons\u00e1vel</span>`;
    if(isCreator) el.querySelectorAll("[data-r]").forEach(ch=>ch.addEventListener("click",()=>{selResps=selResps.filter(r=>r!==ch.dataset.r);refreshRespChips();}));
  }
  refreshRespChips();
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
  }
  document.getElementById("m-x").onclick=document.getElementById("m-cancel").onclick=closeModal;
  document.getElementById("m-save").onclick=async()=>{
    const title=document.getElementById("m-title").value.trim();
    if(!title){toast("Digite um t\u00edtulo","error");return;}
    const isEdit=!!init.id;
    const respsToSave=isCreator?selResps:(init.resps||[]);
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

function openDetailModal(taskId){
  const t={id:taskId,...tasks[taskId]};if(!t.title)return;
  const area=areas[t.areaId],st=STATUS[t.status];
  const resps=Array.isArray(t.resps)?t.resps:(t.resp?[t.resp]:[]);
  const canPin=isAdmin();
  const canDelete=isAdmin()||(t.creatorId===currentUser?.uid);
  const priorityChip=t.priority?'<span class="chip" style="background:'+PRIORITY[t.priority].color+'18;color:'+PRIORITY[t.priority].color+';border:1px solid '+PRIORITY[t.priority].color+'30;padding:4px 12px;text-transform:capitalize">'+t.priority+'</span>':"";
  const areaChip=area?'<span class="chip" style="background:'+area.color+'18;color:'+area.color+';border:1px solid '+area.color+'30;padding:4px 12px">'+esc(area.name)+'</span>':"";
  const descBlock=t.desc?'<div style="font-size:13px;color:#a0a0b0;line-height:1.6;background:#18181c;padding:12px;border-radius:8px;margin-bottom:14px">'+esc(t.desc)+'</div>':"";
  const respBlock=resps.length?'<div style="margin-bottom:12px"><div style="font-size:10px;color:#7a7a8a;text-transform:uppercase;letter-spacing:1px;margin-bottom:6px">Responsaveis</div><div style="display:flex;gap:6px;flex-wrap:wrap">'+resps.map(r=>'<span style="background:#7c6eff18;color:#9d93ff;border:1px solid #7c6eff30;padding:4px 12px;border-radius:20px;font-size:12px">'+esc(r)+'</span>').join("")+'</div></div>':"";
  const dateBlock=t.date?'<div><div style="font-size:10px;color:#7a7a8a;text-transform:uppercase;letter-spacing:1px;margin-bottom:3px">Prazo</div><div>'+fmtDate(t.date)+'</div></div>':"";
  const creatorBlock=t.creatorName?'<div style="font-size:11px;color:#5a5a6a;margin-top:10px;padding-top:10px;border-top:1px solid #1e1e28">Criada por: '+esc(t.creatorName)+'</div>':"";
  const statusBtns=Object.entries(STATUS).map(([k,v])=>{
    const sel=t.status===k;
    const s=sel?'background:'+v.color+'22;color:'+v.color+';border:1px solid '+v.color+'60':'border:1px solid #2e2e3a;color:#7a7a8a';
    return'<button class="btn-small move-status" data-status="'+k+'" style="'+s+'">'+v.label+'</button>';
  }).join("");
  const pinLabel=t.pinned?'Fixada (desfixar)':'Fixar tarefa';
  const delAttrs=t.pinned?'disabled title="Desfixe antes de excluir"':"";
  const delLabel=t.pinned?'Fixada':'Excluir';
  const pinTitlePrefix=t.pinned?'[Fixada] ':'';
  const collectiveBlock=t.allUsers&&resps.length?`<div style="margin-bottom:14px;background:#1a1a22;border:1px solid #2e2e3a;border-radius:8px;padding:10px 14px">
    <div style="font-size:10px;color:#7a7a8a;text-transform:uppercase;letter-spacing:1px;margin-bottom:8px">⚙ Tarefa coletiva — progresso</div>
    ${Object.entries(users).filter(([,u])=>resps.includes(u.name)).map(([uid2,u])=>{
      const done=!!(t.completions||{})[uid2];
      return`<div style="display:flex;align-items:center;gap:8px;margin-bottom:4px">
        <span style="width:14px;height:14px;border-radius:50%;background:${done?"#c8f04e":"#1e1e28"};border:2px solid ${done?"#c8f04e":"#3e3e4a"};flex-shrink:0"></span>
        <span style="font-size:12px;color:${done?"#c8f04e":"#a0a0b0"}">${esc(u.name)}${done?" ✓":""}</span>
      </div>`;}).join("")}
  </div>`:"";
  const pinBtn=canPin?'<button id="m-pin" class="btn-small" style="border:1px solid '+(t.pinned?'#c8f04e':'#2e2e3a')+';color:'+(t.pinned?'#c8f04e':'#7a7a8a')+'">'+pinLabel+'</button>':"";
  openModal('<div class="overlay" id="ov"><div class="modal"><div class="modal-header"><div class="modal-title">'+pinTitlePrefix+'Detalhe</div><button class="icon-btn" id="m-x">X</button></div><div class="modal-body"><div style="font-family:\'Syne\',sans-serif;font-size:18px;font-weight:700;line-height:1.3;margin-bottom:10px">'+esc(t.title)+'</div><div style="display:flex;gap:8px;flex-wrap:wrap;margin-bottom:14px"><span class="chip" style="background:'+st.color+'22;color:'+st.color+';border:1px solid '+st.color+'40;padding:4px 12px">'+st.label+'</span>'+priorityChip+areaChip+deadlineBadge(t.date)+'</div>'+collectiveBlock+descBlock+respBlock+'<div style="display:grid;grid-template-columns:1fr 1fr;gap:12px;margin-bottom:16px">'+dateBlock+'</div><div><div style="font-size:10px;color:#7a7a8a;text-transform:uppercase;letter-spacing:1px;margin-bottom:8px">Mover para</div><div style="display:flex;gap:6px;flex-wrap:wrap">'+statusBtns+'</div></div>'+creatorBlock+'</div><div class="modal-footer">'+pinBtn+(canDelete?'<button class="btn-danger" id="m-del" '+delAttrs+'>'+delLabel+'</button>':"")+'<button class="btn-ghost" id="m-x2">Fechar</button><button class="btn-primary" id="m-edit">Editar</button></div></div></div>');
  document.getElementById("m-x").onclick=document.getElementById("m-x2").onclick=closeModal;
  document.getElementById("m-edit").onclick=()=>{closeModal();openTaskModal({...t});};
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
    if(t.allUsers){
      // For collective tasks, use markUserCompletion instead of direct status change
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
  toast("Gerando backup…","success");
  const backup={
    exportedAt:new Date().toISOString(),
    areas,tasks,notes,users:Object.fromEntries(Object.entries(users).map(([id,u])=>[id,{...u}])),
    flowData,orgData,calEvents,freelaEvents,flowStickies,orgStickies,fyiNotes,
    // personal notes and area notes are per-user/area — include what's in memory
    areaNotes,personalNotes,auditLog
  };
  const blob=new Blob([JSON.stringify(backup,null,2)],{type:"application/json"});
  const a=document.createElement("a");
  a.href=URL.createObjectURL(blob);
  a.download=`mineirart-backup-${new Date().toISOString().slice(0,10)}.json`;
  a.click(); URL.revokeObjectURL(a.href);
  await logAction("backup","Backup completo exportado");
  toast("Backup completo baixado!","success");
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
  onValue(dbRef(`user_notifs/${currentUser.uid}`),snap=>{
    const notifs=snap.val()||{};
    userNotifsUnread=Object.values(notifs).filter(n=>!n.read).length;
    // Show banners for unread
    Object.entries(notifs).filter(([,n])=>!n.read).forEach(([nid,n])=>{
      showCalBanner(n.msg,"#c8f04e","Atualização");
      dbSet(`user_notifs/${currentUser.uid}/${nid}/read`,true);
    });
    render();
  });
}



// ── BLOCK NOTES EDITOR ────────────────────────────────────────────────────────
// Replaces the old note card system with an inline block editor per area
// Each "note" is now a doc with an array of blocks: {id, type:'text'|'toggle', text, done?, color?}

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
      const isOpen=b.open!==false; // default open
      const children=(b.children||[]);
      const childrenHtml=children.map(c=>`<div style="display:flex;align-items:center;gap:8px;padding:3px 0;margin-left:28px">
        <span contenteditable="true" data-bid="${b.id}" data-cid="${c.id}" class="toggle-child-text" spellcheck="false" style="flex:1;font-size:13px;color:${c.color||"#a0a0b0"};outline:none;word-break:break-word;line-height:1.6;min-height:16px">${esc(c.text||"")}</span>
        <button class="toggle-child-del" data-bid="${b.id}" data-cid="${c.id}" style="opacity:0;background:none;border:none;color:#ff6b6b;cursor:pointer;font-size:13px;padding:0;transition:opacity .15s" title="Remover">✕</button>
      </div>`).join("");
      const childInput=isOpen?`<div style="margin-left:28px;margin-top:4px">
        <input class="toggle-add-child" data-bid="${b.id}" placeholder="Adicionar item…" style="width:100%;box-sizing:border-box;background:transparent;border:none;border-bottom:1px dashed #2e2e3a;color:#7a7a8a;font-family:'DM Sans',sans-serif;font-size:12px;padding:4px 2px;outline:none"/>
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
      <span contenteditable="true" data-bid="${b.id}" class="block-text" spellcheck="false" style="flex:1;font-size:13px;color:${color};outline:none;word-break:break-word;line-height:1.7;min-height:18px">${esc(b.text||"")}</span>
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

  // Add child to toggle via Enter on the add-child input
  document.querySelectorAll(".toggle-add-child").forEach(inp2=>{
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
  document.querySelectorAll(".toggle-child-text").forEach(el=>{
    el.addEventListener("blur",async()=>{
      const bid=el.dataset.bid, cid=el.dataset.cid;
      const newText=el.innerText.trim();
      blocks=blocks.map(b=>b.id===bid?{...b,children:(b.children||[]).map(c=>c.id===cid?{...c,text:newText}:c)}:b);
      await saveBlocks();
    });
    el.addEventListener("keydown",e=>{if(e.key==="Enter"){e.preventDefault();el.blur();}});
  });

  // Delete child
  document.querySelectorAll(".toggle-child-del").forEach(btn=>{
    btn.addEventListener("click",async()=>{
      const bid=btn.dataset.bid, cid=btn.dataset.cid;
      blocks=blocks.map(b=>b.id===bid?{...b,children:(b.children||[]).filter(c=>c.id!==cid)}:b);
      await saveBlocks();
    });
  });

  // Hover on child rows
  document.querySelectorAll(".toggle-child-del").forEach(btn=>{
    const row=btn.parentElement;
    row?.addEventListener("mouseenter",()=>btn.style.opacity="1");
    row?.addEventListener("mouseleave",()=>btn.style.opacity="0");
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
