/* Plotline: walk a cemetery section and see who is around you.
   Graves are public data; relationships are worked out live for whoever signs in with Geni,
   from their own account, in their own browser. */
(() => {
  "use strict";

  const CONFIG = window.KIN_CONFIG || {};
  const KINDS = {
    direct: { label: "Direct line", css: "--direct" },
    blood: { label: "Blood relative", css: "--blood" },
    inlaw: { label: "Through marriage", css: "--inlaw" },
    none: { label: "Not connected", css: "--none" },
    unknown: { label: "Not worked out yet", css: "--unknown" },
  };
  const STEP_M = 1.5;          // one arrow-key step
  const FAR_M = 600;           // further than this from the section = "not here"
  const LABEL_ZOOM = 20;       // show names on the map from this zoom
  const GENI_GAP_MS = 10500;   // Geni allows about one request per 10 s
  const CACHE_DAYS = 30;

  const $ = (s) => document.querySelector(s);
  const store = {
    get(k, d) { try { return localStorage.getItem(k) ?? d; } catch { return d; } },
    set(k, v) { try { localStorage.setItem(k, v); } catch { /* private mode */ } },
    del(k) { try { localStorage.removeItem(k); } catch { /* private mode */ } },
  };
  const cssVar = (name) => getComputedStyle(document.documentElement).getPropertyValue(name).trim();
  const esc = (s) => String(s ?? "").replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));

  /* ---------- geometry ---------- */
  const rad = (d) => (d * Math.PI) / 180;
  function dist(a, b) {
    const dLat = rad(b[0] - a[0]), dLon = rad(b[1] - a[1]);
    const h = Math.sin(dLat / 2) ** 2 + Math.cos(rad(a[0])) * Math.cos(rad(b[0])) * Math.sin(dLon / 2) ** 2;
    return 2 * 6371000 * Math.asin(Math.sqrt(h));
  }
  function bearing(a, b) {
    const y = Math.sin(rad(b[1] - a[1])) * Math.cos(rad(b[0]));
    const x = Math.cos(rad(a[0])) * Math.sin(rad(b[0])) - Math.sin(rad(a[0])) * Math.cos(rad(b[0])) * Math.cos(rad(b[1] - a[1]));
    return ((Math.atan2(y, x) * 180) / Math.PI + 360) % 360;
  }
  const move = (p, northM, eastM) => [p[0] + northM / 111320, p[1] + eastM / (111320 * Math.cos(rad(p[0])))];
  const compass = (b) => ["N", "NE", "E", "SE", "S", "SW", "W", "NW"][Math.round(b / 45) % 8];

  /* ---------- state ---------- */
  const state = {
    sections: [], section: null, graves: [], me: null, mode: "explore", heading: null,
    radius: Number(store.get("radius", "30")), units: store.get("units", "ft"),
    hidden: new Set(JSON.parse(store.get("hiddenKinds", "[]"))),
    selected: null, follow: true, watchId: null, lastFix: null,
  };
  // Geni sign-in and this visitor's relationships (kept only in this browser).
  const geni = { token: null, expires: 0, user: null, rels: {}, busy: false, paused: false, nextAt: 0, error: "" };

  function fmt(m) {
    if (state.units === "ft") {
      const ft = m * 3.28084;
      return ft < 1000 ? `${Math.round(ft)} ft` : `${(m / 1609.34).toFixed(1)} mi`;
    }
    return m < 1000 ? `${Math.round(m)} m` : `${(m / 1000).toFixed(1)} km`;
  }
  const radiusLabel = (r) => (state.units === "ft" ? `${Math.round(r * 3.28084 / 5) * 5} ft` : `${r} m`);
  const relOf = (g) => geni.rels[g.id];
  // A blood line this close still counts as family, even when a shorter route runs through a marriage.
  const BLOOD_COUSIN_LIMIT = 8;
  const ORDINALS = ["first", "second", "third", "fourth", "fifth", "sixth", "seventh", "eighth", "ninth", "tenth",
    "eleventh", "twelfth", "thirteenth", "fourteenth", "fifteenth", "sixteenth", "seventeenth", "eighteenth", "nineteenth", "twentieth"];
  function cousinDegree(text) {
    const m = /(\w+)\s+cousin/i.exec(text || "");
    if (!m) return 0; // uncle, niece, sibling…: closer than any cousin
    const n = parseInt(m[1], 10);
    return n || ORDINALS.indexOf(m[1].toLowerCase()) + 1 || 99;
  }
  // The blood line kept alongside an in-law answer, if it's close enough to count.
  const closeBlood = (r) => (r?.kind === "inlaw" && r.also && r.also.kind !== "inlaw"
    && cousinDegree(r.also.relationship) <= BLOOD_COUSIN_LIMIT) ? r.also : null;
  const kindOf = (g) => {
    const r = relOf(g);
    if (!r || r.status === "pending") return "unknown";
    return closeBlood(r) ? "blood" : r.kind;
  };

  /* ---------- Geni: sign-in ---------- */
  const redirectUri = () => location.origin + location.pathname;

  // Geni may send the token as "#access_token=..." or percent-encoded as "#access_token%3D...%26...",
  // and possibly in the query string; accept any of them.
  function signInParams() {
    for (let raw of [location.hash.slice(1), location.search.slice(1)]) {
      if (!raw) continue;
      if (!raw.includes("=") || /access_token%3D|status%3D/i.test(raw)) {
        try { raw = decodeURIComponent(raw); } catch { /* keep as is */ }
      }
      const p = new URLSearchParams(raw.replace(/^[#?]/, ""));
      if (p.get("access_token") || p.get("status")) return p;
    }
    return new URLSearchParams();
  }

  function readSignIn() {
    const h = signInParams();
    if (h.get("access_token")) {
      geni.token = h.get("access_token");
      geni.expires = Date.now() + (Number(h.get("expires_in")) || 86400) * 1000 - 60000;
      store.set("geniToken", JSON.stringify({ token: geni.token, expires: geni.expires }));
      history.replaceState(null, "", location.pathname + store.get("returnHash", ""));
      store.del("returnHash");
      return "new";
    }
    if (h.get("status") === "unauthorized") {
      history.replaceState(null, "", location.pathname + store.get("returnHash", ""));
      store.del("returnHash");
      return "declined";
    }
    try {
      const saved = JSON.parse(store.get("geniToken", "null"));
      if (saved && saved.expires > Date.now()) {
        Object.assign(geni, saved);
        if (geni.user) loadRels();
      }
    } catch { /* ignore */ }
    return geni.token ? "saved" : "none";
  }

  function signIn() {
    if (!CONFIG.geniAppKey) return toast("Geni sign-in isn't set up for this site yet.");
    store.set("returnHash", location.hash);
    const q = new URLSearchParams({ client_id: CONFIG.geniAppKey, redirect_uri: redirectUri(), response_type: "token", display: "web" });
    location.href = `https://www.geni.com/platform/oauth/authorize?${q}`;
  }

  function signOut() {
    store.del("geniToken");
    if (geni.user) store.del(`rels:${geni.user.id}`);
    Object.assign(geni, { token: null, expires: 0, user: null, rels: {}, error: "" });
    drawGraves();
    render();
    toast("Signed out. Your relationships were cleared from this browser.");
  }

  /* ---------- Geni: API calls (JSONP, which Geni supports for other websites) ---------- */
  let seq = 0;
  function jsonp(path, params) {
    return new Promise((resolve, reject) => {
      const name = `__kin${Date.now().toString(36)}${++seq}`;
      const script = document.createElement("script");
      const timer = setTimeout(() => finish(new Error("timeout")), 30000);
      function finish(err, data) {
        clearTimeout(timer);
        window[name] = () => {};   // a late reply must not throw
        script.remove();
        err ? reject(err) : resolve(data);
      }
      window[name] = (data) => finish(null, data);
      script.onerror = () => finish(new Error("network"));
      const q = new URLSearchParams({ ...params, access_token: geni.token, callback: name });
      script.src = `https://www.geni.com/api/${path}?${q}`;
      document.head.appendChild(script);
    });
  }

  const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
  // Geni allows about one request per 10 s, apparently per person across all their apps. When it
  // refuses (a rate-limited JSONP reply fails to load) we back off further each time and keep going.
  async function api(path, params = {}) {
    for (let fails = 0; ; ) {
      while (geni.paused) await sleep(1000);
      const wait = geni.nextAt - Date.now();
      if (wait > 0) await sleep(wait);
      if (!geni.token) { const e = new Error("signed out"); e.auth = true; throw e; }
      geni.nextAt = Date.now() + GENI_GAP_MS;
      let data = null;
      try { data = await jsonp(path, params); } catch { /* busy or offline */ }
      const msg = (data && (data.error?.message || (!data.id && !data.relations && !data.status && data.message))) || "";
      if (data && /token|oauth|authoriz/i.test(msg)) { const e = new Error(msg); e.auth = true; throw e; }
      if (data && !/rate limit/i.test(msg)) {
        if (geni.notice) { geni.notice = ""; render(); }
        return data;
      }
      fails += 1;
      const backoff = Math.min(120000, GENI_GAP_MS * 2 ** Math.min(fails, 4));
      geni.nextAt = Date.now() + backoff;
      geni.notice = navigator.onLine === false
        ? "You're offline. Waiting for a connection…"
        : `Geni asked us to slow down. Trying again in ${Math.round(backoff / 1000)} s.`;
      render();
    }
  }

  async function pathTo(g, extra) {
    const r = await api(`${geni.user.id}/path-to/${g.id}`, { skip_email: "true", skip_notify: "true", ...extra });
    if (r.status !== "done" || !r.relations?.length) return { status: r.status || "not found" };
    const chain = r.relations.map((x) => ({ name: x.name || "", relation: x.relation || "" }));
    return { status: "done", relationship: r.relationship || "", steps: r.step_count || chain.length - 1, inlaw: !!r.inlaw_distance, chain };
  }

  function classify(p) {
    const rels = p.chain.slice(1).map((c) => c.relation);
    if (rels.length && rels.every((r) => r === "father" || r === "mother")) return "direct";
    return p.inlaw ? "inlaw" : "blood";
  }

  // Geni's default path can be a roundabout in-law route even when a blood line exists, so an
  // in-law answer is checked against the blood-only path; the shorter-ish one leads.
  async function resolve(g) {
    if (g.id === geni.user.id) return { status: "done", kind: "direct", relationship: "you", chain: [], at: Date.now() };
    const closest = await pathTo(g, {});
    if (closest.status === "pending") return { status: "pending", tries: (relOf(g)?.tries || 0) + 1, retryAt: Date.now() + 25000 };
    let main = closest, also = null;
    if (closest.status !== "done" || closest.inlaw) {
      const blood = await pathTo(g, { path_type: "blood" });
      if (blood.status === "done" && (closest.status !== "done" || blood.steps <= closest.steps + 2)) {
        main = blood; also = closest.status === "done" ? closest : null;
      } else if (blood.status === "done") {
        also = blood;
      }
    }
    if (main.status !== "done") return { status: "done", kind: "none", relationship: "", chain: [], at: Date.now() };
    if (also && also.relationship === main.relationship) also = null;
    return { status: "done", kind: classify(main), relationship: main.relationship, steps: main.steps, chain: main.chain,
             also: also && { relationship: also.relationship, chain: also.chain, steps: also.steps, kind: classify(also) },
             at: Date.now() };
  }

  function saveRels() {
    if (geni.user) store.set(`rels:${geni.user.id}`, JSON.stringify(geni.rels));
  }
  function loadRels() {
    try {
      const all = JSON.parse(store.get(`rels:${geni.user.id}`, "{}"));
      const fresh = Date.now() - CACHE_DAYS * 864e5;
      geni.rels = Object.fromEntries(Object.entries(all).filter(([, r]) => r.status === "done" && r.at > fresh));
    } catch { geni.rels = {}; }
  }

  // Only one Plotline tab per browser asks Geni at a time; others pick up its results.
  const TAB = Math.random().toString(36).slice(2);
  function takeLock() {
    try {
      const l = JSON.parse(store.get("geniLock", "null"));
      if (l && l.tab !== TAB && Date.now() - l.at < 25000) return false;
    } catch { /* take it */ }
    store.set("geniLock", JSON.stringify({ tab: TAB, at: Date.now() }));
    return true;
  }
  function dropLock() {
    try { if (JSON.parse(store.get("geniLock", "null"))?.tab === TAB) store.del("geniLock"); } catch { /* ignore */ }
  }
  window.addEventListener("pagehide", dropLock);
  window.addEventListener("storage", (e) => {
    if (geni.user && e.key === `rels:${geni.user.id}`) { loadRels(); drawGraves(); render(); }
  });

  function nextGrave() {
    const now = Date.now();
    const open = state.graves.filter((g) => {
      const r = relOf(g);
      return !r || (r.status === "pending" && r.tries < 5 && r.retryAt <= now);
    });
    if (!open.length) return null;
    const first = open.find((g) => g.id === geni.priority);
    if (first) { geni.priority = null; return first; }
    const here = state.me || state.section?.centre;
    return open.reduce((best, g) => (dist(here, g.gps) < dist(here, best.gps) ? g : best));
  }

  async function startGeni(kind) {
    if (!geni.token) return render();
    try {
      if (!geni.user) {
        geni.busy = true;
        render();
        const u = await api("profile", { fields: "id,name" });
        if (!u.id) throw new Error("Geni didn't return your profile.");
        geni.user = { id: u.id, name: u.name || "you" };
        // Remember who this is, so a reload shows saved answers at once instead of waiting on Geni.
        store.set("geniToken", JSON.stringify({ token: geni.token, expires: geni.expires, user: geni.user }));
        if (kind === "new") toast(`Signed in as ${geni.user.name}.`);
      }
      loadRels();
      drawGraves();
      work();
    } catch (e) {
      geni.busy = false;
      if (e.auth) { signOut(); toast("Your Geni sign-in has expired. Please sign in again."); }
      else { geni.error = e.message; render(); }
    }
  }

  async function work() {
    if (geni.busy && geni.working) return;
    geni.working = geni.busy = true;
    geni.error = "";
    render();
    const heartbeat = setInterval(() => {
      try { if (JSON.parse(store.get("geniLock", "null"))?.tab === TAB) store.set("geniLock", JSON.stringify({ tab: TAB, at: Date.now() })); } catch { /* ignore */ }
    }, 5000);
    try {
      while (geni.token && geni.user && !geni.paused) {
        if (!takeLock()) {
          geni.notice = "Another Plotline tab or window in this browser is asking Geni. Its results show up here too.";
          render();
          await sleep(5000);
          loadRels();
          drawGraves();
          if (state.graves.every((x) => relOf(x)?.status === "done")) break;
          continue;
        }
        const g = nextGrave();
        if (!g) {
          const waiting = state.graves.some((x) => relOf(x)?.status === "pending" && relOf(x).tries < 5);
          if (!waiting) break;
          await sleep(3000);
          continue;
        }
        geni.current = g.id;
        render();
        const user = geni.user;
        const rel = await resolve(g);
        if (geni.user !== user) break;   // signed out (or switched) while Geni was answering
        geni.rels[g.id] = rel;
        saveRels();
        drawGraves();
        render();
      }
    } catch (e) {
      if (e.auth) {
        clearInterval(heartbeat); dropLock();
        geni.working = geni.busy = false;
        if (geni.token) { signOut(); toast("Your Geni sign-in has expired. Please sign in again."); }
        return;
      }
      if (geni.user) geni.error = e.message;
    }
    clearInterval(heartbeat);
    geni.current = null;
    geni.notice = "";
    geni.working = geni.busy = false;
    dropLock();
    render();
  }

  /* ---------- map ---------- */
  const map = L.map("map", { zoomControl: false, maxZoom: 22, zoomSnap: 0.5 }).setView([41.8649, -87.9125], 19);
  L.control.zoom({ position: "topleft" }).addTo(map);
  const satellite = L.tileLayer("https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}", {
    maxNativeZoom: 19, maxZoom: 22, attribution: "Imagery © Esri, Maxar, Earthstar Geographics",
  });
  const street = L.tileLayer("https://tile.openstreetmap.org/{z}/{x}/{y}.png", {
    maxNativeZoom: 19, maxZoom: 22, attribution: "© OpenStreetMap contributors",
  });
  (store.get("base", "satellite") === "street" ? street : satellite).addTo(map);
  L.control.layers({ Satellite: satellite, "Street map": street }, null, { position: "topright" }).addTo(map);
  map.on("baselayerchange", (e) => store.set("base", e.layer === street ? "street" : "satellite"));

  const graveLayer = L.layerGroup().addTo(map);
  const meIcon = L.divIcon({ className: "", html: '<div class="me"><div class="pulse"></div><div class="cone"></div><div class="dot"></div></div>', iconSize: [28, 28], iconAnchor: [14, 14] });
  const meMarker = L.marker([0, 0], { icon: meIcon, draggable: true, keyboard: false, zIndexOffset: 1000 });
  const accuracy = L.circle([0, 0], { radius: 1, color: "#2f7df6", weight: 1, fillOpacity: 0.08, interactive: false });
  const ring = L.circle([0, 0], { radius: 30, color: "#ffffff", weight: 1.5, dashArray: "4 6", fill: false, interactive: false });
  const line = L.polyline([], { color: "#ffffff", weight: 2.5, dashArray: "2 7", interactive: false });

  meMarker.on("drag", (e) => setMe([e.latlng.lat, e.latlng.lng], { pan: false }));
  map.on("click", (e) => {
    if (state.mode !== "explore") return;
    const prev = state.me;
    setMe([e.latlng.lat, e.latlng.lng], { pan: false });
    if (prev) setHeading(bearing(prev, state.me));
  });
  map.on("dragstart", () => { if (state.mode === "live") state.follow = false; });
  map.on("zoomend", drawGraves);

  /* ---------- data ---------- */
  async function getJSON(url) {
    const r = await fetch(url, { cache: "no-cache" });
    if (!r.ok) throw new Error(`${url}: ${r.status}`);
    return r.json();
  }

  async function init() {
    const signIn = readSignIn();
    if (signIn === "declined") toast("Geni sign-in was cancelled.");
    try {
      state.sections = await getJSON("data/sections.json");
    } catch (e) {
      $("#panelBody").innerHTML = `<p class="pad">Couldn't load the section list. ${esc(e.message)}</p>`;
      return;
    }
    const sel = $("#section");
    sel.innerHTML = state.sections.map((s) => `<option value="${esc(s.id)}">${esc(s.cemetery)} · ${esc(s.short)}</option>`).join("");
    const hash = readHash();
    const first = state.sections.find((s) => s.id === hash.s) || state.sections[0];
    sel.value = first.id;
    sel.addEventListener("change", () => loadSection(sel.value, null));
    await loadSection(first.id, hash.at);
    if (hash.z) map.setZoom(hash.z);
    startGeni(signIn);
  }

  async function loadSection(id, at) {
    const meta = state.sections.find((s) => s.id === id);
    let data;
    try {
      data = await getJSON(meta.file);
    } catch (e) {
      $("#panelBody").innerHTML = `<p class="pad">Couldn't load ${esc(meta.short)}. ${esc(e.message)}</p>`;
      return;
    }
    state.section = data;
    state.selected = null;
    // Graves that share one lot point are spread into a small ring so each can be tapped.
    const groups = {};
    data.graves.filter((g) => g.gps).forEach((g) => { (groups[g.gps.map((v) => v.toFixed(6)).join()] ||= []).push(g); });
    state.graves = [];
    Object.values(groups).forEach((list) => {
      list.forEach((g, i) => {
        const a = (2 * Math.PI * i) / list.length;
        g.pos = list.length > 1 ? move(g.gps, Math.cos(a) * 1.4, Math.sin(a) * 1.4) : g.gps;
        g.lotmates = list.filter((o) => o !== g).map((o) => o.name);
        state.graves.push(g);
      });
    });
    drawGraves();
    const centre = data.centre || state.graves[0]?.gps;
    if (state.mode === "explore" || !state.me) setMe(at || move(centre, -18, 0), { pan: true, zoom: 19.5 });
    else render();
    if (geni.user) work();
  }

  /* ---------- drawing ---------- */
  function drawGraves() {
    graveLayer.clearLayers();
    const labels = map.getZoom() >= LABEL_ZOOM;
    state.graves.forEach((g) => {
      const k = kindOf(g);
      const on = !state.hidden.has(k);
      const sel = state.selected === g;
      const m = L.circleMarker(g.pos, {
        radius: sel ? 11 : 8, color: sel ? "#2f7df6" : "#ffffff", weight: sel ? 3.5 : 2,
        fillColor: cssVar(KINDS[k].css), fillOpacity: on ? 1 : 0.25, opacity: on ? 1 : 0.4,
      });
      m.bindTooltip(esc(g.name), { className: "name", direction: "top", offset: [0, -8], permanent: labels && on });
      m.on("click", (e) => { L.DomEvent.stopPropagation(e); select(g); });
      m.addTo(graveLayer);
    });
  }

  function setMe(p, opts = {}) {
    state.me = p;
    meMarker.setLatLng(p);
    if (!map.hasLayer(meMarker)) meMarker.addTo(map);
    ring.setLatLng(p).setRadius(state.radius || 1);
    if (state.radius && !map.hasLayer(ring)) ring.addTo(map);
    if (!state.radius && map.hasLayer(ring)) ring.remove();
    if (opts.pan) map.setView(p, opts.zoom || map.getZoom(), { animate: false });
    else if (state.mode === "live" && state.follow) map.panTo(p, { animate: true });
    if (state.mode === "explore") writeHash();
    scheduleRender();
  }

  function setHeading(deg) {
    state.heading = deg;
    const el = meMarker.getElement()?.querySelector(".me");
    if (!el) return;
    el.classList.toggle("has-heading", deg != null);
    const cone = el.querySelector(".cone");
    if (cone && deg != null) cone.style.transform = `rotate(${deg}deg)`;
  }

  let renderQueued = false;
  function scheduleRender() {
    if (renderQueued) return;
    renderQueued = true;
    requestAnimationFrame(() => { renderQueued = false; render(); });
  }

  /* ---------- panel ---------- */
  const arrowSvg = (deg) => `<svg class="arrow" viewBox="0 0 16 16" style="transform:rotate(${deg}deg)" aria-hidden="true"><path d="M8 1l5 13-5-3-5 3z" fill="currentColor"/></svg>`;
  const swatch = (k) => `<span class="sw" style="background:var(${KINDS[k].css})"></span>`;

  function render() {
    if (!state.section || !state.me) return;
    updateLine();
    if (state.selected) return renderDetail(state.selected);
    renderList();
  }

  function geniCard() {
    if (!geni.token) {
      return `<div class="signin">
        <div><b>How are you related to them?</b><br><span class="muted">Sign in with your Geni account and this page asks Geni how you're connected to each person here. It all stays in your browser.</span></div>
        <button type="button" class="btn" data-act="signin" ${CONFIG.geniAppKey ? "" : "disabled"}>Sign in with Geni</button></div>`;
    }
    if (!geni.user) return `<div class="signin"><span class="muted">${geni.error ? esc(geni.error) : "Connecting to Geni…"}</span></div>`;
    const total = state.graves.length;
    const done = state.graves.filter((g) => relOf(g)?.status === "done").length;
    if (done >= total && !geni.busy) return "";
    const left = total - done;
    const mins = Math.max(1, Math.round((left * 1.4 * GENI_GAP_MS) / 60000));
    const cur = state.graves.find((g) => g.id === geni.current);
    return `<div class="signin progress">
      <div><b>Working out your relationships · ${done} of ${total}</b>
        <span class="muted">${geni.paused ? "Paused." : geni.notice ? esc(geni.notice) : geni.error ? esc(geni.error) : `Nearest first. About ${mins} min left${cur ? ` · asking about ${esc(cur.name)}` : ""}.`}</span>
        <div class="bar-track"><div class="bar-fill" style="width:${Math.round((done / total) * 100)}%"></div></div></div>
      <button type="button" class="btn secondary" data-act="${geni.paused ? "resume" : "pause"}">${geni.paused ? "Resume" : "Pause"}</button></div>`;
  }

  function renderList() {
    const me = state.me;
    const all = state.graves.map((g) => ({ g, k: kindOf(g), d: dist(me, g.gps), b: bearing(me, g.gps) })).sort((a, b) => a.d - b.d);
    const shown = all.filter((x) => !state.hidden.has(x.k));
    const near = state.radius ? shown.filter((x) => x.d <= state.radius) : shown;
    const rest = state.radius ? shown.filter((x) => x.d > state.radius) : [];
    const sec = state.sections.find((s) => s.id === state.section.id) || {};
    const fromCentre = state.section.centre ? dist(me, state.section.centre) : 0;
    const closestKin = all.find((x) => x.k === "direct" || x.k === "blood");

    let html = "";
    if (fromCentre > FAR_M) {
      html += `<div class="notice">You're <b>${fmt(fromCentre)}</b> from ${esc(sec.short || "the section")}.
        ${state.mode === "live" ? "Walk it virtually instead?" : ""}
        <br><button type="button" data-act="jump">${state.mode === "live" ? "Explore the section" : "Go to the section"}</button></div>`;
    }
    html += geniCard();
    html += `<div class="head"><h2>${near.length ? `${near.length} around you` : "No one right here"}</h2>
      <p>${state.radius ? `within ${radiusLabel(state.radius)}` : "everyone in the section"}${closestKin && fromCentre <= FAR_M ? ` · closest kin: ${esc(closestKin.g.name)}, ${fmt(closestKin.d)} ${compass(closestKin.b)}` : ""}</p></div>`;
    const counts = {};
    all.forEach((x) => { counts[x.k] = (counts[x.k] || 0) + 1; });
    const chips = Object.keys(KINDS).filter((k) => counts[k]);
    html += `<div class="tools">${chips.length > 1 ? chips.map((k) =>
      `<button type="button" class="chip ${state.hidden.has(k) ? "off" : "on"}" data-kind="${k}" aria-pressed="${!state.hidden.has(k)}">${swatch(k)}${KINDS[k].label} ${counts[k]}</button>`).join("") : ""}
      <label class="radius">Range <select data-act="radius">${[10, 20, 30, 50, 100, 0].map((r) =>
        `<option value="${r}" ${r === state.radius ? "selected" : ""}>${r ? radiusLabel(r) : "All"}</option>`).join("")}</select></label></div>`;
    html += `<ul class="list">${near.map(row).join("")}</ul>`;
    if (rest.length) html += `<div class="sep">Further away</div><ul class="list">${rest.map(row).join("")}</ul>`;
    if (!shown.length) html += `<p class="pad muted">Nobody matches the filters above.</p>`;
    html += `<div class="foot">Grave locations from Catholic Cemeteries records; people from the
      <a href="${esc(state.section.geni_project)}" target="_blank" rel="noopener">Geni project</a>.
      Not affiliated with Geni.${geni.user ? `<br>Signed in to Geni as ${esc(geni.user.name)} · <button type="button" class="linkish" data-act="signout">Sign out</button>` : ""}</div>`;
    $("#panelBody").innerHTML = html;
  }

  function relText(g) {
    const r = relOf(g);
    if (!geni.token) return "";
    if (!r) return geni.current === g.id ? "Asking Geni…" : "Not worked out yet";
    if (r.status === "pending") return "Geni is still working this out";
    if (r.relationship === "you") return "You";
    return r.relationship || "Not connected to you on Geni";
  }

  function row({ g, k, d, b }) {
    const yrs = [g.born, g.died].filter(Boolean).join("–");
    const rel = relText(g), blood = closeBlood(relOf(g));
    return `<li class="row" tabindex="0" data-id="${esc(g.id)}">
      ${swatch(k)}
      <div><div class="nm">${esc(g.name)}</div>
        ${rel ? `<div class="rel ${relOf(g)?.status === "done" ? "" : "pending"}">${esc(rel)}</div>` : ""}
        ${blood ? `<div class="rel">and your ${esc(blood.relationship)}</div>` : ""}
        ${yrs ? `<div class="yrs">${esc(yrs)}</div>` : ""}</div>
      <div class="dist">${arrowSvg(b)}${fmt(d)}<small>${compass(b)}</small></div></li>`;
  }

  function chainHtml(chain, g) {
    return `<ol class="chain">${chain.map((c, i) => {
      const cls = i === 0 ? "you" : i === chain.length - 1 ? "end" : "";
      const name = i === 0 ? "You" : i === chain.length - 1 ? g.name : c.name;
      return `<li class="${cls}">${i ? `<span class="via">${esc(c.relation)}</span>` : ""}<span class="who">${esc(name)}</span></li>`;
    }).join("")}</ol>`;
  }

  function renderDetail(g) {
    const d = dist(state.me, g.gps), b = bearing(state.me, g.gps);
    const plot = Object.entries(g.plot).filter(([, v]) => v).map(([k, v]) => `${k[0].toUpperCase() + k.slice(1)} ${v}`).join(", ");
    const yrs = [g.born, g.died].filter(Boolean).join("–");
    const r = relOf(g), k = kindOf(g);
    const steps = r?.chain?.length ? r.chain.length - 1 : 0;
    let relBlock;
    if (!geni.token) {
      relBlock = `<div class="signin small"><span class="muted">Sign in with Geni to see how you're related.</span>
        <button type="button" class="btn" data-act="signin" ${CONFIG.geniAppKey ? "" : "disabled"}>Sign in with Geni</button></div>`;
    } else if (r?.status === "done") {
      const tags = closeBlood(r) ? ["blood", "inlaw"] : [k];
      relBlock = `${tags.map((t) => `<span class="tag" style="background:var(${KINDS[t].css})">${KINDS[t].label}</span>`).join(" ")}
        <div class="big-rel">${r.relationship === "you" ? "This is you" : r.relationship ? `Your ${esc(r.relationship)}` : "Geni found no connection to you"}</div>`;
    } else {
      relBlock = `<div class="big-rel muted">${esc(relText(g))}</div>`;
    }
    $("#panelBody").innerHTML = `<div class="detail">
      <button type="button" class="back" data-act="back">← Around you</button>
      <h2>${esc(g.name)}</h2>
      ${yrs ? `<div class="yrs">${esc(yrs)}</div>` : ""}
      ${relBlock}
      <dl class="facts">
        <dt>From you</dt><dd>${arrowSvg(b)}<b>${fmt(d)}</b> ${compass(b)}</dd>
        ${plot ? `<dt>Plot</dt><dd>${esc(plot)}</dd>` : ""}
        ${g.lotmates.length ? `<dt>Same lot</dt><dd>${g.lotmates.map(esc).join(", ")}</dd>` : ""}
      </dl>
      ${r?.also ? `<div class="also-line">${swatch(r.also.kind || "blood")}<span>Also your <b>${esc(r.also.relationship)}</b>
        <span class="muted">· ${esc(KINDS[r.also.kind || "blood"].label.toLowerCase())}${r.also.steps ? `, ${r.also.steps} steps` : ""}</span></span></div>` : ""}
      ${steps ? `<h3>How you're connected · ${steps} step${steps > 1 ? "s" : ""}</h3>${chainHtml(r.chain, g)}` : ""}
      ${r?.also ? `<details class="also"><summary>Show the ${esc(KINDS[r.also.kind || "blood"].label.toLowerCase())} path</summary>${chainHtml(r.also.chain, g)}</details>` : ""}
      ${steps && r?.also ? `<p class="muted note">Plotline shows the shorter connection first, and a blood line first unless it's more than two steps longer.
        Anyone who is your ${ORDINALS[BLOOD_COUSIN_LIMIT - 1]} cousin or closer by blood is coloured and counted as a blood relative.</p>` : ""}
      ${geni.user && r?.status === "done" ? `<button type="button" class="linkish recheck" data-act="recheck" data-gid="${esc(g.id)}">Ask Geni again</button>` : ""}
      <div class="links">
        <a class="btn" href="https://www.google.com/maps/dir/?api=1&destination=${g.gps[0]},${g.gps[1]}&travelmode=walking" target="_blank" rel="noopener">Walking directions</a>
        ${g.geni ? `<a class="btn secondary" href="${esc(g.geni)}" target="_blank" rel="noopener">Geni profile</a>` : ""}
        ${g.findagrave ? `<a class="btn secondary" href="${esc(g.findagrave)}" target="_blank" rel="noopener">Find a Grave</a>` : ""}
      </div></div>`;
  }

  function updateLine() {
    if (state.selected) {
      line.setLatLngs([state.me, state.selected.pos]);
      if (!map.hasLayer(line)) line.addTo(map);
    } else if (map.hasLayer(line)) line.remove();
  }

  function select(g) {
    state.selected = g;
    drawGraves();
    render();
    $("#panelBody").scrollTop = 0;
    if (!map.getBounds().pad(-0.1).contains(g.pos)) map.panTo(g.pos);
    if (matchMedia("(max-width: 760px)").matches) $("#panel").classList.add("tall");
  }

  $("#panelBody").addEventListener("click", (e) => {
    const t = e.target.closest("[data-id],[data-kind],[data-act]");
    if (!t || t.tagName === "SELECT") return;
    if (t.dataset.id) return select(state.graves.find((g) => g.id === t.dataset.id));
    if (t.dataset.kind) {
      const k = t.dataset.kind;
      state.hidden.has(k) ? state.hidden.delete(k) : state.hidden.add(k);
      store.set("hiddenKinds", JSON.stringify([...state.hidden]));
      drawGraves();
      return render();
    }
    const act = t.dataset.act;
    if (act === "back") { state.selected = null; drawGraves(); return render(); }
    if (act === "signin") return signIn();
    if (act === "signout") return signOut();
    if (act === "pause") { geni.paused = true; return render(); }
    if (act === "resume") { geni.paused = false; geni.error = ""; return work(); }
    if (act === "recheck") {
      delete geni.rels[t.dataset.gid];
      saveRels();
      geni.priority = t.dataset.gid;
      geni.paused = false;
      drawGraves();
      render();
      toast("Asking Geni again. It's next in line.");
      return work();
    }
    if (act === "jump") {
      setMode("explore");
      setMe(move(state.section.centre, -18, 0), { pan: true, zoom: 19.5 });
    }
  });
  $("#panelBody").addEventListener("change", (e) => {
    if (e.target.dataset.act !== "radius") return;
    state.radius = Number(e.target.value);
    store.set("radius", String(state.radius));
    setMe(state.me, { pan: false });
  });
  $("#panelBody").addEventListener("keydown", (e) => {
    if ((e.key === "Enter" || e.key === " ") && e.target.dataset.id) { e.preventDefault(); e.target.click(); }
  });
  $("#handle").addEventListener("click", () => {
    $("#panel").classList.toggle("tall");
    setTimeout(() => map.invalidateSize(), 220);
  });

  /* ---------- modes ---------- */
  function toast(msg) {
    const t = $("#toast");
    t.textContent = msg;
    t.classList.add("show");
    clearTimeout(toast.timer);
    toast.timer = setTimeout(() => t.classList.remove("show"), 3600);
  }

  function setMode(mode) {
    state.mode = mode;
    document.body.classList.toggle("live", mode === "live");
    $("#modeExplore").classList.toggle("on", mode === "explore");
    $("#modeLive").classList.toggle("on", mode === "live");
    if (meMarker.dragging) mode === "explore" ? meMarker.dragging.enable() : meMarker.dragging.disable();
    if (mode === "live") startLive();
    else stopLive();
  }

  function startLive() {
    if (!("geolocation" in navigator)) { toast("This browser can't share your location."); return setMode("explore"); }
    state.follow = true;
    toast("Finding you…");
    state.watchId = navigator.geolocation.watchPosition((pos) => {
      const p = [pos.coords.latitude, pos.coords.longitude];
      const first = !state.lastFix;
      state.lastFix = pos;
      accuracy.setLatLng(p).setRadius(pos.coords.accuracy || 1);
      if (!map.hasLayer(accuracy)) accuracy.addTo(map);
      if (pos.coords.heading != null && !Number.isNaN(pos.coords.heading) && pos.coords.speed > 0.4) setHeading(pos.coords.heading);
      setMe(p, { pan: first, zoom: first ? 19.5 : undefined });
      if (first) {
        const far = state.section?.centre && dist(p, state.section.centre) > FAR_M;
        toast(far ? "Got your location. You're not at this section, so the list shows the distance." : `Located to within ${fmt(pos.coords.accuracy)}.`);
      }
    }, (err) => {
      toast(err.code === 1 ? "Location permission was declined. Explore mode is still available." : "Couldn't get your location.");
      setMode("explore");
    }, { enableHighAccuracy: true, maximumAge: 2000, timeout: 20000 });
    startCompass();
  }

  function stopLive() {
    if (state.watchId != null) navigator.geolocation.clearWatch(state.watchId);
    state.watchId = null;
    state.lastFix = null;
    if (map.hasLayer(accuracy)) accuracy.remove();
  }

  let compassOn = false;
  function onOrientation(e) {
    if (state.mode !== "live") return;
    let h = null;
    if (typeof e.webkitCompassHeading === "number") h = e.webkitCompassHeading;
    else if (e.absolute && typeof e.alpha === "number") h = (360 - e.alpha) % 360;
    if (h != null) setHeading(h);
  }
  async function startCompass() {
    if (compassOn) return;
    try {
      if (typeof DeviceOrientationEvent !== "undefined" && typeof DeviceOrientationEvent.requestPermission === "function") {
        if ((await DeviceOrientationEvent.requestPermission()) !== "granted") return;
      }
      window.addEventListener("deviceorientationabsolute", onOrientation);
      window.addEventListener("deviceorientation", onOrientation);
      compassOn = true;
    } catch { /* no compass; the dot still works */ }
  }

  $("#modeExplore").addEventListener("click", () => setMode("explore"));
  $("#modeLive").addEventListener("click", () => setMode("live"));
  $("#units").addEventListener("click", () => {
    state.units = state.units === "ft" ? "m" : "ft";
    store.set("units", state.units);
    $("#units").textContent = state.units;
    render();
  });
  $("#units").textContent = state.units;

  /* ---------- walking ---------- */
  const STEPS = { n: [1, 0, 0], s: [-1, 0, 180], e: [0, 1, 90], w: [0, -1, 270] };
  function step(dir, scale = 1) {
    if (state.mode !== "explore" || !state.me) return;
    if (dir === "c") return map.panTo(state.me);
    const [n, e, h] = STEPS[dir];
    setMe(move(state.me, n * STEP_M * scale, e * STEP_M * scale), { pan: false });
    setHeading(h);
    if (!map.getBounds().pad(-0.2).contains(state.me)) map.panTo(state.me);
    hideHint();
  }
  const KEYS = { ArrowUp: "n", ArrowDown: "s", ArrowLeft: "w", ArrowRight: "e", w: "n", s: "s", a: "w", d: "e" };
  document.addEventListener("keydown", (e) => {
    if (/^(INPUT|SELECT|TEXTAREA)$/.test(e.target.tagName) || e.metaKey || e.ctrlKey || e.altKey) return;
    const dir = KEYS[e.key] || KEYS[e.key.toLowerCase()];
    if (!dir) return;
    e.preventDefault();
    step(dir, e.shiftKey ? 4 : 1);
  });
  let holdTimer;
  $("#dpad").addEventListener("pointerdown", (e) => {
    const b = e.target.closest("[data-step]");
    if (!b) return;
    e.preventDefault();
    step(b.dataset.step);
    if (b.dataset.step === "c") return;
    clearInterval(holdTimer);
    holdTimer = setInterval(() => step(b.dataset.step), 160);
  });
  ["pointerup", "pointerleave", "pointercancel"].forEach((ev) => $("#dpad").addEventListener(ev, () => clearInterval(holdTimer)));
  L.DomEvent.disableClickPropagation($("#dpad"));

  function hideHint() { $("#hint").style.opacity = "0"; }
  setTimeout(hideHint, 9000);

  /* ---------- link to a spot ---------- */
  function readHash() {
    const h = new URLSearchParams(location.hash.slice(1));
    const at = (h.get("at") || "").split(",").map(Number);
    return { s: h.get("s"), at: at.length === 2 && at.every(Number.isFinite) ? at : null, z: Number(h.get("z")) || null };
  }
  let hashTimer;
  function writeHash() {
    clearTimeout(hashTimer);
    hashTimer = setTimeout(() => {
      if (!state.section || !state.me) return;
      history.replaceState(null, "", `#s=${state.section.id}&at=${state.me[0].toFixed(6)},${state.me[1].toFixed(6)}&z=${map.getZoom()}`);
    }, 400);
  }
  map.on("zoomend", () => state.mode === "explore" && writeHash());

  matchMedia("(prefers-color-scheme: dark)").addEventListener?.("change", drawGraves);
  window.addEventListener("resize", () => map.invalidateSize());
  init();
})();
