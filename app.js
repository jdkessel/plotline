/* Kin in the Rows: walk a cemetery section and see who is around you. */
(() => {
  "use strict";

  const KINDS = {
    direct: { label: "Direct line", css: "--direct" },
    blood: { label: "Blood relative", css: "--blood" },
    inlaw: { label: "Through marriage", css: "--inlaw" },
    none: { label: "Not connected yet", css: "--none" },
  };
  const STEP_M = 1.5;          // one arrow-key step
  const FAR_M = 600;           // further than this from the section = "not here"
  const LABEL_ZOOM = 20;       // show names on the map from this zoom

  const $ = (s) => document.querySelector(s);
  const store = {
    get(k, d) { try { return localStorage.getItem(k) ?? d; } catch { return d; } },
    set(k, v) { try { localStorage.setItem(k, v); } catch { /* private mode */ } },
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
    kinds: new Set(JSON.parse(store.get("kinds", '["direct","blood","inlaw","none"]'))),
    selected: null, follow: true, watchId: null, lastFix: null,
  };

  function fmt(m) {
    if (state.units === "ft") {
      const ft = m * 3.28084;
      return ft < 1000 ? `${Math.round(ft)} ft` : `${(m / 1609.34).toFixed(1)} mi`;
    }
    return m < 1000 ? `${Math.round(m)} m` : `${(m / 1000).toFixed(1)} km`;
  }
  const radiusLabel = (r) => (state.units === "ft" ? `${Math.round(r * 3.28084 / 5) * 5} ft` : `${r} m`);

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
    try {
      state.sections = await getJSON("data/sections.json");
    } catch (e) {
      $("#panelBody").innerHTML = `<p class="pad">Couldn't load the section list. ${esc(e.message)}</p>`;
      return;
    }
    const sel = $("#section");
    sel.innerHTML = state.sections.map((s) => `<option value="${esc(s.id)}">${esc(s.cemetery)} · ${esc(s.short)}</option>`).join("");
    sel.hidden = state.sections.length < 1;
    const hash = readHash();
    const first = state.sections.find((s) => s.id === hash.s) || state.sections[0];
    sel.value = first.id;
    sel.addEventListener("change", () => loadSection(sel.value, null));
    await loadSection(first.id, hash.at);
    if (hash.z) map.setZoom(hash.z);
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
  }

  /* ---------- drawing ---------- */
  function drawGraves() {
    graveLayer.clearLayers();
    const labels = map.getZoom() >= LABEL_ZOOM;
    state.graves.forEach((g) => {
      const on = state.kinds.has(g.connection);
      const colour = cssVar(KINDS[g.connection].css);
      const m = L.circleMarker(g.pos, {
        radius: state.selected === g ? 11 : 8, color: state.selected === g ? "#2f7df6" : "#ffffff",
        weight: state.selected === g ? 3.5 : 2, fillColor: colour, fillOpacity: on ? 1 : 0.25, opacity: on ? 1 : 0.4,
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
  const kindChip = (k) => `<span class="sw" style="background:var(${KINDS[k].css})"></span>`;

  function render() {
    if (!state.section || !state.me) return;
    updateLine();
    if (state.selected) return renderDetail(state.selected);
    renderList();
  }

  function renderList() {
    const me = state.me;
    const all = state.graves
      .map((g) => ({ g, d: dist(me, g.gps), b: bearing(me, g.gps) }))
      .sort((a, b) => a.d - b.d);
    const shown = all.filter((x) => state.kinds.has(x.g.connection));
    const near = state.radius ? shown.filter((x) => x.d <= state.radius) : shown;
    const rest = state.radius ? shown.filter((x) => x.d > state.radius) : [];
    const sec = state.sections.find((s) => s.id === state.section.id) || {};
    const fromCentre = state.section.centre ? dist(me, state.section.centre) : 0;
    const closestKin = all.find((x) => x.g.connection === "direct" || x.g.connection === "blood");

    let html = "";
    if (fromCentre > FAR_M) {
      html += `<div class="notice">You're <b>${fmt(fromCentre)}</b> from ${esc(sec.short || "the section")}.
        ${state.mode === "live" ? "Walk it virtually instead?" : ""}
        <br><button type="button" data-act="jump">${state.mode === "live" ? "Explore the section" : "Go to the section"}</button></div>`;
    }
    html += `<div class="head"><h2>${near.length ? `${near.length} around you` : "No one right here"}</h2>
      <p>${state.radius ? `within ${radiusLabel(state.radius)}` : "everyone in the section"}${closestKin && fromCentre <= FAR_M ? ` · closest kin: ${esc(closestKin.g.name)}, ${fmt(closestKin.d)} ${compass(closestKin.b)}` : ""}</p></div>`;
    html += `<div class="tools">${Object.entries(KINDS).map(([k, v]) => {
      const n = state.graves.filter((g) => g.connection === k).length;
      return n ? `<button type="button" class="chip ${state.kinds.has(k) ? "on" : "off"}" data-kind="${k}" aria-pressed="${state.kinds.has(k)}">${kindChip(k)}${v.label} ${n}</button>` : "";
    }).join("")}
      <label class="radius">Range <select data-act="radius">${[10, 20, 30, 50, 100, 0].map((r) =>
        `<option value="${r}" ${r === state.radius ? "selected" : ""}>${r ? radiusLabel(r) : "All"}</option>`).join("")}</select></label></div>`;
    html += `<ul class="list">${near.map(row).join("")}</ul>`;
    if (rest.length) html += `<div class="sep">Further away</div><ul class="list">${rest.map(row).join("")}</ul>`;
    if (!shown.length) html += `<p class="pad muted">Nobody matches the filters above.</p>`;
    html += `<div class="foot">Relationships from Geni. Grave locations from Catholic Cemeteries records. Living relatives are hidden.
      <a href="${esc(state.section.geni_project)}" target="_blank" rel="noopener">Geni project</a></div>`;
    $("#panelBody").innerHTML = html;
  }

  function row({ g, d, b }) {
    const yrs = [g.born, g.died].filter(Boolean).join("–");
    return `<li class="row" tabindex="0" data-id="${esc(g.id)}">
      <span class="sw" style="background:var(${KINDS[g.connection].css})"></span>
      <div><div class="nm">${esc(g.name)}</div>
        <div class="rel">${esc(g.relationship || "Not connected on Geni yet")}</div>
        ${yrs ? `<div class="yrs">${esc(yrs)}</div>` : ""}</div>
      <div class="dist">${arrowSvg(b)}${fmt(d)}<small>${compass(b)}</small></div></li>`;
  }

  function chainHtml(chain, g) {
    return `<ol class="chain">${chain.map((c, i) => {
      const cls = i === 0 ? "you" : i === chain.length - 1 ? "end" : "";
      const hidden = c.name === "Living relative";
      return `<li class="${cls}">${i ? `<span class="via">${esc(c.relation)}</span>` : ""}
        <span class="who ${hidden ? "hidden" : ""}">${esc(i === chain.length - 1 ? g.name : c.name)}</span></li>`;
    }).join("")}</ol>`;
  }

  function renderDetail(g) {
    const d = dist(state.me, g.gps), b = bearing(state.me, g.gps);
    const plot = Object.entries(g.plot).filter(([, v]) => v).map(([k, v]) => `${k[0].toUpperCase() + k.slice(1)} ${v}`).join(", ");
    const yrs = [g.born, g.died].filter(Boolean).join("–");
    const steps = g.chain.length ? g.chain.length - 1 : 0;
    $("#panelBody").innerHTML = `<div class="detail">
      <button type="button" class="back" data-act="back">← Around you</button>
      <h2>${esc(g.name)}</h2>
      ${yrs ? `<div class="yrs">${esc(yrs)}</div>` : ""}
      <span class="tag" style="background:var(${KINDS[g.connection].css})">${KINDS[g.connection].label}</span>
      <div class="big-rel">${esc(g.relationship ? `Your ${g.relationship}` : "Not connected to your tree on Geni yet")}</div>
      <dl class="facts">
        <dt>From you</dt><dd>${arrowSvg(b)}<b>${fmt(d)}</b> ${compass(b)}</dd>
        ${plot ? `<dt>Plot</dt><dd>${esc(plot)}</dd>` : ""}
        ${g.lotmates.length ? `<dt>Same lot</dt><dd>${g.lotmates.map(esc).join(", ")}</dd>` : ""}
      </dl>
      ${steps ? `<h3>How you're connected · ${steps} step${steps > 1 ? "s" : ""}</h3>${chainHtml(g.chain, g)}` : ""}
      ${g.also ? `<details class="also"><summary>Also: your ${esc(g.also.relationship)}</summary>${chainHtml(g.also.chain, g)}</details>` : ""}
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
      state.kinds.has(k) ? state.kinds.delete(k) : state.kinds.add(k);
      store.set("kinds", JSON.stringify([...state.kinds]));
      drawGraves();
      return render();
    }
    if (t.dataset.act === "back") { state.selected = null; drawGraves(); return render(); }
    if (t.dataset.act === "jump") {
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
    toast.timer = setTimeout(() => t.classList.remove("show"), 3200);
  }

  function setMode(mode) {
    state.mode = mode;
    document.body.classList.toggle("live", mode === "live");
    $("#modeExplore").classList.toggle("on", mode === "explore");
    $("#modeLive").classList.toggle("on", mode === "live");
    meMarker.dragging && (mode === "explore" ? meMarker.dragging.enable() : meMarker.dragging.disable());
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
  $("#section").addEventListener("click", (e) => e.stopPropagation());

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
    if (/^(INPUT|SELECT|TEXTAREA)$/.test(e.target.tagName) || e.metaKey || e.ctrlKey) return;
    const dir = KEYS[e.key] || KEYS[e.key.toLowerCase?.()];
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
