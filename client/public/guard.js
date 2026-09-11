// The dashboard's own client code: the signal tables, the filter bar, the live
// tick and the detail panel.
//
// The shared vocabulary lives in core.js, the panel renderers in charts.js, and
// everything under /views in views.js. This file imports all three; none of
// them imports this one, so the dependency runs one way.
import { adminHeaders, bytes, compact, duration, el, muted, number, palette, qs, qsa, relativeTime, request, shortID, since, svgNS, text, timeText } from "./core.js";
import { drawWaterfall } from "./charts.js";
import { mountViews, refreshViews, unmountViews } from "./views.js";
import { closeInteractiveTerminal, refreshCluster, refreshMachine } from "./cluster.js";
import { refreshRegistries } from "./registries.js";
import { refreshCloud } from "./cloud.js";
import { refreshStorage } from "./storage.js";
import { refreshMembers } from "./members.js";
import { refreshAlerts } from "./alerts.js";
import { refreshSecrets } from "./secrets.js";
import { refreshConfig } from "./config.js";
import { refreshBackup } from "./backup.js";
import { closeDeployStreams, refreshDeploys } from "./deploys.js";
import { refreshAnalytics } from "./analytics.js";
import { refreshHealthChecks } from "./checks.js";
import { screenCleared } from "./store.js";

// Machine-scoped signal queries were retired: service is the useful isolation
// boundary, and resolving persisted node IDs through topology made an old
// browser preference able to hide every event. Forget the retired key as well
// as ignoring it, so it cannot return after a downgrade/upgrade cycle.
try { localStorage.removeItem("guard.cluster"); } catch { /* storage may be disabled */ }

// The one filter nobody types: an analytics path arrives in the URL and the
// table narrows to the spans of the browser sessions that saw it. It is what
// makes a rate on /analytics walkable — the ids stay in the database, the link
// carries the path, and the store does the join.
//
// Read from the URL on every mount because it belongs to the link somebody
// followed: a reload, a new tab, the Back button and a pasted address all land
// on the same table, and walking anywhere else drops it without anybody having
// to say so.
let linkedPath = "";

function readLinkedFilter() {
  const params = new URLSearchParams(location.search);
  linkedPath = params.get("rum_path") || "";
  // The window comes with the link. A drill out of "last 30 days" that landed
  // on this page's default hour would be an empty table saying nothing
  // happened, which is the one answer it must not give.
  const wanted = params.get("range");
  if (!wanted) return;
  for (const select of qsa('[data-filter="range"]')) {
    if ([...select.options].some((option) => option.value === wanted)) select.value = wanted;
  }
}

function renderLinkedFilter() {
  for (const host of qsa("[data-linked-filter]")) {
    host.classList.toggle("hidden", !linkedPath);
    host.classList.toggle("flex", Boolean(linkedPath));
    if (!linkedPath) {
      host.replaceChildren();
      continue;
    }
    const label = el("span", `text-xs font-medium ${muted}`, "From analytics");
    const chip = el("button", "cn-badge inline-flex w-fit shrink-0 items-center gap-1.5 whitespace-nowrap border-primary/40 bg-primary/15 text-primary");
    chip.type = "button";
    chip.dataset.linkedClear = "true";
    chip.title = `Only the spans of browser sessions that saw ${linkedPath}. Press to drop the filter.`;
    chip.append(text(`sessions that saw ${linkedPath}`), el("span", "opacity-60", "✕"));
    host.replaceChildren(label, chip);
  }
}

const pageSize = 50;
const signalPages = new Map([["logs", 0], ["traces", 0], ["metrics", 0]]);
const signalRequests = new Map();
const facetsTTL = 60_000;
let facetsCache = null;
let facetsFetchedAt = 0;
let facetsRequest = null;
let live = localStorage.getItem("guard.live") !== "off";
let filterTimer;
let initializedPage = null;
let initialRefresh = null;
let liveTimer;
let refreshInFlight = false;
let lastInteraction = 0;
let renderGeneration = 0;
let summarySignature = "";
const signalSignatures = new Map();
let metricsSignature = "";
let latestMetricSeries = [];
let signalListObserver;

// Keep the event list inside the viewport even when the filter toolbar changes
// height (the custom range adds a second row). The card then gives its spare
// space to the table container, so the document stays still while rows scroll.
function sizeSignalList() {
  const list = qs("[data-signal-list]");
  if (!list) return;
  const pageTop = list.getBoundingClientRect().top + window.scrollY;
  const pageGutter = window.innerWidth >= 1024 ? 32 : 16;
  const available = window.innerHeight - pageTop - pageGutter;
  list.style.setProperty("--signal-list-height", `${Math.max(288, available)}px`);
}

function mountSignalList() {
  signalListObserver?.disconnect();
  signalListObserver = undefined;
  if (!qs("[data-signal-list]")) return;
  requestAnimationFrame(sizeSignalList);
  const toolbar = qs("[data-signal-toolbar]");
  if (toolbar && "ResizeObserver" in window) {
    signalListObserver = new ResizeObserver(() => requestAnimationFrame(sizeSignalList));
    signalListObserver.observe(toolbar);
  }
}

window.addEventListener("resize", sizeSignalList, { passive: true });

const signalURLParams = ["range", "service", "severity", "name", "q", "group", "from", "to", "page", "nodes"];

function signalRoot(signal) {
  return qs(`[data-filter-signal="${signal}"]`);
}

function localDateTime(value) {
  const date = new Date(value);
  if (!value || Number.isNaN(date.getTime())) return "";
  const local = new Date(date.getTime() - date.getTimezoneOffset() * 60_000);
  return local.toISOString().slice(0, 16);
}

function setFilterValue(root, name, value) {
  const control = qs(`[data-filter="${name}"]`, root);
  if (!control) return;
  // Facets arrive after the first event request. Keep a linked service or
  // metric selectable until the real option list arrives, so the very first
  // request already matches the address somebody opened.
  if (control.tagName === "SELECT" && value && ![...control.options].some((option) => option.value === value)) {
    const option = document.createElement("option");
    option.value = value;
    option.textContent = value;
    control.appendChild(option);
  }
  control.value = value;
}

function readSignalURLState(signal) {
  const root = signalRoot(signal);
  if (!root) return;
  const params = new URLSearchParams(location.search);
  const page = Number.parseInt(params.get("page") || "1", 10);
  signalPages.set(signal, Number.isFinite(page) && page > 0 ? page - 1 : 0);
  for (const name of ["service", "severity", "name", "group"]) setFilterValue(root, name, params.get(name) || "");
  setFilterValue(root, "query", params.get("q") || "");
  const range = params.get("range") || (params.has("from") || params.has("to") ? "custom" : "1h");
  setFilterValue(root, "range", range);
  setFilterValue(root, "from", localDateTime(params.get("from")));
  setFilterValue(root, "to", localDateTime(params.get("to")));
  qs("[data-custom-range]", root)?.classList.toggle("hidden", range !== "custom");
}

function syncSignalURL(signal) {
  const root = signalRoot(signal);
  if (!root) return;
  const here = new URL(location.href);
  for (const name of signalURLParams) here.searchParams.delete(name);
  const value = (name) => qs(`[data-filter="${name}"]`, root)?.value || "";
  here.searchParams.set("range", value("range") || "1h");
  for (const name of ["service", "severity", "name", "group"]) if (value(name)) here.searchParams.set(name, value(name));
  if (value("query")) here.searchParams.set("q", value("query"));
  if (value("range") === "custom") {
    for (const name of ["from", "to"]) {
      const date = new Date(value(name));
      if (value(name) && !Number.isNaN(date.getTime())) here.searchParams.set(name, date.toISOString());
    }
  }
  const page = signalPages.get(signal) || 0;
  if (page) here.searchParams.set("page", String(page + 1));
  history.replaceState(history.state, "", here.pathname + here.search + here.hash);
}

// The overview is a personal board. Its layout is deliberately browser-local:
// pinning a widget is a reading preference, not shared Guard configuration.
// The twelve-column widths match saved Views so a panel has one spatial
// language everywhere in the product.
const dashboardLayoutKey = "guard.dashboard.layout.v1";
let dashboardLayout = null;
let dashboardDragging = null;
let dashboardEditing = false;

function dashboardFrames() { return qsa("[data-dashboard-widget]"); }

function loadDashboardLayout() {
  const frames = dashboardFrames();
  if (!frames.length) return null;
  const defaults = {
    order: frames.map((frame) => frame.dataset.dashboardWidget),
    pinned: Object.fromEntries(frames.map((frame) => [frame.dataset.dashboardWidget, frame.dataset.widgetDefaultPinned === "true"])),
    widths: Object.fromEntries(frames.map((frame) => [frame.dataset.dashboardWidget, Number(frame.dataset.widgetWidth)])),
    service: "",
  };
  try {
    const stored = JSON.parse(localStorage.getItem(dashboardLayoutKey) || "null");
    if (stored) {
      const known = new Set(defaults.order);
      defaults.order = [...(stored.order || []).filter((key) => known.has(key)), ...defaults.order.filter((key) => !(stored.order || []).includes(key))];
      defaults.pinned = { ...defaults.pinned, ...(stored.pinned || {}) };
      defaults.widths = { ...defaults.widths, ...(stored.widths || {}) };
      defaults.service = stored.service || "";
    }
  } catch { /* an old or disabled localStorage means the default board */ }
  dashboardLayout = defaults;
  return defaults;
}

function saveDashboardLayout() {
  if (!dashboardLayout) return;
  try { localStorage.setItem(dashboardLayoutKey, JSON.stringify(dashboardLayout)); } catch { /* the board still works for this visit */ }
}

function applyDashboardLayout() {
  const grid = qs("[data-widget-grid]");
  if (!grid) return;
  const layout = loadDashboardLayout();
  const byKey = new Map(dashboardFrames().map((frame) => [frame.dataset.dashboardWidget, frame]));
  for (const key of layout.order) {
    const frame = byKey.get(key);
    if (!frame) continue;
    const sizes = (frame.dataset.widgetSizes || "12").split(",").map(Number);
    const width = sizes.includes(Number(layout.widths[key])) ? Number(layout.widths[key]) : sizes[0];
    layout.widths[key] = width;
    frame.hidden = !layout.pinned[key];
    frame.style.setProperty("--widget-span", String(width));
    qs("[data-widget-size]", frame).textContent = String(width);
    grid.appendChild(frame);
  }
  for (const row of qsa("[data-widget-catalogue]")) {
    const key = row.dataset.widgetCatalogue;
    const pinned = Boolean(layout.pinned[key]);
    const button = qs("[data-widget-pin]", row);
    button.setAttribute("aria-pressed", String(pinned));
    qs("[data-widget-pin-label]", button).textContent = pinned ? "Unpin" : "Pin";
    qs("[data-widget-catalogue-size]", row).textContent = `${layout.widths[key]}/12`;
  }
  const service = qs("[data-widget-log-service]");
  if (service) service.value = layout.service;
  grid.classList.toggle("dashboard-editing", dashboardEditing);
  for (const frame of dashboardFrames()) {
    frame.draggable = dashboardEditing;
    frame.tabIndex = dashboardEditing && !frame.hidden ? 0 : -1;
    if (dashboardEditing) frame.setAttribute("aria-label", `Move ${frame.dataset.dashboardWidget} widget. Use arrow keys to reorder.`);
    else frame.removeAttribute("aria-label");
  }
  const edit = qs("[data-dashboard-edit]");
  if (edit) {
    edit.setAttribute("aria-pressed", String(dashboardEditing));
    qs("[data-dashboard-edit-label]", edit).textContent = dashboardEditing ? "Done" : "Edit";
  }
}

function setDashboardEditing(editing) {
  dashboardEditing = editing;
  applyDashboardLayout();
}

function dashboardWidgetPinned(key) {
  const frame = qs(`[data-dashboard-widget="${key}"]`);
  return Boolean(frame && !frame.hidden);
}

function setDashboardPinned(key, pinned) {
  if (!dashboardLayout) loadDashboardLayout();
  dashboardLayout.pinned[key] = pinned;
  saveDashboardLayout();
  applyDashboardLayout();
}

function resizeDashboardWidget(frame) {
  if (!dashboardLayout) return;
  const key = frame.dataset.dashboardWidget;
  const sizes = frame.dataset.widgetSizes.split(",").map(Number);
  const current = Number(dashboardLayout.widths[key]);
  dashboardLayout.widths[key] = sizes[(Math.max(0, sizes.indexOf(current)) + 1) % sizes.length];
  saveDashboardLayout();
  applyDashboardLayout();
}

function saveDashboardOrder() {
  if (!dashboardLayout) return;
  dashboardLayout.order = dashboardFrames().map((frame) => frame.dataset.dashboardWidget);
  saveDashboardLayout();
}

// Metrics uses the same twelve-column, browser-local board language as Home,
// but its catalogue is discovered from OTLP rather than compiled into markup.
// Keeping a separate key means rearranging runtime instruments cannot move the
// health and cluster widgets on the overview.
const metricLayoutKey = "guard.metrics.layout.v1";
let metricLayout = null;
let metricDragging = null;
let metricEditing = false;

function metricFrames() { return qsa("[data-metric-widget]"); }

function defaultMetricPinned(item, index) {
  const useful = /(?:heap\.(?:size|used|limit)|gc\.duration|active_requests|request\.duration|cpu\.utilization|memory\.usage|memory\.utilization)$/i;
  return useful.test(item.key) || index < 6;
}

function loadMetricLayout(series = latestMetricSeries) {
  const defaults = {
    order: series.map((item) => item.key),
    pinned: Object.fromEntries(series.map((item, index) => [item.key, defaultMetricPinned(item, index)])),
    widths: Object.fromEntries(series.map((item) => [item.key, 4])),
  };
  try {
    const stored = JSON.parse(localStorage.getItem(metricLayoutKey) || "null");
    if (stored) {
      const known = new Set(defaults.order);
      defaults.order = [...(stored.order || []).filter((key) => known.has(key)), ...defaults.order.filter((key) => !(stored.order || []).includes(key))];
      defaults.pinned = { ...defaults.pinned, ...(stored.pinned || {}) };
      defaults.widths = { ...defaults.widths, ...(stored.widths || {}) };
    }
  } catch { /* the received instruments still get a useful default board */ }
  metricLayout = defaults;
  return defaults;
}

function saveMetricLayout() {
  if (!metricLayout) return;
  try { localStorage.setItem(metricLayoutKey, JSON.stringify(metricLayout)); } catch { /* local preference only */ }
}

function applyMetricLayout() {
  const grid = qs("[data-metric-widget-grid]");
  if (!grid || !metricLayout) return;
  const byKey = new Map(metricFrames().map((frame) => [frame.dataset.metricWidget, frame]));
  for (const key of metricLayout.order) {
    const frame = byKey.get(key);
    if (!frame) continue;
    const sizes = (frame.dataset.widgetSizes || "4,6,8,12").split(",").map(Number);
    const width = sizes.includes(Number(metricLayout.widths[key])) ? Number(metricLayout.widths[key]) : sizes[0];
    metricLayout.widths[key] = width;
    frame.hidden = !metricLayout.pinned[key];
    frame.style.setProperty("--widget-span", String(width));
    qs("[data-widget-size]", frame).textContent = String(width);
    grid.appendChild(frame);
  }
  for (const row of qsa("[data-metric-catalogue-item]")) {
    const key = row.dataset.metricCatalogueItem;
    const pinned = Boolean(metricLayout.pinned[key]);
    const button = qs("[data-metric-widget-pin]", row);
    button.setAttribute("aria-pressed", String(pinned));
    qs("[data-metric-widget-pin-label]", button).textContent = pinned ? "Unpin" : "Pin";
    qs("[data-metric-catalogue-size]", row).textContent = `${metricLayout.widths[key]}/12`;
  }
  grid.classList.toggle("dashboard-editing", metricEditing);
  for (const frame of metricFrames()) {
    frame.draggable = metricEditing;
    frame.tabIndex = metricEditing && !frame.hidden ? 0 : -1;
    if (metricEditing) frame.setAttribute("aria-label", `Move ${humanMetricName(frame.dataset.metricWidget)} card. Use arrow keys to reorder.`);
    else frame.removeAttribute("aria-label");
  }
  const edit = qs("[data-metric-dashboard-edit]");
  if (edit) {
    edit.setAttribute("aria-pressed", String(metricEditing));
    qs("[data-metric-dashboard-edit-label]", edit).textContent = metricEditing ? "Done" : "Edit";
  }
  const empty = qs("[data-metric-board-empty]");
  if (empty) empty.hidden = metricFrames().some((frame) => !frame.hidden);
}

function setMetricEditing(editing) {
  metricEditing = editing;
  if (!editing && latestMetricSeries.length) renderMetricCards(latestMetricSeries);
  else applyMetricLayout();
}

function setMetricPinned(key, pinned) {
  if (!metricLayout) loadMetricLayout();
  metricLayout.pinned[key] = pinned;
  saveMetricLayout();
  applyMetricLayout();
}

function resizeMetricWidget(frame) {
  if (!metricLayout) return;
  const key = frame.dataset.metricWidget;
  const sizes = frame.dataset.widgetSizes.split(",").map(Number);
  const current = Number(metricLayout.widths[key]);
  metricLayout.widths[key] = sizes[(Math.max(0, sizes.indexOf(current)) + 1) % sizes.length];
  saveMetricLayout();
  applyMetricLayout();
}

function saveMetricOrder() {
  if (!metricLayout) return;
  metricLayout.order = metricFrames().map((frame) => frame.dataset.metricWidget);
  saveMetricLayout();
}

function setStat(name, value) {
  for (const node of qsa(`[data-stat="${name}"]`)) node.textContent = number.format(value ?? 0);
}

function updateLiveControl(status = live ? "receiving" : "paused") {
  for (const node of qsa("[data-live-status]")) node.textContent = status;
  for (const node of qsa("[data-live-action]")) node.textContent = live ? "Pause" : "Resume";
  for (const node of qsa("[data-live-toggle]")) node.setAttribute("aria-label", live ? "Pause live refresh" : "Resume live refresh");
  for (const node of qsa("[data-live-dot]")) node.classList.toggle("opacity-30", !live);
}

// The class strings below are written out in full on purpose: Tailwind scans
// this file (see the @source list in client/styles/app.css) and only emits the
// utilities it can see literally.
const cellBase = "cn-table-cell cn-table-cell-aria";

function td(value, className = "") {
  const cell = document.createElement("td");
  cell.className = `${cellBase} ${className}`.trim();
  cell.appendChild(text(value));
  return cell;
}

function eventRow(event) {
  const row = document.createElement("tr");
  row.className = "cn-table-row cursor-pointer focus:bg-accent focus:outline-none";
  row.tabIndex = 0;
  row.dataset.eventId = event.id;
  return row;
}

function eventText(event) { return event.message || (event.value !== undefined ? `${event.name} = ${event.value}${event.unit ? ` ${event.unit}` : ""}` : event.name) || "telemetry event"; }

// style-nova ships default/secondary/destructive/outline badges; severity and
// span status need two more tones, built from the same theme tokens.
const tones = {
  neutral: "cn-badge-variant-secondary",
  error: "cn-badge-variant-destructive",
  debug: "border-violet-400/40 bg-violet-400/15 text-violet-300",
  info: "border-blue-400/40 bg-blue-400/15 text-blue-300",
  warning: "border-warning/40 bg-warning/15 text-warning",
  ok: "border-primary/40 bg-primary/15 text-primary",
  trace: "border-chart-3/40 bg-chart-3/15 text-chart-3",
  metric: "border-chart-2/40 bg-chart-2/15 text-chart-2",
};

function badge(value, tone = tones.neutral) {
  const node = document.createElement("span");
  node.className = `cn-badge inline-flex w-fit shrink-0 items-center justify-center whitespace-nowrap ${tone}`;
  node.appendChild(text(value));
  return node;
}

function logTone(severity = "INFO") {
  if (/error|fatal/i.test(severity)) return tones.error;
  if (/warn/i.test(severity)) return tones.warning;
  if (/debug|trace/i.test(severity)) return tones.debug;
  if (/info/i.test(severity)) return tones.info;
  return tones.neutral;
}

function emptyRow(body, columns, message) {
  const row = document.createElement("tr");
  const cell = td(message, `py-12 text-center ${muted}`);
  cell.colSpan = columns;
  row.appendChild(cell);
  body.replaceChildren(row);
}

function renderLogs(events) {
  const body = qs("[data-log-rows]");
  if (!body) return;
  if (!events.length) return emptyRow(body, 4, "No logs match this view.");
  body.replaceChildren(...events.map((event) => {
    const row = eventRow(event);
    row.dataset.logRow = "true";
    row.dataset.traceId = event.trace_id || "";
    row.dataset.severity = (event.severity || "INFO").toUpperCase();
    if (!event.trace_id) {
      row.classList.remove("cursor-pointer");
      row.removeAttribute("tabindex");
    }
    const severity = document.createElement("td");
    severity.className = cellBase;
    severity.appendChild(badge(event.severity || "INFO", logTone(event.severity)));
    row.append(td(timeText(event.timestamp), `whitespace-nowrap font-mono text-xs ${muted}`), severity,
      td(event.service, "font-medium"), td(event.message || "—", "max-w-xl truncate"));
    return row;
  }));
  if (expandedLog) {
    const row = qsa("[data-event-id]", body).find((candidate) => candidate.dataset.eventId === expandedLog.eventID);
    if (row) renderLogInline(row, expandedLog);
    else expandedLog = null;
  }
}

function renderTraces(events) {
  const body = qs("[data-trace-rows]");
  if (!body) return;
  if (!events.length) return emptyRow(body, 7, "No spans match this view.");
  body.replaceChildren(...events.map((event) => {
    const row = eventRow(event);
    row.dataset.traceId = event.trace_id;
    const status = document.createElement("td");
    status.className = cellBase;
    status.appendChild(badge((event.severity || "OK").toLowerCase(), /error/i.test(event.severity || "") ? tones.error : tones.ok));
    row.append(td(timeText(event.timestamp), `whitespace-nowrap font-mono text-xs ${muted}`), status,
      td(event.service, "font-medium"), td(event.name || "unnamed span", "max-w-sm truncate"), td((event.kind || "internal").toLowerCase(), `text-xs ${muted}`),
      td(`${number.format(event.duration_ms || 0)} ms`, "whitespace-nowrap font-mono text-xs"), td(shortID(event.trace_id), `font-mono text-[.65rem] ${muted}`));
    return row;
  }));
  if (expandedTrace) {
    const row = qsa("[data-event-id]", body).find((candidate) => candidate.dataset.eventId === expandedTrace.eventID);
    if (row) renderTraceInline(row, expandedTrace.trace);
    else expandedTrace = null;
  }
}

function renderMetricRows(events) {
  const body = qs("[data-metric-rows]");
  if (!body) return;
  if (!events.length) return emptyRow(body, 6, "No metric points match this view.");
  body.replaceChildren(...events.map((event) => {
    const row = eventRow(event);
    row.append(td(timeText(event.timestamp), `whitespace-nowrap font-mono text-xs ${muted}`), td(event.name, "font-mono text-xs"),
      td(event.service, "font-medium"), td(event.metric_type || "number", `text-xs ${muted}`),
      td(`${number.format(event.value ?? 0)}${event.unit ? ` ${event.unit}` : ""}`, "whitespace-nowrap font-mono text-xs"),
      td(`${Object.keys(event.attributes || {}).length} fields`, `text-xs ${muted}`));
    return row;
  }));
}

function renderOverview(events) {
  const body = qs('[data-event-rows][data-signal=""]');
  if (!body) return;
  qs("[data-recent-empty]")?.remove();
  if (!events.length) return emptyRow(body, 5, "Telemetry will appear here as it arrives.");
  body.replaceChildren(...events.map((event) => {
    const row = eventRow(event);
    const signal = document.createElement("td");
    signal.className = cellBase;
    const label = event.signal === "logs" ? (event.severity || "log").toLowerCase() : event.signal.replace(/s$/, "");
    const tone = event.signal === "traces" ? tones.trace : event.signal === "metrics" ? tones.metric : /error|fatal/i.test(event.severity || "") ? tones.error : tones.neutral;
    signal.appendChild(badge(label, tone));
    row.append(td(timeText(event.timestamp), `font-mono text-xs ${muted}`), signal, td(event.service), td(eventText(event), "max-w-lg truncate"), td(shortID(event.trace_id), `font-mono text-[.65rem] ${muted}`));
    return row;
  }));
}

function renderInstances(instances) {
  const list = qs("[data-instance-list]");
  if (!list) return;
  if (!instances.length) { list.replaceChildren(); return; }
  list.replaceChildren(...instances.map((instance) => {
    const row = document.createElement("div");
    row.className = "flex items-center gap-3 rounded-xl bg-muted/40 p-3";
    const dot = document.createElement("span"); dot.className = "signal-dot";
    const names = document.createElement("div"); names.className = "min-w-0 flex-1";
    const service = document.createElement("p"); service.className = "truncate text-sm font-medium"; service.appendChild(text(instance.service));
    const id = document.createElement("p"); id.className = `truncate font-mono text-[.65rem] ${muted}`; id.appendChild(text(instance.instance || "default"));
    names.append(service, id);
    const seen = document.createElement("span"); seen.className = `text-xs ${muted}`; seen.appendChild(text(relativeTime(instance.last_seen)));
    row.append(dot, names, seen); return row;
  }));
}

function renderDashboardServiceOptions(instances) {
  const select = qs("[data-widget-log-service]");
  if (!select) return;
  const services = [...new Set((instances || []).map((instance) => instance.service).filter(Boolean))].sort();
  const wanted = dashboardLayout?.service || select.value;
  const all = el("option", "", "All services"); all.value = "";
  const options = services.map((service) => { const option = el("option", "", service); option.value = service; return option; });
  select.replaceChildren(all, ...options);
  select.value = services.includes(wanted) ? wanted : "";
  if (dashboardLayout && select.value !== wanted) dashboardLayout.service = "";
}

async function refreshDashboardLogs() {
  const host = qs("[data-widget-log-rows]");
  if (!host || !dashboardWidgetPinned("service-logs")) return;
  const service = qs("[data-widget-log-service]")?.value || "";
  const params = new URLSearchParams({ signal: "logs", limit: "6" });
  if (service) params.set("service", service);
  const events = await request(`/api/events?${params}`);
  if (!events.length) {
    host.replaceChildren(el("p", `p-5 text-sm ${muted}`, service ? `No retained logs from ${service}.` : "No retained logs yet."));
  } else {
    host.replaceChildren(...events.slice(0, 6).map((event) => {
      const row = el("button", "grid w-full grid-cols-[auto_1fr] gap-x-3 gap-y-1 px-4 py-3 text-left hover:bg-accent/50");
      row.type = "button"; row.dataset.eventId = event.id;
      row.append(el("span", `font-mono text-[.65rem] ${muted}`, timeText(event.timestamp)), el("span", "truncate text-xs font-medium", event.service || "unknown"));
      const message = el("span", "col-span-2 truncate text-sm", event.message || "log record");
      row.append(message);
      return row;
    }));
  }
  const link = qs("[data-widget-log-link]");
  if (link) link.href = service ? `/logs?service=${encodeURIComponent(service)}` : "/logs";
}

async function refreshDashboardViews() {
  const host = qs("[data-widget-view-list]");
  if (!host || !dashboardWidgetPinned("views")) return;
  const views = await request("/api/views");
  if (!views.length) {
    host.replaceChildren(el("p", `p-5 text-sm ${muted}`, "No saved views yet."));
    return;
  }
  host.replaceChildren(...views.slice(0, 6).map((view) => {
    const row = el("a", "flex items-center gap-3 px-4 py-3 hover:bg-accent/50");
    row.href = "/views";
    const copy = el("span", "min-w-0 flex-1");
    copy.append(el("span", "block truncate text-sm font-medium", view.name), el("span", `block truncate text-xs ${muted}`, view.description || `${view.panel} · ${view.query?.signal || "telemetry"}`));
    row.append(copy, el("span", `shrink-0 font-mono text-[.65rem] ${muted}`, `${view.width || 12}/12`));
    return row;
  }));
}

function filterParams(signal, paginate = false) {
  const root = signalRoot(signal);
  const params = new URLSearchParams({ signal, limit: paginate ? String(pageSize + 1) : signal === "metrics" ? "500" : "250" });
  if (paginate) params.set("offset", String((signalPages.get(signal) || 0) * pageSize));
  if (!root) return params;
  const value = (name) => qs(`[data-filter="${name}"]`, root)?.value || "";
  for (const name of ["service", "severity", "name"]) if (value(name)) params.set(name, value(name));
  if (value("query")) params.set("q", value("query"));
  if (linkedPath) params.set("rum_path", linkedPath);
  const range = value("range");
  const durations = { "15m": 15 * 60e3, "1h": 3600e3, "6h": 6 * 3600e3, "24h": 24 * 3600e3, "7d": 7 * 86400e3 };
  if (durations[range]) params.set("from", new Date(Date.now() - durations[range]).toISOString());
  if (range === "custom") {
    if (value("from")) params.set("from", new Date(value("from")).toISOString());
    if (value("to")) params.set("to", new Date(value("to")).toISOString());
  }
  return params;
}

async function refreshSummary() {
  try {
    const data = await request("/api/summary");
    const signature = `${renderGeneration}:${data.logs}:${data.errors}:${data.spans}:${data.metrics}:${(data.instances || []).map((item) => `${item.service}/${item.instance}/${item.last_seen}`).join(",")}:${(data.recent || []).map((event) => event.id).join(",")}`;
    if (signature === summarySignature) return;
    summarySignature = signature;
    setStat("logs", data.logs); setStat("errors", data.errors); setStat("spans", data.spans); setStat("metrics", data.metrics); setStat("instances", data.instances?.length);
    renderInstances(data.instances || []); renderOverview(data.recent || []);
    renderDashboardServiceOptions(data.instances || []);
    await refreshDashboardLogs();
    updateLiveControl();
  } catch { updateLiveControl("reconnecting"); }
}

async function refreshSignal(signal) {
	if (!qs(`[data-filter-signal="${signal}"]`)) return;
	// Metrics is a card board now. Its series endpoint contains the points and
	// instrument metadata the cards need; fetching the old raw table page as
	// well only transferred fifty records nobody could see.
	if (signal === "metrics" && !qs("[data-metric-rows]")) return;
  const requestID = (signalRequests.get(signal) || 0) + 1;
  signalRequests.set(signal, requestID);
  const params = filterParams(signal, true);
  const events = await request(`/api/events?${params}`);
  if (signalRequests.get(signal) !== requestID) return;
  const page = signalPages.get(signal) || 0;
  if (!events.length && page > 0) {
    signalPages.set(signal, page - 1);
    syncSignalURL(signal);
    return refreshSignal(signal);
  }
  const hasNext = events.length > pageSize;
  const visible = events.slice(0, pageSize);
  // Events are immutable; IDs fully describe whether this page needs repainting.
  const signature = `${renderGeneration}:${params}:${hasNext}:${visible.map((event) => event.id).join(",")}`;
  if (signalSignatures.get(signal) === signature) return;
  signalSignatures.set(signal, signature);
  if (signal === "logs") renderLogs(visible);
  if (signal === "traces") renderTraces(visible);
  if (signal === "metrics") renderMetricRows(visible);
  renderPagination(signal, visible.length, hasNext);
}

function renderPagination(signal, count, hasNext) {
  const root = qs(`[data-pagination="${signal}"]`);
  if (!root) return;
  const page = signalPages.get(signal) || 0;
  const first = count ? page * pageSize + 1 : 0;
  const last = page * pageSize + count;
  qs("[data-page-summary]", root).textContent = count ? `Showing ${number.format(first)}–${number.format(last)} · ${pageSize} per page` : "No matching events";
  qs("[data-page-number]", root).textContent = `Page ${number.format(page + 1)}`;
  qs('[data-page-action="previous"]', root).disabled = page === 0;
  qs('[data-page-action="next"]', root).disabled = !hasNext;
}

function updateSelect(select, values, label) {
  if (!select) return;
  const current = select.value;
  const initial = document.createElement("option"); initial.value = ""; initial.textContent = label;
  const options = [...values];
  if (current && !options.includes(current)) options.push(current);
  select.replaceChildren(initial, ...options.map((value) => { const option = document.createElement("option"); option.value = value; option.textContent = value; return option; }));
  select.value = current;
}

function applyFacets(facets) {
  if (!qs("[data-filter-signal]")) return;
  for (const select of qsa('[data-filter="service"]')) updateSelect(select, facets.services || [], "All services");
  for (const root of qsa('[data-filter-signal="logs"]')) updateSelect(qs('[data-filter="severity"]', root), facets.severities || [], "All levels");
  for (const root of qsa('[data-filter-signal="traces"]')) updateSelect(qs('[data-filter="severity"]', root), ["OK", "ERROR"], "All statuses");
  for (const select of qsa('[data-filter="name"]')) updateSelect(select, facets.metric_names || [], "All metrics");
}

async function refreshFacets(force = false) {
  if (!qs("[data-filter-signal]")) return;
  if (facetsCache) applyFacets(facetsCache);
  if (!force && facetsCache && Date.now() - facetsFetchedAt < facetsTTL) return;
  if (!facetsRequest) {
    facetsRequest = request("/api/facets")
      .then((facets) => {
        facetsCache = facets;
        facetsFetchedAt = Date.now();
        return facets;
      })
      .finally(() => { facetsRequest = null; });
  }
  applyFacets(await facetsRequest);
}

async function refreshMetrics() {
  if (!qs('[data-filter-signal="metrics"]')) return;
  const params = filterParams("metrics");
  const group = qs('[data-filter-signal="metrics"] [data-filter="group"]')?.value || "";
  params.set("group_by", group); params.set("limit", "5000");
  const series = await request(`/api/metrics/series?${params}`);
  // Avoid serialising thousands of points on every live tick. Metric points are
  // append-only, so the count and final point identify a changed series.
  const signature = `${renderGeneration}:${params}:${series.map((item) => {
    const last = item.points?.at(-1);
    return `${item.key}/${item.points?.length || 0}/${last?.timestamp || ""}/${last?.value ?? ""}`;
  }).join(",")}`;
  if (signature === metricsSignature) return;
  metricsSignature = signature;
  latestMetricSeries = series;
  if (!metricEditing) renderMetricCards(series);
}

function renderChart(series) {
  const host = qs("[data-metric-chart]");
  if (!host) return;
  const shown = series.filter((item) => item.points?.length).slice(0, palette.length);
  qs("[data-metric-series-count]").textContent = `${shown.length} ${shown.length === 1 ? "series" : "series"}`;
  if (!shown.length) { host.replaceChildren(Object.assign(document.createElement("div"), { className: `grid min-h-72 place-items-center ${muted}`, textContent: "Choose a metric or wait for points to arrive." })); qs("[data-metric-legend]").replaceChildren(); return; }
  const all = shown.flatMap((item) => item.points);
  let minX = Math.min(...all.map((p) => new Date(p.timestamp).getTime())), maxX = Math.max(...all.map((p) => new Date(p.timestamp).getTime()));
  let minY = Math.min(...all.map((p) => p.value)), maxY = Math.max(...all.map((p) => p.value));
  if (minX === maxX) { minX -= 1000; maxX += 1000; }
  if (minY === maxY) { minY -= Math.abs(minY || 1) * .1; maxY += Math.abs(maxY || 1) * .1; }
  const width = 900, height = 280, pad = { left: 64, right: 18, top: 18, bottom: 34 };
  const x = (v) => pad.left + ((new Date(v).getTime() - minX) / (maxX - minX)) * (width - pad.left - pad.right);
  const y = (v) => pad.top + (1 - (v - minY) / (maxY - minY)) * (height - pad.top - pad.bottom);
  const svg = document.createElementNS(svgNS, "svg"); svg.setAttribute("viewBox", `0 0 ${width} ${height}`); svg.setAttribute("class", "h-72 w-full overflow-visible"); svg.setAttribute("role", "img"); svg.setAttribute("aria-label", "Metric series chart");
  for (let i = 0; i < 5; i++) {
    const gy = pad.top + i * (height - pad.top - pad.bottom) / 4;
    const line = document.createElementNS(svgNS, "line"); for (const [key, value] of Object.entries({ x1: pad.left, x2: width - pad.right, y1: gy, y2: gy })) line.setAttribute(key, value); line.setAttribute("stroke", "currentColor"); line.setAttribute("class", "text-border"); svg.appendChild(line);
    const label = document.createElementNS(svgNS, "text"); label.setAttribute("x", pad.left - 10); label.setAttribute("y", gy + 4); label.setAttribute("text-anchor", "end"); label.setAttribute("class", "fill-muted-foreground text-[11px]"); label.textContent = number.format(maxY - i * (maxY - minY) / 4); svg.appendChild(label);
  }
  shown.forEach((item, index) => {
    const polyline = document.createElementNS(svgNS, "polyline"); polyline.setAttribute("fill", "none"); polyline.setAttribute("stroke", palette[index]); polyline.setAttribute("stroke-width", "2.5"); polyline.setAttribute("stroke-linejoin", "round"); polyline.setAttribute("stroke-linecap", "round"); polyline.setAttribute("points", item.points.map((p) => `${x(p.timestamp)},${y(p.value)}`).join(" ")); svg.appendChild(polyline);
    for (const point of item.points) { const circle = document.createElementNS(svgNS, "circle"); circle.setAttribute("cx", x(point.timestamp)); circle.setAttribute("cy", y(point.value)); circle.setAttribute("r", "3"); circle.setAttribute("fill", palette[index]); svg.appendChild(circle); }
  });
  const start = document.createElementNS(svgNS, "text"); start.setAttribute("x", pad.left); start.setAttribute("y", height - 8); start.setAttribute("class", "fill-muted-foreground text-[11px]"); start.textContent = new Date(minX).toLocaleTimeString(); svg.appendChild(start);
  const end = document.createElementNS(svgNS, "text"); end.setAttribute("x", width - pad.right); end.setAttribute("y", height - 8); end.setAttribute("text-anchor", "end"); end.setAttribute("class", "fill-muted-foreground text-[11px]"); end.textContent = new Date(maxX).toLocaleTimeString(); svg.appendChild(end);
  host.replaceChildren(svg);
  const legend = qs("[data-metric-legend]"); legend.replaceChildren(...shown.map((item, index) => { const node = document.createElement("span"); node.className = `inline-flex items-center gap-2 text-xs ${muted}`; const dot = document.createElement("span"); dot.className = "size-2 rounded-full"; dot.style.background = palette[index]; node.append(dot, text(item.key)); return node; }));
}

const metricNames = new Map([
  ["http.server.active_requests", "Active requests"],
  ["http.server.request.body.size", "Request body size"],
  ["http.server.request.duration", "Request duration"],
  ["http.server.response.body.size", "Response body size"],
  ["v8js.gc.duration", "Garbage collection"],
  ["v8js.memory.heap.limit", "Heap limit"],
  ["v8js.memory.heap.size", "Heap in use"],
  ["v8js.memory.heap.used", "Heap in use"],
  ["v8js.memory.space.available_size", "Heap space available"],
  ["v8js.memory.heap.space.available_size", "Heap space available"],
  ["v8js.memory.space.physical_size", "Heap physical memory"],
  ["v8js.memory.heap.space.physical_size", "Heap physical memory"],
  ["process.cpu.utilization", "Process CPU"],
  ["process.memory.usage", "Process memory"],
  ["system.cpu.utilization", "System CPU"],
  ["system.memory.usage", "System memory"],
  ["container.cpu.utilization", "Container CPU"],
  ["container.memory.usage", "Container memory"],
  ["db.client.operation.duration", "Database operation duration"],
]);

function humanMetricName(key) {
  if (metricNames.has(key)) return metricNames.get(key);
  const acronyms = new Map([["cpu", "CPU"], ["gc", "GC"], ["http", "HTTP"], ["https", "HTTPS"], ["db", "Database"], ["dns", "DNS"], ["io", "I/O"], ["jvm", "JVM"], ["v8js", "V8"]]);
  return key.split(/[._-]+/).filter(Boolean).map((part, index) => {
    const lower = part.toLowerCase();
    if (acronyms.has(lower)) return acronyms.get(lower);
    return index ? lower : lower.charAt(0).toUpperCase() + lower.slice(1);
  }).join(" ");
}

function metricCategory(key) {
  if (/^(?:postgresql|redis|mysql|mongodb|db)\./i.test(key)) return "Database";
  if (/^(?:container|docker|k8s)\./i.test(key)) return "Container";
  if (/^(?:system|host)\./i.test(key)) return "System";
  if (/^process\./i.test(key)) return "Process";
  if (/^(?:v8js|nodejs|jvm|go|dotnet|cpython)\./i.test(key)) return "Runtime";
  if (/^http\./i.test(key)) return "HTTP";
  return "Application";
}

function metricDescription(item) {
  if (/gc\.duration$/i.test(item.key)) return "Latest GC pause · spikes show collection work";
  if (/heap\.(?:size|used)$/i.test(item.key)) return "Drops show memory reclaimed by garbage collection";
  if (/\.utilization$/i.test(item.key)) return "Latest utilization";
  if (/\.duration$/i.test(item.key)) return item.type?.includes("histogram") ? "Average in the latest collection" : "Latest duration";
  if (/memory.*(?:usage|size)$/i.test(item.key)) return "Latest memory measurement";
  return `Latest ${item.type || "measurement"}`;
}

function metricPointValue(item, point) {
  if (/histogram|summary/i.test(item.type || "") && point.count) return point.value / point.count;
  return point.value;
}

function formatBytes(value) {
  if (!Number.isFinite(value)) return "—";
  if (value === 0) return "0 B";
  const units = ["B", "KB", "MB", "GB", "TB", "PB"];
  let size = Math.abs(value), index = 0;
  while (size >= 1024 && index < units.length - 1) { size /= 1024; index++; }
  const shown = size >= 100 ? Math.round(size) : size >= 10 ? Number(size.toFixed(1)) : Number(size.toFixed(2));
  return `${value < 0 ? "−" : ""}${shown} ${units[index]}`;
}

function formatMetricValue(value, unit = "", key = "") {
  if (!Number.isFinite(value)) return "—";
  const normalized = unit.trim().toLowerCase();
  if (normalized === "by" || normalized === "byte" || normalized === "bytes") return formatBytes(value);
  if (normalized === "s") return duration(value * 1000);
  if (normalized === "ms") return duration(value);
  if ((normalized === "1" || normalized === "%") && /(?:utilization|ratio|percent|usage)$/i.test(key)) {
    const percent = normalized === "%" || Math.abs(value) > 1 ? value : value * 100;
    return `${compact(percent)}%`;
  }
  const annotated = /^\{(.+)\}$/.exec(unit);
  if (annotated) return `${compact(value)} ${annotated[1].replaceAll("_", " ")}`;
  return unit ? `${compact(value)} ${unit}` : compact(value);
}

function metricPoints(item) {
  const points = (item.points || []).map((point) => ({ ...point, displayValue: metricPointValue(item, point) })).filter((point) => Number.isFinite(point.displayValue));
  // V8 reports one gauge per heap space at the same collection timestamp.
  // Guard's card is the whole heap, so add those dimensions before choosing a
  // latest value; otherwise the answer is whichever space SQLite returned
  // last (often 0 B or a few hundred KB) instead of memory in use.
  if (/^v8js\.memory\./i.test(item.key) && /^(?:by|bytes?)$/i.test(item.unit || "")) {
    const grouped = new Map();
    for (const point of points) {
      const timestamp = point.timestamp;
      const existing = grouped.get(timestamp);
      if (existing) existing.displayValue += point.displayValue;
      else grouped.set(timestamp, { ...point });
    }
    return [...grouped.values()];
  }
  return points;
}

function sampledMetricPoints(points, limit = 240) {
  if (points.length <= limit) return points;
  const sampled = [];
  for (let i = 0; i < limit; i++) sampled.push(points[Math.round(i * (points.length - 1) / (limit - 1))]);
  return sampled;
}

function metricSparkline(item, points) {
  const plot = el("div", "relative mt-3 h-20 select-none");
  plot.dataset.metricPlot = "true";
  plot.tabIndex = 0;
  plot.setAttribute("role", "img");
  plot.setAttribute("aria-label", `${humanMetricName(item.key)} over time. Use the arrow keys for exact readings.`);
  const shown = sampledMetricPoints(points);
  plot._metricPoints = shown;
  plot._metricItem = item;

  const width = 640, height = 80, pad = 4;
  let min = Math.min(...shown.map((point) => point.displayValue));
  let max = Math.max(...shown.map((point) => point.displayValue));
  if (min === max) { const spread = Math.abs(min || 1) * .08; min -= spread; max += spread; }
  const x = (index) => pad + index * (width - pad * 2) / Math.max(shown.length - 1, 1);
  const y = (value) => pad + (1 - (value - min) / (max - min)) * (height - pad * 2);
  const coordinates = shown.map((point, index) => `${x(index)},${y(point.displayValue)}`);
  const chart = document.createElementNS(svgNS, "svg");
  chart.setAttribute("viewBox", `0 0 ${width} ${height}`);
  chart.setAttribute("class", "h-20 w-full overflow-visible");
  chart.setAttribute("aria-hidden", "true");
  const area = document.createElementNS(svgNS, "path");
  area.setAttribute("d", `M${coordinates.join(" L")} L${x(shown.length - 1)},${height} L${x(0)},${height} Z`);
  area.setAttribute("class", "fill-primary/10");
  const line = document.createElementNS(svgNS, "polyline");
  line.setAttribute("points", coordinates.join(" "));
  line.setAttribute("fill", "none"); line.setAttribute("stroke", "currentColor"); line.setAttribute("stroke-width", "2.5");
  line.setAttribute("stroke-linecap", "round"); line.setAttribute("stroke-linejoin", "round"); line.setAttribute("class", "text-primary");
  const marker = document.createElementNS(svgNS, "line");
  marker.dataset.metricMarker = "true"; marker.setAttribute("y1", "0"); marker.setAttribute("y2", String(height));
  marker.setAttribute("class", "hidden stroke-foreground/40"); marker.setAttribute("stroke-width", "1");
  const dot = document.createElementNS(svgNS, "circle");
  dot.dataset.metricMarkerDot = "true"; dot.setAttribute("r", "4"); dot.setAttribute("class", "hidden fill-primary stroke-background"); dot.setAttribute("stroke-width", "2");
  chart.append(area, line, marker, dot);

  const tooltip = el("div", "pointer-events-none absolute top-0 z-10 hidden -translate-x-1/2 rounded-lg border border-border bg-popover px-3 py-2 shadow-xl");
  tooltip.dataset.metricTooltip = "true";
  tooltip.append(el("p", "whitespace-nowrap text-sm font-semibold tabular-nums"), el("p", `mt-0.5 whitespace-nowrap text-[.65rem] ${muted}`));
  plot.append(chart, tooltip);
  return plot;
}

function metricCard(item) {
  const points = metricPoints(item);
  const frame = el("article", "group/widget relative min-w-0");
  frame.dataset.metricWidget = item.key;
  frame.dataset.widgetFrame = "true";
  frame.dataset.widgetSizes = "4,6,8,12";
  frame.style.setProperty("--widget-span", "4");

  const editBadge = el("div", "absolute -left-2 -top-3 z-20 hidden items-center gap-2 rounded-full border border-border bg-popover px-3 py-1.5 text-xs font-medium shadow-lg");
  editBadge.dataset.widgetEditBadge = "true";
  editBadge.append(el("span", "size-2 rounded-full bg-primary"), text(humanMetricName(item.key)));
  const controls = el("div", "absolute -right-2 -top-3 z-20 hidden items-center gap-1"); controls.dataset.widgetEditControls = "true";
  const resize = el("button", "rounded-full border border-border bg-popover px-2.5 py-1.5 font-mono text-[.65rem] text-muted-foreground shadow-lg hover:text-foreground");
  resize.type = "button"; resize.dataset.metricWidgetResize = "true"; resize.setAttribute("aria-label", `Resize ${humanMetricName(item.key)} card`);
  resize.append(el("span", "", "4"), text("/12")); resize.firstElementChild.dataset.widgetSize = "true";
  const remove = el("button", "grid size-8 place-items-center rounded-full border border-border bg-popover text-muted-foreground shadow-lg hover:bg-destructive hover:text-white", "×");
  remove.type = "button"; remove.dataset.metricWidgetRemove = "true"; remove.setAttribute("aria-label", `Remove ${humanMetricName(item.key)} card`);
  controls.append(resize, remove);

  const card = el("div", "h-full overflow-hidden rounded-xl bg-card text-card-foreground ring-1 ring-foreground/10");
  const content = el("div", "p-4");
  const heading = el("div", "flex items-start justify-between gap-4");
  const names = el("div", "min-w-0");
  names.append(el("p", "truncate text-sm font-semibold", humanMetricName(item.key)), el("p", `mt-0.5 truncate font-mono text-[.65rem] ${muted}`, item.key));
  heading.append(names, el("span", "cn-badge shrink-0 border-transparent bg-primary/10 text-primary", metricCategory(item.key)));
  content.append(heading);
  if (!points.length) content.append(el("p", `mt-5 text-sm ${muted}`, "No points in this window."));
  else {
    const values = points.map((point) => point.displayValue);
    const latest = points.at(-1);
    const avg = values.reduce((sum, value) => sum + value, 0) / values.length;
    content.append(el("p", "mt-3 text-2xl font-semibold tracking-tight tabular-nums", formatMetricValue(latest.displayValue, item.unit, item.key)));
    content.append(el("p", `mt-0.5 text-xs ${muted}`, metricDescription(item)));
    content.append(metricSparkline(item, points));
    const stats = el("dl", "mt-3 grid grid-cols-3 gap-2 border-t border-border pt-3");
    for (const [label, value] of [["Average", avg], ["Low", Math.min(...values)], ["High", Math.max(...values)]]) {
      const stat = el("div", "min-w-0");
      stat.append(el("dt", `text-[.65rem] uppercase tracking-wider ${muted}`, label), el("dd", "mt-0.5 truncate text-xs font-medium tabular-nums", formatMetricValue(value, item.unit, item.key)));
      stats.append(stat);
    }
    content.append(stats);
  }
  card.append(content); frame.append(editBadge, controls, card); return frame;
}

function metricCatalogueItem(item) {
  const row = el("div", "flex items-center gap-3 rounded-xl border border-border p-3");
  row.dataset.metricCatalogueItem = item.key;
  row.append(el("span", "grid size-9 shrink-0 place-items-center rounded-lg bg-primary/10 text-xs font-semibold text-primary", metricCategory(item.key).slice(0, 2).toUpperCase()));
  const copy = el("div", "min-w-0 flex-1");
  copy.append(el("p", "truncate text-sm font-medium", humanMetricName(item.key)), el("p", `mt-0.5 truncate font-mono text-[.65rem] ${muted}`, item.key));
  const size = el("span", `shrink-0 font-mono text-[.65rem] ${muted}`, "4/12"); size.dataset.metricCatalogueSize = "true";
  const button = el("button", "cn-button inline-flex shrink-0 items-center justify-center whitespace-nowrap cn-button-variant-outline cn-button-size-sm");
  button.type = "button"; button.dataset.metricWidgetPin = item.key; button.append(el("span", "", "Pin")); button.firstElementChild.dataset.metricWidgetPinLabel = "true";
  row.append(copy, size, button); return row;
}

function renderMetricCards(series) {
  const host = qs("[data-metric-widget-grid]");
  const catalogue = qs("[data-metric-catalogue]");
  if (!host || !catalogue) return;
  loadMetricLayout(series);
  const empty = qs("[data-metric-board-empty]", host) || el("p", `col-span-full rounded-xl border border-dashed border-border p-8 text-center text-sm ${muted}`, "No metrics are pinned. Add one from the metric library.");
  empty.dataset.metricBoardEmpty = "true";
  host.replaceChildren(empty, ...series.map(metricCard));
  catalogue.replaceChildren(...series.map(metricCatalogueItem));
  applyMetricLayout();
}

function showMetricTooltip(plot, index) {
  const points = plot?._metricPoints || [];
  if (!points.length) return;
  const at = Math.max(0, Math.min(points.length - 1, index));
  plot._metricIndex = at;
  const point = points[at], item = plot._metricItem;
  const ratio = points.length === 1 ? .5 : at / (points.length - 1);
  const marker = qs("[data-metric-marker]", plot), dot = qs("[data-metric-marker-dot]", plot), tooltip = qs("[data-metric-tooltip]", plot);
  const values = points.map((candidate) => candidate.displayValue);
  let min = Math.min(...values), max = Math.max(...values);
  if (min === max) { const spread = Math.abs(min || 1) * .08; min -= spread; max += spread; }
  const x = 4 + ratio * 632, y = 4 + (1 - (point.displayValue - min) / (max - min)) * 72;
  marker.classList.remove("hidden"); marker.setAttribute("x1", String(x)); marker.setAttribute("x2", String(x));
  dot.classList.remove("hidden"); dot.setAttribute("cx", String(x)); dot.setAttribute("cy", String(y));
  tooltip.classList.remove("hidden"); tooltip.style.left = `${Math.max(14, Math.min(86, ratio * 100))}%`;
  tooltip.children[0].textContent = formatMetricValue(point.displayValue, item.unit, item.key);
  tooltip.children[1].textContent = new Date(point.timestamp).toLocaleString();
  plot.setAttribute("aria-label", `${humanMetricName(item.key)}: ${tooltip.children[0].textContent}, ${tooltip.children[1].textContent}. Use left and right arrow keys for other readings.`);
}

function hideMetricTooltip(plot) {
  qs("[data-metric-tooltip]", plot)?.classList.add("hidden");
  qs("[data-metric-marker]", plot)?.classList.add("hidden");
  qs("[data-metric-marker-dot]", plot)?.classList.add("hidden");
}

function detailField(label, value) {
  const node = document.createElement("div"); node.className = "min-w-0 bg-card p-3";
  const key = document.createElement("p"); key.className = `text-[.65rem] font-semibold uppercase tracking-[.15em] ${muted}`; key.appendChild(text(label));
  const content = document.createElement("p"); content.className = "mt-1 break-words font-mono text-xs"; content.appendChild(text(value || "—"));
  node.append(key, content); return node;
}

// A trace-linked log expands only the trace relationship. The row already says
// what the log said; repeating its raw record and OTLP attributes here obscures
// the timeline somebody opened it to inspect.
let expandedLog = null;
let logLoadGeneration = 0;

function renderLogInline(row, state = null) {
  qs("[data-log-inline]")?.remove();
  const template = qs("[data-log-inline-template]");
  if (!template || !row) return;
  const inline = template.content.firstElementChild.cloneNode(true);
  row.setAttribute("aria-expanded", "true");
  row.after(inline);
  qs("[data-log-trace-id]", inline).textContent = state?.traceID || row.dataset.traceId;
  if (state?.traceError) {
    qs("[data-log-waterfall]", inline).replaceChildren(el("p", `py-6 text-center text-sm ${muted}`, state.traceError));
    return;
  }
  if (!state?.trace) return;
  const trace = state.trace;
  qs("[data-log-trace-duration]", inline).textContent = `${number.format(Math.round(trace.duration_ms))} ms · ${trace.spans.length} spans`;
  qs("[data-log-trace-services]", inline).textContent = `${trace.services.join(" · ")}${trace.errors ? ` · ${trace.errors} errored` : ""}`;
  // The Logs page is intentionally drawer-free. Its waterfall is context for
  // the log, not a second route into raw span detail.
  drawWaterfall(qs("[data-log-waterfall]", inline), trace);
}

async function showLog(row) {
  if (!row?.dataset.traceId) return;
  if (expandedLog?.eventID === row.dataset.eventId) {
    collapseLog();
    return;
  }
  collapseTrace();
  collapseLog();
  const generation = ++logLoadGeneration;
  expandedLog = { eventID: row.dataset.eventId, traceID: row.dataset.traceId, trace: null, traceError: "" };
  renderLogInline(row, expandedLog);
  try {
    const trace = await request(`/api/traces/${encodeURIComponent(row.dataset.traceId)}`);
    if (generation !== logLoadGeneration || expandedLog?.eventID !== row.dataset.eventId) return;
    expandedLog.trace = trace;
  } catch {
    if (generation !== logLoadGeneration || expandedLog?.eventID !== row.dataset.eventId) return;
    expandedLog.traceError = "Trace timeline is unavailable for this log.";
  }
  renderLogInline(row, expandedLog);
}

function collapseLog() {
  logLoadGeneration++;
  qs('[data-log-rows] [aria-expanded="true"]')?.setAttribute("aria-expanded", "false");
  qs("[data-log-inline]")?.remove();
  expandedLog = null;
}

function globalDetailShell() {
  return qs('[data-detail-shell][data-detail-scope="global"]');
}

async function openDetail(id, shell = globalDetailShell()) {
  if (!shell) return;
  const event = await request(`/api/events/${id}`);
  qs("[data-detail-eyebrow]", shell).textContent = `${event.signal.replace(/s$/, "")} detail`;
  qs("[data-detail-title]", shell).textContent = eventText(event);
  // 1px of the border colour shows between the cells as the grid gap.
  const grid = document.createElement("div"); grid.className = "grid grid-cols-2 gap-px overflow-hidden rounded-xl border border-border bg-border";
  const fields = [["Timestamp", new Date(event.timestamp).toLocaleString()], ["Received", new Date(event.received_at).toLocaleString()], ["Service", event.service], ["Instance", event.instance], ["Scope", event.scope], ["Severity / status", event.severity], ["Span kind", event.kind], ["Duration", event.duration_ms ? `${event.duration_ms} ms` : ""], ["Metric type", event.metric_type], ["Value", event.value !== undefined ? `${event.value}${event.unit ? ` ${event.unit}` : ""}` : ""], ["Trace ID", event.trace_id], ["Span ID", event.span_id], ["Parent span", event.parent_span_id]];
  grid.append(...fields.filter(([, value]) => value !== "" && value !== undefined).map(([label, value]) => detailField(label, value)));
  const attrs = document.createElement("section"); const heading = document.createElement("h3"); heading.className = "mb-3 font-medium"; heading.appendChild(text(`Attributes · ${Object.keys(event.attributes || {}).length}`));
  const pre = document.createElement("pre"); pre.className = "overflow-x-auto rounded-xl bg-code p-4 font-mono text-xs leading-6 text-code-foreground"; pre.appendChild(text(JSON.stringify(event.attributes || {}, null, 2))); attrs.append(heading, pre);
  qs("[data-detail-content]", shell).replaceChildren(grid, attrs); shell.classList.add("open"); document.body.classList.add("overflow-hidden");
  // Arriving from a drill-down leaves a list to go back to; arriving from a
  // table does not, and an inert button would be worse than none.
  qs("[data-detail-footer]", shell).hidden = shell.dataset.detailScope === "trace" || !lastDrill;
}

// A row expands its whole trace immediately underneath itself. Choosing one
// span from that waterfall still opens raw event detail, so the interaction
// moves from request to span without taking the list away or blurring it.
//
// A span list answers "what happened"; only the timeline answers "what was
// waiting on what", which is the question a slow request actually raises. The
// card is on the traces page only — the same renderer serves the waterfall
// panel on /views, from the same endpoint.
let expandedTrace = null;
let traceLoadGeneration = 0;

function renderTraceInline(row, trace = null) {
  qs("[data-trace-inline]")?.remove();
  const template = qs("[data-trace-inline-template]");
  if (!template || !row) return;
  const inline = template.content.firstElementChild.cloneNode(true);
  inline.dataset.traceID = row.dataset.traceId;
  row.setAttribute("aria-expanded", "true");
  row.after(inline);
  if (!trace) return;
  qs("[data-trace-id]", inline).textContent = trace.trace_id;
  qs("[data-trace-duration]", inline).textContent = `${number.format(Math.round(trace.duration_ms))} ms · ${trace.spans.length} spans`;
  qs("[data-trace-services]", inline).textContent = `${trace.services.join(" · ")}${trace.errors ? ` · ${trace.errors} errored` : ""}`;
  drawWaterfall(qs("[data-waterfall]", inline), trace, { onSpan: (id) => openDetail(id).catch(() => {}) });
}

async function showTrace(traceID, row) {
  if (!row) return;
  if (expandedTrace?.eventID === row.dataset.eventId) {
    collapseTrace();
    return;
  }
  collapseLog();
  collapseTrace();
  const generation = ++traceLoadGeneration;
  expandedTrace = { traceID, eventID: row.dataset.eventId, trace: null };
  renderTraceInline(row);
  const trace = await request(`/api/traces/${encodeURIComponent(traceID)}`);
  if (generation !== traceLoadGeneration || expandedTrace?.eventID !== row.dataset.eventId) return;
  expandedTrace.trace = trace;
  renderTraceInline(row, trace);
}

function openEventRow(row) {
  if (row.closest("[data-log-rows]")) return showLog(row);
  if (row.dataset.traceId) return showTrace(row.dataset.traceId, row);
  return openDetail(row.dataset.eventId);
}

function collapseTrace() {
  traceLoadGeneration++;
  const openRow = qs('[data-trace-rows] [aria-expanded="true"]');
  openRow?.setAttribute("aria-expanded", "false");
  qs("[data-trace-inline]")?.remove();
  expandedTrace = null;
}

function closeDetail(shell = globalDetailShell()) {
  shell?.classList.remove("open");
  if (!qs('[data-detail-shell].open')) document.body.classList.remove("overflow-hidden");
  lastDrill = null;
  qs("[data-detail-footer]", shell)?.toggleAttribute("hidden", true);
}

// The drawer's second mode: the events behind one mark on a chart.
//
// A bar is an aggregate — 217 events, not one — so clicking it cannot open
// "the" event. It opens the list, and a row in that list opens the event. The
// list is remembered so the detail view has somewhere to go back to.
let lastDrill = null;

async function openDrill(request, datum = {}) {
  const drill = await request_("/api/views/drill", request);
  lastDrill = { request, datum, drill };
  renderDrill();
  globalDetailShell().classList.add("open");
  document.body.classList.add("overflow-hidden");
}

function request_(path, body) {
  return request(path, { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(body) });
}

function renderDrill() {
  if (!lastDrill) return;
  const { datum, drill } = lastDrill;
  const shown = drill.events.length;
  const shell = globalDetailShell();
  qs("[data-detail-eyebrow]", shell).textContent = shown === drill.total
    ? `${number.format(drill.total)} ${drill.total === 1 ? "event" : "events"}`
    : `${number.format(shown)} of ${number.format(drill.total)} events`;
  qs("[data-detail-title]", shell).textContent = datum.title || "Selected events";
  qs("[data-detail-footer]", shell).hidden = true;

  const template = qs("[data-drill-row-template]");
  const list = document.createElement("div");
  list.className = "-mt-2";
  if (!shown) {
    list.appendChild(Object.assign(document.createElement("p"), {
      className: `py-8 text-center text-sm ${muted}`,
      textContent: "No events behind this mark.",
    }));
  }
  for (const event of drill.events) {
    const row = template.content.firstElementChild.cloneNode(true);
    row.dataset.eventId = event.id;
    qs("[data-drill-time]", row).textContent = timeText(event.timestamp);
    const badge = qs("[data-drill-badge]", row);
    const label = event.signal === "logs" ? (event.severity || "log").toLowerCase() : event.signal.replace(/s$/, "");
    badge.className = `cn-badge inline-flex w-fit shrink-0 items-center justify-center whitespace-nowrap ${
      event.signal === "traces" ? tones.trace : event.signal === "metrics" ? tones.metric
        : /error|fatal/i.test(event.severity || "") ? tones.error : tones.neutral}`;
    badge.textContent = label;
    qs("[data-drill-text]", row).textContent = `${event.service} · ${eventText(event)}`;
    qs("[data-drill-value]", row).textContent = event.duration_ms
      ? `${number.format(Math.round(event.duration_ms))} ms`
      : event.value !== undefined ? number.format(event.value) : "";
    list.appendChild(row);
  }
  const content = qs("[data-detail-content]", shell);
  content.replaceChildren(list);
  content.scrollTop = 0;
}

// views.js opens the drawer when a chart is clicked — one drawer per document,
// owned here, reachable from there. Both entry points are published rather than
// imported, because guard.js imports views.js and the reverse would be a cycle.
globalThis.guardOpenDetail = (id) => openDetail(id).catch(() => {});
globalThis.guardOpenDrill = (request, datum) => openDrill(request, datum).catch((failure) => {
  const shell = globalDetailShell();
  qs("[data-detail-eyebrow]", shell).textContent = "Could not read these events";
  qs("[data-detail-title]", shell).textContent = failure.message;
  qs("[data-detail-content]", shell).replaceChildren();
  shell.classList.add("open");
});

async function loadSettings() {
  const form = qs("[data-settings-form]"); if (!form) return;
	if (form.dataset.loaded === "true") return;
  const settings = await request("/api/settings");
  for (const key of ["database_path", "retention_hours", "max_events", "analytics_rollup_days", "analytics_seen_days"]) qs(`[data-setting="${key}"]`, form).value = settings[key] ?? "";
  qs('[data-setting="token"]', form).value = sessionStorage.getItem("guard.token") || "";
	form.dataset.loaded = "true";
}

async function saveSettings(form) {
  const status = qs("[data-settings-status]", form); status.textContent = "Saving…";
  try {
    // Every number the form holds goes on every save: the store reads a zero as
    // "leave it alone", so a partial body would look like a save that worked.
    const number_ = (key) => Number(qs(`[data-setting="${key}"]`, form).value);
    const value = {
      retention_hours: number_("retention_hours"), max_events: number_("max_events"),
      analytics_rollup_days: number_("analytics_rollup_days"), analytics_seen_days: number_("analytics_seen_days"),
    };
    await request("/api/settings", { method: "PUT", headers: adminHeaders(), body: JSON.stringify(value) }); status.textContent = "Saved and cleanup applied."; await refreshSummary();
  } catch (error) { status.textContent = error.message; }
}

async function purgeNow() {
  const status = qs("[data-settings-status]"); status.textContent = "Cleaning…";
  try { const value = await request("/api/settings/purge", { method: "POST", headers: adminHeaders() }); status.textContent = `Cleanup complete · ${number.format(value.removed)} removed.`; await refreshSummary(); }
  catch (error) { status.textContent = error.message; }
}

async function refreshPage({ facets = false } = {}) {
  const work = [refreshSignal("logs"), refreshSignal("traces"), refreshSignal("metrics"), refreshMetrics(), loadSettings()];
  if (qs("[data-stat]") || qs("[data-instance-list]")) work.push(refreshSummary());
  // The overview widget is live; the editor is mount-and-write so a background
  // refresh never replaces fields while somebody is typing in them.
  if ((dashboardWidgetPinned("health") && qs("[data-status-widget]")) || (facets && qs("[data-check-rows]"))) work.push(refreshHealthChecks());
  if (qs("[data-view-grid]")) work.push(refreshViews());
  if (facets && dashboardWidgetPinned("views")) work.push(refreshDashboardViews());
  if (qs("[data-cluster-rows]") || qs("[data-cluster-cards]") || (qs("[data-topology]") && (dashboardWidgetPinned("cluster-map") || dashboardWidgetPinned("cluster")))) work.push(refreshCluster());
  // One machine's own page reads one machine, on the same tick as everything else.
  if (qs("[data-machine-card]")) work.push(refreshMachine());
  // Forced only alongside a facets refresh — a mount or an explicit click —
  // because behind this one is a provider's API, not guard's database.
  if (qs("[data-registry-overview]")) work.push(refreshRegistries(facets));
  if (qs("[data-cloud-accounts]") || qs("[data-import-rows]")) work.push(refreshCloud());
  // Guard's own SQLite, but it changes when a person presses something rather
  // than when telemetry arrives — so it is read on a mount and after a change,
  // not on the tick.
  if (facets && qs("[data-member-rows]")) work.push(refreshMembers());
  // Guard's own configuration: it changes when somebody saves the form, never on
  // its own — so a mount and a press, not the tick.
  if (facets && qs("[data-config-groups]")) work.push(refreshConfig());
  // What a backup would hold: counts of guard's own rows, which move when
  // somebody adds a machine rather than when telemetry arrives.
  if (facets && qs("[data-backup-sections]")) work.push(refreshBackup());
  // The alert rules and their destinations: guard's own SQLite, but read on a
  // mount and after a change rather than on the tick. Nothing here moves
  // except when somebody edits it — and a row being redrawn under a cursor
  // mid-edit is the one thing this page must not do.
  if (facets && qs("[data-webhooks]")) work.push(refreshAlerts());
  // The deploys page is both: the groups and templates move only when somebody
  // saves a form, and a run moves by itself, machine by machine. Watching that
  // happen is the reason to deploy from here, so it is on the tick — one small
  // query for the runs still going, and the lists only on a mount.
  if (qs("[data-deploy-rows]")) work.push(refreshDeploys(facets));
  // The storage page reads the provider, so it refreshes on a mount or an
  // explicit press — never on the three-second tick.
  if (facets && qs("[data-storage-rows]")) work.push(refreshStorage());
  // The secrets page is guard's own SQLite and moves only when somebody edits
  // it — and a value being redrawn under a cursor mid-edit is the one thing
  // this page must not do. So: on a mount and after a change, never on the
  // tick.
  if (facets && qs("[data-secret-envs]")) work.push(refreshSecrets());
  // Analytics is a rollup keyed by whole UTC days, read over a window of at
  // least one of them: a three-second tick would redraw the same numbers a
  // thousand times an hour. A mount and a press, like the pages behind an API.
  if (facets && qs("[data-analytics-page]")) work.push(refreshAnalytics());
  if (facets) {
    renderLinkedFilter();
    work.push(refreshFacets());
  }
  await Promise.allSettled(work);
}

async function liveTick() {
  if (live && !refreshInFlight && document.visibilityState === "visible" && Date.now() - lastInteraction > 500) {
    refreshInFlight = true;
    try { await refreshPage(); } finally { refreshInFlight = false; }
  }
  liveTimer = setTimeout(liveTick, 3000);
}

// ---------------------------------------------------------------------------
// Is there a newer guard?
//
// The sidebar lives outside the outlet, so this is set up once and survives
// every navigation. It reads guard's own cached answer — the server asks GitHub
// on a fifteen-minute timer, so this can be cheap and frequent without spending
// the sixty requests an hour an unauthenticated address gets.
// ---------------------------------------------------------------------------

let updateState = null;

async function refreshUpdate() {
  // Either surface is reason enough to ask. The card is in the layout and the
  // panel is on one page, and returning early when the card is missing would
  // leave Settings -> Info permanently drawing dashes on any instance whose
  // sidebar is not rendered.
  if (!qs("[data-update-card]") && !qs("[data-info-version]")) return;
  try {
    updateState = await request("/api/update");
  } catch {
    // A dashboard that cannot ask about updates is a dashboard that says
    // nothing about them, which is what the card already does.
    return;
  }
  renderUpdate();
  renderInfo();
}

function renderUpdate() {
  const card = qs("[data-update-card]");
  if (!card || !updateState) return;
  const state = updateState;
  card.hidden = !state.available;
  if (!state.available) return;

  const link = qs("[data-update-link]", card);
  link.textContent = state.latest || "";
  link.href = state.url || "#";

  const actions = qs("[data-update-actions]", card);
  const note = qs("[data-update-note]", card);
  const status = qs("[data-update-status]", card);

  // Already asked for: the file names the new release and the updater has it
  // from here. Saying "installing" would be a claim about another process on
  // another timer; "asked for" is what guard actually knows.
  if (state.wanted && state.wanted === state.latest) {
    actions.hidden = true;
    note.hidden = false;
    note.textContent = `${state.latest} requested — installation is starting now.`;
    return;
  }
  // No /etc/guard on this box, so there is nothing to write and no unit to act
  // on it. The release is still worth naming, with a link to it.
  if (!state.managed) {
    actions.hidden = true;
    note.hidden = false;
    note.textContent = "This instance updates itself elsewhere — see the release.";
    return;
  }
  note.hidden = true;
  actions.hidden = false;
  status.textContent = "";
}

async function applyUpdate() {
  // Pressed from the sidebar card or from Settings -> Info; whichever is on
  // screen owns the button and the line under it.
  const onPage = Boolean(qs("[data-info-version]"));
  const status = qs(onPage ? "[data-info-status]" : "[data-update-status]");
  const button = qs(onPage ? "[data-info-update]" : "[data-update-apply]");
  if (!updateState?.latest || !status || !button) return;
  button.disabled = true;
  status.textContent = "asking…";
  try {
    updateState = await request("/api/update", {
      method: "POST", headers: adminHeaders(),
      body: JSON.stringify({ version: updateState.latest }),
    });
    status.textContent = "";
    renderUpdate();
    renderInfo();
  } catch (failure) {
    status.textContent = failure.message;
  } finally {
    button.disabled = false;
  }
}

// Settings -> Info. The sidebar card appears only when there is news, which is
// right for a sidebar and useless for the page somebody opens *to check*. Same
// state object, drawn in full: what is running, what the channel says, when
// guard last asked, and what the version file pins.
function renderInfo() {
  const panel = qs("[data-info-version]");
  if (!panel) return;
  const state = updateState || {};
  const dash = (value) => (value && String(value).trim()) || "—";

  qs("[data-info-current]").textContent = dash(state.current);
  const latest = qs("[data-info-latest]");
  latest.textContent = dash(state.latest);
  // No release yet means nowhere to point: a link to "#" that scrolls the page
  // is worse than text.
  if (state.url) {
    latest.href = state.url;
    latest.removeAttribute("aria-disabled");
  } else {
    latest.removeAttribute("href");
  }
  qs("[data-info-checked]").textContent = state.checked_at ? relativeTime(state.checked_at) : "never";
  qs("[data-info-wanted]").textContent = dash(state.wanted);

  const summary = qs("[data-info-summary]");
  const update = qs("[data-info-update]");
  update.hidden = true;
  if (state.error) {
    // Named rather than folded into "up to date": a check that could not reach
    // GitHub knows nothing, and saying nothing is new would be a guess.
    summary.hidden = false;
    summary.textContent = `Could not reach the release repository — ${state.error}`;
    return;
  }
  if (state.development) {
    summary.hidden = false;
    summary.textContent = "This is a development build, so there is nothing to compare it against.";
    return;
  }
  if (!state.latest) {
    summary.hidden = true;
    return;
  }
  summary.hidden = false;
  if (!state.available) {
    summary.textContent = `Running the current release, ${state.latest}.`;
    return;
  }
  if (state.wanted && state.wanted === state.latest) {
    summary.textContent = `${state.latest} requested — installation is starting now.`;
    return;
  }
  if (!state.managed) {
    summary.textContent = "A newer release exists, but this instance updates itself elsewhere.";
    return;
  }
  summary.textContent = `${state.latest} is available.`;
  update.hidden = false;
}

// The box guard is on. Read on mount rather than on the tick: it describes
// hardware and a database size, neither of which moves in three seconds, and a
// settings page that re-fetched on every pass would be spending requests to
// redraw the same words.
async function refreshHost() {
  const panel = qs("[data-info-host]");
  if (!panel) return;
  const problem = qs("[data-info-host-error]");
  let host;
  try {
    host = await request("/api/info");
  } catch (failure) {
    problem.hidden = false;
    problem.textContent = failure.message;
    return;
  }
  problem.hidden = true;

  // Unmeasurable is a dash, never a zero — the has_* flags are the server
  // saying which is which, and "0% of memory used" is a number somebody acts
  // on. Off Linux most of this is legitimately empty.
  const rows = [
    ["Operating system", host.distro || `${host.os || "—"} ${host.arch || ""}`.trim()],
    ["Kernel", host.kernel || "—"],
    ["Hostname", host.hostname || "—"],
    ["CPU", host.cpu_model ? `${host.cpu_model} · ${host.cpu_count} cores` : (host.cpu_count ? `${host.cpu_count} cores` : "—")],
    ["Load", host.has_cpu
      ? `${host.load_1.toFixed(2)} · ${host.load_5.toFixed(2)} · ${host.load_15.toFixed(2)}` +
        (host.cpu_count ? ` over ${host.cpu_count}` : "")
      : "—"],
    ["Memory", host.has_memory
      ? `${bytes(host.mem_used_kb * 1024)} of ${bytes(host.mem_total_kb * 1024)}` +
        ` (${Math.round((host.mem_used_kb / host.mem_total_kb) * 100)}%)`
      : "—"],
    ["Disk", host.has_disk
      ? `${bytes(host.disk_used_kb * 1024)} of ${bytes(host.disk_total_kb * 1024)}` +
        ` (${Math.round((host.disk_used_kb / host.disk_total_kb) * 100)}%) on ${host.disk_path}`
      : "—"],
    ["Database", host.database_path
      ? `${bytes(host.database_bytes)} at ${host.database_path}`
      : "—"],
    ["Host uptime", since(host.host_uptime_seconds)],
    ["Guard uptime", since(host.process_uptime_seconds)],
    ["Runtime", `${host.go_version || "—"} · ${host.goroutines} goroutines · ${bytes(host.heap_bytes)} heap`],
    // Both explain something the page above cannot: no supervisor means the
    // restart button is absent, and a container is why there is no
    // /etc/guard and so no update button.
    ["Process", [host.supervised ? "supervised" : "not supervised",
      host.in_container ? "in a container" : null].filter(Boolean).join(" · ")],
  ];

  panel.replaceChildren(...rows.map(([label, value]) => {
    const cell = el("div");
    cell.append(
      el("dt", "text-xs font-medium uppercase tracking-wider text-muted-foreground", label),
      el("dd", "mt-1 text-sm break-words", value || "—"),
    );
    return cell;
  }));
}

async function checkForUpdates() {
  const button = qs("[data-info-check]");
  const status = qs("[data-info-status]");
  if (!button) return;
  button.disabled = true;
  status.textContent = "asking…";
  try {
    updateState = await request("/api/update/check", { method: "POST", headers: adminHeaders() });
    status.textContent = "";
    renderUpdate();
    renderInfo();
  } catch (failure) {
    status.textContent = failure.message;
  } finally {
    button.disabled = false;
  }
}

// The tabs inside components.HowTo.
//
// Opening and closing the dialog is a checkbox and a sibling selector, with no
// script at all. Only this part is scripted, and only because the alternative
// is not available: showing panel N from radio N needs a `peer-checked/N:`
// class assembled from an index, and Tailwind emits no class it cannot find
// written out. Delegated on document like everything else here, so it keeps
// working after a client-side navigation replaces the outlet.
document.addEventListener("click", (event) => {
  const tab = event.target.closest("[data-howto-tab]");
  if (!tab) return;
  const dialog = tab.closest("[data-howto]");
  if (!dialog) return;
  const wanted = tab.dataset.howtoTab;
  for (const control of qsa("[data-howto-tab]", dialog)) {
    const active = control.dataset.howtoTab === wanted;
    control.dataset.active = String(active);
    control.setAttribute("aria-selected", String(active));
  }
  for (const panel of qsa("[data-howto-panel]", dialog)) {
    panel.hidden = panel.dataset.howtoPanel !== wanted;
  }
});

document.addEventListener("click", (event) => {
  if (event.target.closest("[data-update-apply]")) applyUpdate();
  if (event.target.closest("[data-info-check]")) checkForUpdates();
  if (event.target.closest("[data-info-update]")) applyUpdate();
});

// On a mount, and then rarely: the answer changes when somebody publishes a
// release, which is not something a page needs to learn about in seconds.
setInterval(refreshUpdate, 5 * 60_000);

globalThis.guardPageMount = (page) => {
  // The cold document can start fetching as soon as guard.js executes, without
  // waiting for the WASM binary. Its later Mount consumes that same promise;
  // AOT navigations start a fresh page-specific load here.
  // Live/pause belongs to this browser and is restored from localStorage.
  // Every client navigation recreates the layout with its neutral SSR text,
  // so apply the browser-owned value synchronously before any fetch finishes.
  updateLiveControl();
  refreshUpdate();
  renderGeneration++;
  // Before anything asks for rows: the URL is what says which sessions this
  // page is about, and the first request must already know.
  readLinkedFilter();
  readSignalURLState(page);
  syncSignalURL(page);
  mountSignalList();
  if (page === "home") applyDashboardLayout();
  if (page === initializedPage && initialRefresh) {
    const pending = initialRefresh;
    initialRefresh = null;
    // That eager pass started when guard.js was evaluated — before the WASM
    // had rendered anything — so every branch of refreshPage that asks "is
    // this page's markup here?" answered no, and pages like /storage and
    // /settings/alerts never fetched at all. Their first paint said "Loading…"
    // and stayed there. So the page's own pass runs here as well; the store
    // shares in-flight loads by key, so this is not a second round of
    // requests, and everything it does put in the store is already drawn.
    return Promise.allSettled([pending, refreshPage({ facets: true }), refreshHost()]);
  }
  initializedPage = page;
  if (page === "info") return refreshHost();
  if (page === "views") return mountViews();
  return refreshPage({ facets: true });
};
globalThis.guardPageUnmount = () => {
  // The outlet is about to throw this page's DOM away. The store keeps track of
  // what is on screen so it can skip redundant redraws; from here, nothing is.
  screenCleared();
  signalListObserver?.disconnect();
  signalListObserver = undefined;
  // Every open event stream belongs to the page that is being thrown away.
  closeDeployStreams();
  closeInteractiveTerminal();
  clearTimeout(filterTimer);
  filterTimer = undefined;
  for (const signal of signalRequests.keys()) signalRequests.set(signal, signalRequests.get(signal) + 1);
  unmountViews();
  dashboardDragging = null;
  dashboardEditing = false;
  dragMovedAt = null;
  metricDragging = null;
  metricEditing = false;
  metricLayout = null;
  latestMetricSeries = [];
  traceLoadGeneration++;
  expandedTrace = null;
  logLoadGeneration++;
  expandedLog = null;
};

for (const eventName of ["scroll", "wheel", "touchmove", "pointermove"]) {
  document.addEventListener(eventName, () => { lastInteraction = Date.now(); }, { passive: true });
}

// Native drag-and-drop mirrors moving apps on a phone: edit mode turns the
// whole card into the handle, then persistence waits until the drop.
//
// A move reflows the grid, and on a twelve-column board of mixed widths the
// reflow can slide a different card under a pointer that has not moved — which,
// answered, moves the card straight back. Chrome fires dragover every ~50ms
// while the pointer holds still, so that was an endless two-step of whole-board
// layouts that locked the tab. So a card moves again only once the pointer has.
const DRAG_SLOP = 12;
let dragMovedAt = null;

document.addEventListener("dragstart", (event) => {
  dragMovedAt = null;
  if (metricEditing && !event.target.closest?.("[data-widget-edit-controls]")) {
    metricDragging = event.target.closest?.("[data-metric-widget]");
    if (metricDragging) {
      metricDragging.classList.add("opacity-40");
      event.dataTransfer.effectAllowed = "move";
      event.dataTransfer.setData("text/plain", metricDragging.dataset.metricWidget);
      return;
    }
  }
  if (!dashboardEditing || event.target.closest?.("[data-widget-edit-controls]")) return;
  dashboardDragging = event.target.closest?.("[data-dashboard-widget]");
  if (!dashboardDragging) return;
  dashboardDragging.classList.add("opacity-40");
  event.dataTransfer.effectAllowed = "move";
  event.dataTransfer.setData("text/plain", dashboardDragging.dataset.dashboardWidget);
});

document.addEventListener("dragover", (event) => {
  const dragging = metricDragging || dashboardDragging;
  if (!dragging) return;
  const over = event.target.closest?.(metricDragging ? "[data-metric-widget]" : "[data-dashboard-widget]");
  event.preventDefault();
  event.dataTransfer.dropEffect = "move";
  if (!over || over === dragging || over.hidden) return;
  if (dragMovedAt && Math.hypot(event.clientX - dragMovedAt.x, event.clientY - dragMovedAt.y) < DRAG_SLOP) return;
  const box = over.getBoundingClientRect();
  const after = event.clientY > box.top + box.height / 2 || (Math.abs(event.clientY - (box.top + box.height / 2)) < box.height / 3 && event.clientX > box.left + box.width / 2);
  const anchor = after ? over.nextSibling : over;
  if (anchor === dragging || anchor === dragging.nextSibling) return; // already there
  over.parentNode.insertBefore(dragging, anchor);
  dragMovedAt = { x: event.clientX, y: event.clientY };
});

document.addEventListener("drop", (event) => { if (dashboardDragging || metricDragging) event.preventDefault(); });
document.addEventListener("dragend", () => {
  dragMovedAt = null;
  if (metricDragging) {
    metricDragging.classList.remove("opacity-40");
    metricDragging = null;
    saveMetricOrder();
    return;
  }
  if (!dashboardDragging) return;
  dashboardDragging.classList.remove("opacity-40");
  dashboardDragging = null;
  saveDashboardOrder();
});

document.addEventListener("click", (event) => {
  // The sidebar is a CSS-only drawer below lg; navigating has to close it,
  // because on those widths nothing else will.
  if (event.target.closest("[data-nav-link]")) { const drawer = qs("#nav-drawer"); if (drawer) drawer.checked = false; }
  const editDashboard = event.target.closest("[data-dashboard-edit]");
  if (editDashboard) { setDashboardEditing(!dashboardEditing); return; }
  const editMetrics = event.target.closest("[data-metric-dashboard-edit]");
  if (editMetrics) { setMetricEditing(!metricEditing); return; }
  const pinMetric = event.target.closest("[data-metric-widget-pin]");
  if (pinMetric) { setMetricPinned(pinMetric.dataset.metricWidgetPin, !metricLayout?.pinned[pinMetric.dataset.metricWidgetPin]); return; }
  const removeMetric = event.target.closest("[data-metric-widget-remove]");
  if (removeMetric) { setMetricPinned(removeMetric.closest("[data-metric-widget]").dataset.metricWidget, false); return; }
  const resizeMetric = event.target.closest("[data-metric-widget-resize]");
  if (resizeMetric) { resizeMetricWidget(resizeMetric.closest("[data-metric-widget]")); return; }
  const pin = event.target.closest("[data-widget-pin]");
  if (pin) {
    const key = pin.dataset.widgetPin;
    setDashboardPinned(key, !dashboardLayout?.pinned[key]);
    refreshPage({ facets: true });
    return;
  }
  const remove = event.target.closest("[data-widget-remove]");
  if (remove) { setDashboardPinned(remove.closest("[data-dashboard-widget]").dataset.dashboardWidget, false); return; }
  const resize = event.target.closest("[data-widget-resize]");
  if (resize) { resizeDashboardWidget(resize.closest("[data-dashboard-widget]")); return; }
  const toggle = event.target.closest("[data-live-toggle]");
  if (toggle) { live = !live; localStorage.setItem("guard.live", live ? "on" : "off"); updateLiveControl(); if (live) refreshPage(); return; }
  if (event.target.closest("[data-linked-clear]")) {
    linkedPath = "";
    // The URL is what put it there, so the URL is what has to stop saying it:
    // dropping the chip and leaving the address alone would bring the filter
    // back on the next reload, and the Back button would still owe somebody
    // the filtered view they walked in on — which replaceState leaves intact.
    const here = new URL(location.href);
    here.searchParams.delete("rum_path");
    history.replaceState(history.state, "", here.pathname + here.search);
    for (const signal of signalPages.keys()) signalPages.set(signal, 0);
    const signal = event.target.closest("[data-filter-signal]")?.dataset.filterSignal;
    if (signal) syncSignalURL(signal);
    renderLinkedFilter();
    refreshPage();
    return;
  }
  if (event.target.closest("[data-detail-back]")) { renderDrill(); return; }
  const detailClose = event.target.closest("[data-detail-close]");
  if (detailClose) { closeDetail(detailClose.closest("[data-detail-shell]")); return; }
  if (event.target.closest("[data-trace-inline-close]")) { collapseTrace(); return; }
  const pageButton = event.target.closest("[data-page-action]");
  if (pageButton && !pageButton.disabled) {
    const signal = pageButton.closest("[data-pagination]").dataset.pagination;
    const direction = pageButton.dataset.pageAction === "next" ? 1 : -1;
    signalPages.set(signal, Math.max(0, (signalPages.get(signal) || 0) + direction));
    syncSignalURL(signal);
    refreshSignal(signal).catch(() => {});
    return;
  }
  const row = event.target.closest("[data-event-id]"); if (row) { openEventRow(row).catch(() => {}); return; }
  if (event.target.closest("[data-purge-now]")) purgeNow();
});

document.addEventListener("keydown", (event) => {
  if (event.key === "Escape") {
    const traceShell = qs('[data-detail-shell][data-detail-scope="trace"].open');
    if (traceShell) closeDetail(traceShell);
    else if (globalDetailShell()?.classList.contains("open")) closeDetail();
    else if (expandedLog) collapseLog();
    else if (expandedTrace) collapseTrace();
  }
  if (event.key === "Escape" && dashboardEditing) { setDashboardEditing(false); return; }
  if (event.key === "Escape" && metricEditing) { setMetricEditing(false); return; }
  const metricWidget = metricEditing ? event.target.closest?.("[data-metric-widget]") : null;
  if (metricWidget && !event.target.closest?.("[data-widget-edit-controls]") && ["ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown"].includes(event.key)) {
    event.preventDefault();
    const visible = metricFrames().filter((frame) => !frame.hidden);
    const at = visible.indexOf(metricWidget);
    const step = event.key === "ArrowLeft" || event.key === "ArrowUp" ? -1 : 1;
    const sibling = visible[at + step];
    if (sibling) {
      metricWidget.parentNode.insertBefore(step > 0 ? sibling : metricWidget, step > 0 ? metricWidget : sibling);
      metricWidget.focus();
      saveMetricOrder();
    }
    return;
  }
  const metricPlot = event.target.closest?.("[data-metric-plot]");
  if (metricPlot && ["ArrowLeft", "ArrowRight", "Home", "End"].includes(event.key)) {
    event.preventDefault();
    const last = metricPlot._metricPoints.length - 1;
    const current = metricPlot._metricIndex ?? last;
    const next = event.key === "Home" ? 0 : event.key === "End" ? last : current + (event.key === "ArrowLeft" ? -1 : 1);
    showMetricTooltip(metricPlot, next);
    return;
  }
  const widget = dashboardEditing ? event.target.closest?.("[data-dashboard-widget]") : null;
  if (widget && !event.target.closest?.("[data-widget-edit-controls]") && ["ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown"].includes(event.key)) {
    event.preventDefault();
    const visible = dashboardFrames().filter((frame) => !frame.hidden);
    const at = visible.indexOf(widget);
    const step = event.key === "ArrowLeft" || event.key === "ArrowUp" ? -1 : 1;
    const sibling = visible[at + step];
    if (sibling) {
      widget.parentNode.insertBefore(step > 0 ? sibling : widget, step > 0 ? widget : sibling);
      widget.focus();
      saveDashboardOrder();
    }
    return;
  }
  if ((event.key === "Enter" || event.key === " ") && event.target.matches("[data-event-id]")) { event.preventDefault(); openEventRow(event.target).catch(() => {}); }
});

document.addEventListener("pointermove", (event) => {
  const plot = event.target.closest?.("[data-metric-plot]");
  if (!plot || !plot._metricPoints?.length) return;
  const box = plot.getBoundingClientRect();
  const ratio = Math.max(0, Math.min(1, (event.clientX - box.left) / Math.max(box.width, 1)));
  showMetricTooltip(plot, Math.round(ratio * (plot._metricPoints.length - 1)));
});

document.addEventListener("pointerout", (event) => {
  const plot = event.target.closest?.("[data-metric-plot]");
  if (plot && !plot.contains(event.relatedTarget) && document.activeElement !== plot) hideMetricTooltip(plot);
});

document.addEventListener("focusin", (event) => {
  const plot = event.target.closest?.("[data-metric-plot]");
  if (plot) showMetricTooltip(plot, plot._metricIndex ?? plot._metricPoints.length - 1);
});

document.addEventListener("focusout", (event) => {
  const plot = event.target.closest?.("[data-metric-plot]");
  if (plot) hideMetricTooltip(plot);
});

document.addEventListener("input", (event) => {
  if (!event.target.matches("input[data-filter]")) return;
  const signal = event.target.closest("[data-filter-signal]")?.dataset.filterSignal;
  if (signal) {
    signalPages.set(signal, 0);
    syncSignalURL(signal);
  }
  clearTimeout(filterTimer); filterTimer = setTimeout(() => refreshPage(), 180);
});

document.addEventListener("change", (event) => {
  if (event.target.matches("[data-widget-log-service]")) {
    if (!dashboardLayout) loadDashboardLayout();
    dashboardLayout.service = event.target.value;
    saveDashboardLayout();
    refreshDashboardLogs().catch(() => {});
    return;
  }
  // Text and datetime inputs already update on `input`; handling their later
  // `change` event would send the same query again when the control blurs.
  if (event.target.matches("input[data-filter]")) return;
  if (event.target.matches('[data-filter="range"]')) qs("[data-custom-range]", event.target.closest("[data-filter-signal]"))?.classList.toggle("hidden", event.target.value !== "custom");
  if (event.target.matches("[data-filter]")) {
    const signal = event.target.closest("[data-filter-signal]")?.dataset.filterSignal;
    if (signal) {
      signalPages.set(signal, 0);
      syncSignalURL(signal);
    }
    clearTimeout(filterTimer);
    refreshPage();
  }
});

document.addEventListener("submit", (event) => {
  if (!event.target.matches("[data-settings-form]")) return;
  event.preventDefault(); saveSettings(event.target);
});

updateLiveControl();
initializedPage = location.pathname === "/" ? "home" : location.pathname.split("/").filter(Boolean)[0];
if (initializedPage === "home") applyDashboardLayout();
// A cold load of a drill link — a new tab, a reload, an address somebody was
// sent — starts here rather than at the mount, so the eager pass below asks for
// the sessions the URL names instead of the whole table and then narrowing.
readLinkedFilter();
readSignalURLState(initializedPage);
syncSignalURL(initializedPage);
initialRefresh = refreshPage({ facets: true });
liveTimer = setTimeout(liveTick, 3000);
