// ==UserScript==
// @name         Claude.ai — Sort Sidebar + Superchat
// @namespace    local.ordinal
// @version      43.9
// @description  Split rail gap: years need 22px, months only 12px — denser month labels, still-readable years.
// @match        https://claude.ai/*
// @run-at       document-start
// @grant        none
// ==/UserScript==

(function () {
  'use strict';

  // ============================================================
  //  CONFIG
  // ============================================================
  const OLDEST_FIRST = false;
  // Default sort mode. Can be overridden by sidebar toggle button; persists
  // to localStorage. Values: 'created' (sort by chat creation date, default)
  // or 'activity' (sort by last message — Claude's native ordering).
  const DEFAULT_SORT_MODE = 'created';
  const SORT_MODE_STORAGE_KEY = 'sbc-sort-mode';
  let sortMode = DEFAULT_SORT_MODE;
  try {
    const stored = localStorage.getItem(SORT_MODE_STORAGE_KEY);
    if (stored === 'created' || stored === 'activity') sortMode = stored;
  } catch {}
  const setSortMode = (mode) => {
    if (mode !== 'created' && mode !== 'activity') return;
    sortMode = mode;
    try { localStorage.setItem(SORT_MODE_STORAGE_KEY, mode); } catch {}
  };
  // Legacy constant retained for backward-compat reads. True when sortMode === 'created'.
  // transformItems / sortByCreated still reference this; toggle mutates at runtime.
  let REWRITE_UPDATED_AT = sortMode === 'created';

  // Superchat theme: 'contrast' keeps the original dark look regardless of
  // site theme; 'themed' follows claude.ai's dark/light mode. Persists.
  const THEME_STORAGE_KEY = 'sbc-theme-mode';
  let themeMode = 'contrast';
  try {
    const stored = localStorage.getItem(THEME_STORAGE_KEY);
    if (stored === 'contrast' || stored === 'themed') themeMode = stored;
  } catch {}
  const setThemeMode = (mode) => {
    if (mode !== 'contrast' && mode !== 'themed') return;
    themeMode = mode;
    try { localStorage.setItem(THEME_STORAGE_KEY, mode); } catch {}
  };

  // Detect claude.ai's current theme. Checks the class list + data-theme on
  // <html> and <body>, falls back to prefers-color-scheme. Returns 'light'
  // or 'dark'. Default is 'dark' if nothing signals otherwise.
  const detectSiteTheme = () => {
    const html = document.documentElement;
    const body = document.body;
    // Class-based: many apps toggle a 'dark' or 'light' class on <html>
    if (html?.classList.contains('light') || body?.classList.contains('light')) return 'light';
    if (html?.classList.contains('dark') || body?.classList.contains('dark')) return 'dark';
    // data-theme attribute
    const dt = html?.dataset?.theme || body?.dataset?.theme;
    if (dt === 'light' || dt === 'dark') return dt;
    // color-scheme CSS prop
    const cs = getComputedStyle(html).colorScheme;
    if (cs && cs.includes('light') && !cs.includes('dark')) return 'light';
    if (cs && cs.includes('dark') && !cs.includes('light')) return 'dark';
    // System preference as last resort
    if (window.matchMedia?.('(prefers-color-scheme: light)').matches) return 'light';
    return 'dark';
  };
  // In-name modes (disabled by default — they pollute the rename dialog).
  const SHOW_DATE_IN_NAME = false;
  const SHOW_SIZE_IN_NAME = false;
  // Badge mode: render date as a pseudo-element prefix on the chat-name span.
  const SHOW_DATE_BADGE = true;
  const SHOW_SIDEBAR_SIZE_BAR = true;
  const DATE_SEPARATOR = ' · ';
  const PROBE_LIMITS = [1000, 500, 250, 100, 50];

  const ENABLE_SUPERCHAT = true;
  const SUPERCHAT_HOTKEY = (e) => e.ctrlKey && e.shiftKey && e.key.toLowerCase() === 't';
  const FETCH_CONCURRENCY = 4;

  // Silent background prefetch: populates the size cache after page load
  // so sidebar bars appear without the user opening Superchat.
  const BACKGROUND_PREFETCH = true;
  const BG_CONCURRENCY = 8;           // was 6 — no 429s seen at 6, try higher
  const BG_START_DELAY_MS = 2000;
  const BG_BETWEEN_FETCH_MS = 0;

  const DB_NAME = 'sbc-superchat';
  const DB_VERSION = 6;
  // v34: chat_meta + chat_rows. v37: + height_cache (persistent row heights
  // so scrolling through a row once prevents gap-flicker forever after).
  // v41: + star_cache (per-message bookmarks, keyed by messageUuid).
  const DB_META_STORE = 'chat_meta';
  const DB_ROWS_STORE = 'chat_rows';
  const DB_HEIGHTS_STORE = 'height_cache';
  const DB_STARS_STORE = 'star_cache';
  const DB_STORE = DB_META_STORE;  // legacy alias
  // v29 replaced the periodic full-rebuild render. This constant is retained
  // only because the legacy fetch loop still references it; with virtualization,
  // renders are now incremental and near-free regardless of frequency.
  const RENDER_EVERY_N = 5;

  const UUID_RE = /([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})/i;

  const DATE_FORMAT = (iso) => {
    const d = new Date(iso);
    if (isNaN(d)) return '';
    const months = ['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'];
    const mm = months[d.getMonth()], dd = d.getDate(), yy = d.getFullYear();
    return yy === new Date().getFullYear() ? `${mm} ${dd}` : `${mm} ${dd} '${String(yy).slice(2)}`;
  };

  // ============================================================
  //  SHARED STATE
  // ============================================================
  const LOG = (...a) => console.log('[Superchat]', ...a);
  const originalFetch = window.fetch;
  let cachedLimit = null;
  let probePromise = null;
  let cachedOrgId = null;

  const sidebarMeta = new Map();
  let sidebarMetaReady = null;
  // Bumped on every sidebarMeta mutation. Lets decorateSidebar's maxSize
  // cache invalidate without comparing the entire map.
  let sidebarMetaEpoch = 0;
  const setSidebarMeta = (uuid, v) => { sidebarMeta.set(uuid, v); sidebarMetaEpoch++; };

  // Tracks chats currently being fetched. Maps uuid → Promise<metaRec>
  // so a duplicate call can await the ongoing fetch instead of polling DB.
  const inFlight = new Map();

  // Starred message IDs (the row.id / messageUuid). Loaded from DB on
  // Superchat open; mutated by the star toggle and persisted back.
  const starredIds = new Set();
  let starredLoaded = false;
  async function loadStarredIds() {
    if (starredLoaded) return;
    try {
      const all = await dbGetAll(DB_STARS_STORE);
      for (const rec of all) if (rec && rec.id) starredIds.add(rec.id);
      starredLoaded = true;
    } catch { /* DB unavailable — empty set is fine */ }
  }
  async function toggleStar(id) {
    if (starredIds.has(id)) {
      starredIds.delete(id);
      try { await dbDelete(DB_STARS_STORE, id); } catch {}
      return false;
    } else {
      starredIds.add(id);
      try { await dbPut(DB_STARS_STORE, { id, starredAt: Date.now() }); } catch {}
      return true;
    }
  }

  const getURL = (arg) => (typeof arg === 'string' ? arg : arg?.url);
  const isConversationListURL = (url) =>
    typeof url === 'string' &&
    /\/chat_conversations(_v\d+)?(\?|$)/.test(url.split('#')[0]);

  const extractOrgId = (url) => {
    const m = (url || '').match(/\/organizations\/([0-9a-f-]{8,})/);
    return m ? m[1] : null;
  };

  function scanForOrgId() {
    const stores = [];
    try { stores.push(localStorage); } catch {}
    try { stores.push(sessionStorage); } catch {}
    for (const store of stores) {
      try {
        for (let i = 0; i < store.length; i++) {
          const key = store.key(i);
          if (!key) continue;
          const value = store.getItem(key);
          if (!value) continue;
          if (!(/org/i.test(key) || /org/i.test(value.slice(0, 200)))) continue;
          const m = value.match(UUID_RE);
          if (m) return m[1];
        }
      } catch {}
    }
    try {
      for (const c of document.cookie.split(';')) {
        const eq = c.indexOf('=');
        if (eq < 0) continue;
        const key = c.slice(0, eq).trim();
        const val = decodeURIComponent(c.slice(eq + 1).trim());
        if (!/org/i.test(key)) continue;
        const m = val.match(UUID_RE);
        if (m) return m[1];
      }
    } catch {}
    return null;
  }

  const setOrgIdFrom = (source, value) => {
    if (cachedOrgId || !value) return;
    cachedOrgId = value;
    LOG(`orgId via ${source}:`, value);
  };

  const LIST_KEYS = ['data', 'conversations', 'items', 'results'];
  const extractList = (data) => {
    if (Array.isArray(data)) return { list: data, key: null };
    for (const k of LIST_KEYS) if (Array.isArray(data?.[k])) return { list: data[k], key: k };
    return { list: null, key: null };
  };

  const extractInit = (origArgs) => {
    if (typeof origArgs[0] === 'string') return origArgs[1] || { credentials: 'include' };
    const r = origArgs[0];
    return { method: r.method, headers: r.headers, credentials: r.credentials || 'include', mode: r.mode };
  };

  const withLimit = (url, limit) => {
    const u = new URL(url, location.origin);
    u.searchParams.set('limit', String(limit));
    return u.toString();
  };

  const sortByCreated = (list) =>
    [...list].sort((a, b) => {
      const da = new Date(a.created_at || 0).getTime();
      const db = new Date(b.created_at || 0).getTime();
      return OLDEST_FIRST ? da - db : db - da;
    });

  const formatSize = (bytes) => {
    if (!bytes || bytes < 1024) return `${bytes || 0}B`;
    if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(1)}KB`;
    return `${(bytes / (1024 * 1024)).toFixed(2)}MB`;
  };

  const transformItems = (items) => items.map(item => {
    let out = item;
    if (REWRITE_UPDATED_AT && out.created_at) out = { ...out, updated_at: out.created_at };

    // Stash both timestamps into sidebarMeta. createdAt drives the badge.
    // updatedAt is needed for the activity-mode sort toggle — we can't rely
    // on Claude's UI state, so we keep our own copy per-uuid.
    if (out.created_at || item.updated_at) {
      const existing = sidebarMeta.get(out.uuid) || {};
      const nextCreated = out.created_at || existing.createdAt;
      const nextUpdated = item.updated_at || existing.updatedAt;
      if (existing.createdAt !== nextCreated || existing.updatedAt !== nextUpdated) {
        setSidebarMeta(out.uuid, { ...existing, createdAt: nextCreated, updatedAt: nextUpdated });
      }
    }

    if (!SHOW_DATE_IN_NAME && !SHOW_SIZE_IN_NAME) return out;

    const prefix = SHOW_DATE_IN_NAME && out.created_at ? DATE_FORMAT(out.created_at) : '';
    const meta = sidebarMeta.get(out.uuid);
    const suffixParts = [];
    if (SHOW_SIZE_IN_NAME && meta?.sizeBytes) suffixParts.push(formatSize(meta.sizeBytes));
    const suffix = suffixParts.length ? ` ${DATE_SEPARATOR.trim()} ${suffixParts.join(' ')}` : '';

    const base = (out.name && out.name.length > 0) ? out.name : 'Untitled';
    const parts = [];
    if (prefix) parts.push(prefix);
    parts.push(base);
    const joined = parts.join(DATE_SEPARATOR) + suffix;
    return { ...out, name: joined };
  });

  setOrgIdFrom('storage-scan', scanForOrgId());

  const measureSize = (obj) => {
    try { return new Blob([JSON.stringify(obj)]).size; } catch { return 0; }
  };

  // ============================================================
  //  STYLES
  // ============================================================
  const injectStyles = () => {
    if (document.getElementById('sbc-styles')) return;
    const style = document.createElement('style');
    style.id = 'sbc-styles';
    style.textContent = `
      @keyframes sbc-pulse { 0%,100%{opacity:.3} 50%{opacity:1} }
      @keyframes sbc-fade  { from{opacity:0} to{opacity:1} }
      @keyframes sbc-slide { from{opacity:0;transform:translateY(8px)} to{opacity:1;transform:translateY(0)} }

      .sbc-toast { position:fixed; bottom:16px; right:16px; z-index:2147483646;
        padding:8px 14px; background:rgba(24,24,27,.92); color:#f4f4f5;
        font:500 12.5px/1.2 -apple-system,system-ui,sans-serif;
        border-radius:10px; border:1px solid rgba(255,255,255,.08);
        opacity:0; transition:opacity 180ms ease; pointer-events:none;
        backdrop-filter:blur(8px) }
      .sbc-toast.on { opacity:1 }
      .sbc-toast::before { content:''; display:inline-block; width:7px; height:7px;
        border-radius:50%; background:#a78bfa; margin-right:8px;
        animation:sbc-pulse 1.1s ease-in-out infinite; vertical-align:middle }
      .sbc-toast.done::before { background:#4ade80; animation:none }

      /* Size bar + date badge render as pseudo-elements.
         Size bar: ::after on the <a>. Badge: ::before on the inner name span. */
      a[href^="/chat/"][data-sbc-state] {
        position:relative !important;
      }
      /* Date badge: inline prefix inside the chat-name span,
         so it participates in the same truncation/flex sizing as the name. */
      a[href^="/chat/"] span[data-sbc-chat-meta]::before {
        content:attr(data-sbc-chat-meta) ' · ';
        opacity:.45;
        font-weight:400;
        letter-spacing:.02em;
      }
      /* Pending bar: faint purple stripe, pulsing */
      a[href^="/chat/"][data-sbc-state="pending"]::after {
        content:'';
        position:absolute;
        left:8px; right:8px; bottom:2px;
        height:2px; border-radius:1px;
        background:rgba(139,92,246,.22);
        animation:sbc-pulse 1.8s ease-in-out infinite;
        pointer-events:none;
        z-index:5;
      }
      /* Ready bar: just the filled portion — width proportional to relative size. */
      a[href^="/chat/"][data-sbc-state="ready"]::after {
        content:'';
        position:absolute;
        left:8px; bottom:2px;
        width:calc(var(--sbc-bar-fill, 0) * (100% - 16px));
        height:2px; border-radius:1px;
        background:rgba(139,92,246,.6);
        pointer-events:none;
        z-index:5;
        transition:width 200ms ease;
      }

      .sbc-sc-btn { position:fixed; bottom:60px; right:16px; z-index:2147483645;
        padding:8px 14px; background:rgba(24,24,27,.92); color:#f4f4f5;
        font:500 12.5px/1.2 -apple-system,system-ui,sans-serif;
        border-radius:10px; border:1px solid rgba(255,255,255,.08);
        box-shadow:0 4px 20px rgba(0,0,0,.3); cursor:pointer;
        backdrop-filter:blur(8px); transition:all 180ms ease;
        display:flex; align-items:center; gap:8px }
      .sbc-sc-btn:hover { background:rgba(39,39,42,.95); transform:translateY(-1px) }

      /* Sort toggle: lives inside the sidebar container, top. Styled to blend
         with Claude's own sidebar chrome — subtle, not flashy. */
      .sbc-sort-toggle {
        display:block; width:calc(100% - 16px);
        margin:8px; padding:6px 10px;
        background:rgba(255,255,255,.04);
        border:1px solid rgba(255,255,255,.08);
        border-radius:6px;
        color:#a1a1aa;
        font:500 11.5px/1.2 -apple-system,system-ui,sans-serif;
        text-align:left;
        cursor:pointer;
        transition:all 120ms ease;
      }
      .sbc-sort-toggle:hover {
        background:rgba(255,255,255,.08);
        color:#e4e4e7;
      }
      /* Progress ring: SVG <circle> with stroke-dasharray animation.
         Two circles — grey track, purple progress. Progress uses stroke-dashoffset
         driven by the --sbc-progress CSS var (0 = empty, 1 = full). */
      .sbc-sc-btn-ring { width:14px; height:14px; flex-shrink:0;
        transform:rotate(-90deg); }
      .sbc-sc-btn-ring circle { fill:none; stroke-width:2; }
      .sbc-sc-btn-ring .track { stroke:rgba(255,255,255,.12); }
      .sbc-sc-btn-ring .fill  { stroke:#a78bfa;
        stroke-dasharray:34.56;  /* 2πr = 2π×5.5 ≈ 34.56 */
        stroke-dashoffset:calc(34.56 * (1 - var(--sbc-progress, 0)));
        stroke-linecap:round;
        transition:stroke-dashoffset 300ms ease; }
      .sbc-sc-btn-ring.hidden { display:none; }
      .sbc-sc-btn-dot { width:6px; height:6px; border-radius:50%; background:#a78bfa; }
      .sbc-sc-btn-dot.hidden { display:none; }

      .sbc-sc-overlay { position:fixed; inset:0; z-index:2147483647;
        background:rgba(0,0,0,.6); backdrop-filter:blur(6px);
        display:flex; align-items:center; justify-content:center;
        animation:sbc-fade 180ms ease }
      .sbc-sc-modal { background:rgba(24,24,27,.98); color:#e4e4e7;
        border:1px solid rgba(255,255,255,.1); border-radius:12px;
        width:95vw; height:95vh; max-height:95vh; display:flex; flex-direction:column;
        position:relative;  /* date rail anchors here via absolute positioning */
        font:400 14px/1.45 -apple-system,BlinkMacSystemFont,"Segoe UI",system-ui,sans-serif;
        box-shadow:0 20px 60px rgba(0,0,0,.5); animation:sbc-slide 200ms ease }

      /* ================ LIGHT THEME OVERRIDES ================
         Applied when .sbc-light is set on the modal. Body-level background
         + text color are the big ones; everything else cascades from
         contrast-based rgba() values that are readable on both themes. */
      .sbc-sc-modal.sbc-light {
        background:rgba(250,250,250,.98); color:#18181b;
        border-color:rgba(0,0,0,.1);
        box-shadow:0 20px 60px rgba(0,0,0,.15);
      }
      .sbc-sc-modal.sbc-light .sbc-sc-header { border-bottom-color:rgba(0,0,0,.08) }
      .sbc-sc-modal.sbc-light .sbc-sc-progress,
      .sbc-sc-modal.sbc-light .sbc-sc-close { color:#52525b }
      .sbc-sc-modal.sbc-light .sbc-sc-close:hover { background:rgba(0,0,0,.06); color:#18181b }
      .sbc-sc-modal.sbc-light .sbc-sc-search {
        background:rgba(0,0,0,.04); color:#18181b;
        border-color:rgba(0,0,0,.1);
      }
      .sbc-sc-modal.sbc-light .sbc-sc-search::placeholder { color:#71717a }
      .sbc-sc-modal.sbc-light .sbc-sender-btn { color:#52525b }
      .sbc-sc-modal.sbc-light .sbc-sender-btn:hover { color:#18181b; background:rgba(0,0,0,.04) }
      .sbc-sc-modal.sbc-light .sbc-sender-btn.active { background:rgba(167,139,250,.22); color:#18181b }
      .sbc-sc-modal.sbc-light .sbc-sc-chat-filter,
      .sbc-sc-modal.sbc-light .sbc-sc-starred-only,
      .sbc-sc-modal.sbc-light .sbc-sc-theme-toggle {
        background:rgba(0,0,0,.04); color:#18181b; border-color:rgba(0,0,0,.1);
      }
      .sbc-sc-modal.sbc-light .sbc-sc-chat-filter:hover,
      .sbc-sc-modal.sbc-light .sbc-sc-starred-only:hover,
      .sbc-sc-modal.sbc-light .sbc-sc-theme-toggle:hover { background:rgba(0,0,0,.08) }
      .sbc-sc-modal.sbc-light .sbc-sc-starred-only.active {
        background:rgba(251,191,36,.25); border-color:rgba(251,191,36,.5); color:#78350f;
      }
      .sbc-sc-modal.sbc-light .sbc-sc-count { color:#52525b }
      .sbc-sc-modal.sbc-light .sbc-day {
        color:#7c3aed;
        background:rgba(250,250,250,.98);
        border-bottom-color:rgba(124,58,237,.2);
      }
      .sbc-sc-modal.sbc-light .sbc-msg { border-bottom-color:rgba(0,0,0,.06) }
      .sbc-sc-modal.sbc-light .sbc-msg:hover { background:rgba(0,0,0,.03) }
      .sbc-sc-modal.sbc-light .sbc-msg.sbc-msg-selected {
        background:rgba(167,139,250,.12);
      }
      .sbc-sc-modal.sbc-light .sbc-msg-time,
      .sbc-sc-modal.sbc-light .sbc-msg-context { color:#71717a }
      .sbc-sc-modal.sbc-light .sbc-msg-open { color:#52525b }
      .sbc-sc-modal.sbc-light .sbc-msg-open:hover { color:#18181b; background:rgba(0,0,0,.06) }
      .sbc-sc-modal.sbc-light .sbc-msg-copy { color:#52525b }
      .sbc-sc-modal.sbc-light .sbc-msg-copy:hover { color:#18181b; background:rgba(0,0,0,.06) }
      .sbc-sc-modal.sbc-light .sbc-msg-star { color:#52525b }
      .sbc-sc-modal.sbc-light .sbc-msg-star:hover { background:rgba(0,0,0,.06) }
      .sbc-sc-modal.sbc-light .sbc-msg-text { color:#18181b }
      .sbc-sc-modal.sbc-light .sbc-msg.sbc-msg-skel .sbc-msg-text { color:#a1a1aa }
      .sbc-sc-modal.sbc-light .sbc-sc-empty { color:#71717a }
      .sbc-sc-modal.sbc-light .sbc-sc-body::-webkit-scrollbar-track { background:rgba(0,0,0,.04) }
      .sbc-sc-modal.sbc-light .sbc-sc-body::-webkit-scrollbar-thumb { background:rgba(0,0,0,.3) }
      .sbc-sc-modal.sbc-light .sbc-sc-body::-webkit-scrollbar-thumb:hover { background:rgba(0,0,0,.5) }
      .sbc-sc-modal.sbc-light .sbc-sc-body::-webkit-scrollbar-thumb:active { background:rgba(0,0,0,.65) }
      .sbc-sc-modal.sbc-light .sbc-sc-body { scrollbar-color:rgba(0,0,0,.3) rgba(0,0,0,.04) }
      .sbc-sc-modal.sbc-light .sbc-scroll-pill {
        background:rgba(250,250,250,.95); border-color:rgba(0,0,0,.12); color:#18181b;
      }
      .sbc-sc-modal.sbc-light .sbc-date-rail .sbc-rail-tick { color:rgba(24,24,27,.5) }
      .sbc-sc-modal.sbc-light .sbc-date-rail .sbc-rail-tick.year { color:rgba(124,58,237,.9) }
      .sbc-sc-modal.sbc-light .sbc-date-rail .sbc-rail-tick:hover { color:#18181b }
      .sbc-sc-modal.sbc-light .sbc-date-rail .sbc-rail-tick.year:hover { color:#6d28d9 }
      .sbc-sc-modal.sbc-light .sbc-chat-panel-head,
      .sbc-sc-modal.sbc-light .sbc-sc-chat-panel {
        background:rgba(245,245,245,.98); border-color:rgba(0,0,0,.1);
      }
      .sbc-sc-modal.sbc-light .sbc-chat-row:hover { background:rgba(0,0,0,.04) }
      .sbc-sc-header { display:flex; align-items:center; justify-content:space-between;
        padding:14px 20px; border-bottom:1px solid rgba(255,255,255,.06); gap:12px }
      .sbc-sc-title { font:600 15px/1.2 inherit; margin:0 }
      .sbc-sc-progress { font:400 12px/1.2 inherit; color:#a1a1aa; flex:1; text-align:right }
      .sbc-sc-close { background:none; border:none; color:#a1a1aa; cursor:pointer;
        font-size:22px; line-height:1; padding:2px 8px; border-radius:6px;
        transition:all 120ms ease }
      .sbc-sc-close:hover { background:rgba(255,255,255,.06); color:#fff }

      /* Toolbar: search + sender toggle + chat filter. Sits below the header. */
      .sbc-sc-toolbar {
        display:flex; align-items:center; gap:10px;
        padding:10px 20px;
        border-bottom:1px solid rgba(255,255,255,.06);
        background:rgba(255,255,255,.02);
      }
      .sbc-sc-search {
        flex:1; min-width:0;
        background:rgba(255,255,255,.05);
        border:1px solid rgba(255,255,255,.08);
        border-radius:6px;
        color:#e4e4e7;
        padding:6px 10px;
        font:400 13px/1.4 inherit;
        outline:none;
        transition:border-color 120ms ease, background 120ms ease;
      }
      .sbc-sc-search:focus {
        border-color:rgba(167,139,250,.5);
        background:rgba(255,255,255,.08);
      }
      .sbc-sc-search::placeholder { color:#71717a }

      .sbc-sc-sender-toggle {
        display:flex; gap:0;
        background:rgba(255,255,255,.04);
        border:1px solid rgba(255,255,255,.06);
        border-radius:6px;
        overflow:hidden;
        flex-shrink:0;
      }
      .sbc-sender-btn {
        background:transparent; border:none; color:#a1a1aa;
        padding:5px 12px; cursor:pointer;
        font:500 12px/1.2 inherit;
        transition:all 120ms ease;
      }
      .sbc-sender-btn:hover { color:#e4e4e7; background:rgba(255,255,255,.04) }
      .sbc-sender-btn.active {
        background:rgba(167,139,250,.18);
        color:#e4e4e7;
      }

      .sbc-sc-chat-filter {
        background:rgba(255,255,255,.05);
        border:1px solid rgba(255,255,255,.08);
        border-radius:6px;
        color:#e4e4e7;
        padding:5px 12px;
        font:500 12px/1.2 inherit;
        cursor:pointer;
        flex-shrink:0;
        transition:all 120ms ease;
      }
      .sbc-sc-chat-filter:hover { background:rgba(255,255,255,.08) }

      /* Starred-only toggle: amber-tinted variant of chat-filter button. */
      .sbc-sc-starred-only {
        background:rgba(255,255,255,.05);
        border:1px solid rgba(255,255,255,.08);
        border-radius:6px;
        color:#e4e4e7;
        padding:5px 12px;
        font:500 12px/1.2 inherit;
        cursor:pointer;
        flex-shrink:0;
        transition:all 120ms ease;
      }
      .sbc-sc-starred-only:hover { background:rgba(255,255,255,.08) }
      .sbc-sc-starred-only.active {
        background:rgba(251,191,36,.18);
        border-color:rgba(251,191,36,.4);
        color:#fde68a;
      }

      .sbc-sc-count {
        color:#a1a1aa;
        font:400 12px/1.2 inherit;
        margin-left:auto;
        flex-shrink:0;
      }

      /* Chat filter panel: drops down below toolbar */
      .sbc-sc-chat-panel {
        border-bottom:1px solid rgba(255,255,255,.06);
        background:rgba(24,24,27,.98);
        max-height:40vh;
        display:flex; flex-direction:column;
      }
      .sbc-sc-chat-panel[hidden] { display:none }
      .sbc-chat-panel-head {
        display:flex; align-items:center; gap:10px;
        padding:8px 20px;
        border-bottom:1px solid rgba(255,255,255,.04);
        flex-shrink:0;
      }
      .sbc-chat-panel-head button {
        background:rgba(255,255,255,.05);
        border:1px solid rgba(255,255,255,.08);
        border-radius:4px;
        color:#e4e4e7;
        padding:3px 8px;
        font:500 11px/1.2 inherit;
        cursor:pointer;
      }
      .sbc-chat-panel-head button:hover { background:rgba(255,255,255,.1) }
      .sbc-chat-count {
        color:#71717a;
        font:400 11px/1.2 inherit;
        margin-left:auto;
      }
      .sbc-chat-list {
        overflow-y:auto;
        padding:6px 20px 10px;
        flex:1;
      }
      .sbc-chat-row {
        display:flex; align-items:center; gap:8px;
        padding:4px 0;
        color:#e4e4e7;
        font:400 12.5px/1.4 inherit;
        cursor:pointer;
      }
      .sbc-chat-row:hover { color:#fff }
      .sbc-chat-row input { cursor:pointer; flex-shrink:0 }
      .sbc-chat-row span {
        overflow:hidden; text-overflow:ellipsis; white-space:nowrap;
        min-width:0; flex:1;
      }

      /* Search match highlight inside message text */
      mark.sbc-hl {
        background:rgba(251,191,36,.3);
        color:inherit;
        border-radius:2px;
        padding:0 1px;
      }

      .sbc-sc-body { overflow-y:auto; padding:0 0 24px; flex:1; position:relative; contain:strict }
      .sbc-sc-body::-webkit-scrollbar { width:16px }
      .sbc-sc-body::-webkit-scrollbar-track { background:rgba(255,255,255,.04); border-radius:8px }
      .sbc-sc-body::-webkit-scrollbar-thumb {
        background:rgba(255,255,255,.35); border-radius:8px;
        min-height:40px;  /* ensures thumb stays grabbable with lots of content */
      }
      .sbc-sc-body::-webkit-scrollbar-thumb:hover { background:rgba(255,255,255,.55) }
      .sbc-sc-body::-webkit-scrollbar-thumb:active { background:rgba(255,255,255,.7) }
      /* Firefox fallback (doesn't respect ::-webkit-*) */
      .sbc-sc-body { scrollbar-width:auto; scrollbar-color:rgba(255,255,255,.35) rgba(255,255,255,.04) }

      /* Virtualizer: spacer sizes the scroll area to total-height, rows are
         absolutely positioned inside. Only rows in/near viewport are in the DOM. */
      .sbc-vt-spacer { position:relative; width:100%; will-change:height }
      .sbc-vt-row { position:absolute; left:0; right:0; top:0 }
      /* Sticky day header: pinned at the top of the scroll container via
         position:sticky relative to .sbc-sc-body. The .sbc-day styles below
         provide the visual treatment. */
      .sbc-vt-sticky {
        position:sticky; top:0; z-index:3;
        pointer-events:none;
      }

      /* Scroll pill: floating month/year label, shown during scroll, fades out on idle.
         Positioned right edge, vertically centered in the viewport of the body. */
      .sbc-scroll-pill {
        position:sticky; top:50%; z-index:4;
        margin-left:auto; margin-right:14px;
        width:fit-content;
        padding:5px 11px;
        background:rgba(24,24,27,.94);
        border:1px solid rgba(255,255,255,.1);
        border-radius:999px;
        color:#e4e4e7;
        font:500 11.5px/1 inherit;
        letter-spacing:.02em;
        pointer-events:none;
        opacity:0;
        transition:opacity 140ms ease;
      }
      .sbc-scroll-pill.visible { opacity:1; }

      /* Date rail: vertical strip of clickable year/month ticks, overlays
         the right edge of the body area. Positioned absolutely inside the
         modal (NOT inside bodyEl — bodyEl uses contain:strict for the
         virtualizer). Pointer-events pass through the empty areas so scroll
         still works, ticks re-enable for themselves. */
      .sbc-date-rail {
        position:absolute; right:8px; top:120px; bottom:24px;
        width:36px;
        pointer-events:none;
        z-index:2;
      }
      .sbc-date-rail .sbc-rail-tick {
        position:absolute; right:0;
        transform:translateY(-50%);
        background:transparent; border:none;
        color:rgba(228,228,231,.45);
        font:500 9.5px/1 inherit;
        letter-spacing:.02em;
        padding:2px 4px; margin:0;
        cursor:pointer;
        pointer-events:auto;
        white-space:nowrap;
        transition:color 120ms ease;
      }
      .sbc-date-rail .sbc-rail-tick.year {
        color:rgba(167,139,250,.85);
        font-weight:600; font-size:10.5px;
      }
      .sbc-date-rail .sbc-rail-tick:hover {
        color:#e4e4e7;
      }
      .sbc-date-rail .sbc-rail-tick.year:hover {
        color:#c4b5fd;
      }

      .sbc-day { margin:0 20px; padding:10px 0 6px; font:600 12px/1.2 inherit;
        color:#a78bfa; text-transform:uppercase; letter-spacing:.05em;
        border-bottom:1px solid rgba(167,139,250,.15);
        background:rgba(24,24,27,.98); }
      .sbc-msg { display:block; padding:14px 20px; margin:0;
        border-bottom:1px solid rgba(255,255,255,.04);
        color:inherit;
        transition:background 120ms ease;
        cursor:text;  /* text cursor — rows are selectable, not clickable */
      }
      .sbc-msg:hover { background:rgba(255,255,255,.03) }
      /* Keyboard-selected row: subtle purple left-border + slight tint */
      .sbc-msg.sbc-msg-selected {
        background:rgba(167,139,250,.08);
        box-shadow:inset 3px 0 0 0 #a78bfa;
      }
      .sbc-msg-header { display:flex; gap:10px; align-items:center;
        font:500 11.5px/1.2 ui-monospace,monospace; margin-bottom:8px; flex-wrap:wrap }
      .sbc-msg-time { color:#71717a; flex-shrink:0; width:44px }
      .sbc-msg-sender { flex-shrink:0; padding:2px 7px; border-radius:4px;
        font-size:10px; text-transform:uppercase; letter-spacing:.06em; font-weight:600 }
      .sbc-msg-sender.user   { background:rgba(167,139,250,.15); color:#c4b5fd }
      .sbc-msg-sender.claude { background:rgba(74,222,128,.12); color:#86efac }
      .sbc-msg-sender.system { background:rgba(251,191,36,.12); color:#fbbf24 }
      .sbc-msg-context { color:#71717a; flex:1; font-weight:400;
        overflow:hidden; text-overflow:ellipsis; white-space:nowrap; min-width:0 }
      /* Explicit open button — the only thing that navigates.
         Always visible (low opacity) so users can find it, brighter on hover. */
      .sbc-msg-open {
        flex-shrink:0; color:#a1a1aa; text-decoration:none;
        padding:3px 8px; border-radius:4px;
        font:500 13px/1 ui-monospace,monospace;
        cursor:pointer;
        opacity:0.55;
        transition:opacity 120ms ease, background 120ms ease, color 120ms ease;
      }
      .sbc-msg:hover .sbc-msg-open { opacity:0.85; }
      .sbc-msg-open:hover { opacity:1; color:#e4e4e7; background:rgba(255,255,255,.1); }

      /* Star button: ☆ default, ★ when filled. Visible at rest, brighter on hover. */
      .sbc-msg-star {
        flex-shrink:0; background:none; border:none;
        color:#a1a1aa;
        padding:2px 6px; border-radius:4px;
        font:400 18px/1 inherit; cursor:pointer;
        opacity:0.75;
        transition:opacity 120ms ease, color 120ms ease, background 120ms ease, transform 120ms ease;
      }
      .sbc-msg:hover .sbc-msg-star { opacity:1; }
      .sbc-msg-star:hover { opacity:1; color:#fbbf24; background:rgba(255,255,255,.08); transform:scale(1.15); }
      .sbc-msg-star.filled {
        color:#fbbf24;
        opacity:1;
      }
      .sbc-msg-star.filled:hover { color:#fde68a; background:rgba(251,191,36,.15); }

      /* Copy button: ⧉ glyph. Neutral grey, brightens on hover. Brief
         "copied" state shows a check glyph. */
      .sbc-msg-copy {
        flex-shrink:0; background:none; border:none;
        color:#a1a1aa;
        padding:2px 6px; border-radius:4px;
        font:400 16px/1 inherit; cursor:pointer;
        opacity:0.75;
        transition:opacity 120ms ease, color 120ms ease, background 120ms ease, transform 120ms ease;
      }
      .sbc-msg:hover .sbc-msg-copy { opacity:1; }
      .sbc-msg-copy:hover { opacity:1; color:#e4e4e7; background:rgba(255,255,255,.08); transform:scale(1.15); }
      .sbc-msg-copy.copied { color:#86efac; }

      /* Starred row: subtle amber tint on the left edge, mirroring the selected
         row's purple edge. If both are active, selected overrides (purple wins). */
      .sbc-msg.sbc-msg-starred {
        box-shadow:inset 3px 0 0 0 rgba(251,191,36,.45);
      }
      .sbc-msg.sbc-msg-starred.sbc-msg-selected {
        box-shadow:inset 3px 0 0 0 #a78bfa;
      }
      .sbc-msg-text { color:#e4e4e7; font-size:13.5px; line-height:1.55;
        white-space:pre-wrap; word-break:break-word; overflow-wrap:break-word;
        padding-left:54px }
      /* Skeleton rows: dimmed placeholders shown during cold-start fetch. */
      .sbc-msg.sbc-msg-skel { opacity:.45; pointer-events:none; }
      .sbc-msg.sbc-msg-skel .sbc-msg-text {
        color:#71717a; font-style:italic;
        animation:sbc-pulse 1.8s ease-in-out infinite;
      }

      .sbc-bar { height:3px; background:rgba(255,255,255,.06); border-radius:2px;
        overflow:hidden; margin:0 20px }
      .sbc-bar-fill { height:100%; background:linear-gradient(90deg,#a78bfa,#c4b5fd);
        transition:width 180ms ease }
      .sbc-bar.hidden { visibility:hidden }

      .sbc-sc-empty { padding:40px; text-align:center; color:#71717a }
    `;
    (document.head || document.documentElement).appendChild(style);
  };

  // ============================================================
  //  TOAST
  // ============================================================
  const toast = (() => {
    let el = null, timer = null;
    const ensure = () => {
      if (el) return el;
      if (!document.body) return null;
      injectStyles();
      el = document.createElement('div');
      el.className = 'sbc-toast';
      document.body.appendChild(el);
      return el;
    };
    return {
      show(text, done = false) {
        const e = ensure(); if (!e) { setTimeout(() => this.show(text, done), 50); return; }
        clearTimeout(timer);
        e.textContent = text;
        e.classList.toggle('done', done);
        e.classList.add('on');
        if (done) timer = setTimeout(() => e.classList.remove('on'), 1500);
      },
    };
  })();

  // ============================================================
  //  PROBE
  // ============================================================
  async function probeLimit(sampleURL, init) {
    toast.show('Finding limit cap…');
    for (const limit of PROBE_LIMITS) {
      try {
        const resp = await originalFetch(withLimit(sampleURL, limit), init);
        if (!resp.ok) continue;
        const data = await resp.json();
        const { list } = extractList(data);
        const count = list?.length ?? 0;
        LOG(`  limit=${limit}: ${count} items`);
        if (count > 0) { LOG(`✓ cap at or above limit=${limit}`); return limit; }
      } catch {}
    }
    return null;
  }

  async function ensureLimit(sampleURL, init) {
    if (cachedLimit !== null) return cachedLimit;
    if (probePromise) return probePromise;
    probePromise = probeLimit(sampleURL, init).then(l => { cachedLimit = l; return l; });
    return probePromise;
  }

  // ============================================================
  //  INDEXEDDB
  // ============================================================
  // Cache the DB connection across calls. All our db* helpers used to call
  // `indexedDB.open` per operation, creating many short-lived Promise chains.
  // Browsers do share the underlying handle but the request roundtrip still
  // costs. One cached promise + transparent reconnect on close.
  let _dbPromise = null;
  function openDB() {
    if (_dbPromise) return _dbPromise;
    _dbPromise = new Promise((resolve, reject) => {
      const req = indexedDB.open(DB_NAME, DB_VERSION);
      req.onupgradeneeded = (e) => {
        const db = req.result;
        // v5: additive migration — don't wipe. Only create stores that don't
        // exist yet. For upgrades from <v4, chat_meta and chat_rows need to be
        // created; those had a wipe on older versions so existing v4 users
        // already have them. We add height_cache here.
        if (!db.objectStoreNames.contains(DB_META_STORE)) {
          db.createObjectStore(DB_META_STORE, { keyPath: 'uuid' });
        }
        if (!db.objectStoreNames.contains(DB_ROWS_STORE)) {
          db.createObjectStore(DB_ROWS_STORE, { keyPath: 'uuid' });
        }
        if (!db.objectStoreNames.contains(DB_HEIGHTS_STORE)) {
          db.createObjectStore(DB_HEIGHTS_STORE, { keyPath: 'id' });
        }
        if (!db.objectStoreNames.contains(DB_STARS_STORE)) {
          db.createObjectStore(DB_STARS_STORE, { keyPath: 'id' });
        }
        LOG(`DB migrated: ${e.oldVersion} → ${e.newVersion}`);
      };
      req.onsuccess = () => {
        const db = req.result;
        // Reset the cache if the browser closes our connection (tab suspend,
        // version change from another tab). Next call re-opens.
        db.onclose = () => { _dbPromise = null; };
        db.onversionchange = () => { db.close(); _dbPromise = null; };
        resolve(db);
      };
      req.onerror = () => { _dbPromise = null; reject(req.error); };
    });
    return _dbPromise;
  }
  async function dbGet(store, uuid) {
    const db = await openDB();
    return new Promise((res, rej) => {
      const tx = db.transaction(store, 'readonly');
      const req = tx.objectStore(store).get(uuid);
      req.onsuccess = () => res(req.result || null);
      req.onerror = () => rej(req.error);
    });
  }
  async function dbPut(store, record) {
    const db = await openDB();
    return new Promise((res, rej) => {
      const tx = db.transaction(store, 'readwrite');
      tx.objectStore(store).put(record);
      tx.oncomplete = () => res();
      tx.onerror = () => rej(tx.error);
    });
  }
  // Write multiple records in one transaction (much faster than one dbPut per chat)
  async function dbPutBatch(store, records) {
    const db = await openDB();
    return new Promise((res, rej) => {
      const tx = db.transaction(store, 'readwrite');
      const s = tx.objectStore(store);
      for (const r of records) s.put(r);
      tx.oncomplete = () => res();
      tx.onerror = () => rej(tx.error);
    });
  }
  async function dbGetAll(store) {
    const db = await openDB();
    return new Promise((res, rej) => {
      const tx = db.transaction(store, 'readonly');
      const req = tx.objectStore(store).getAll();
      req.onsuccess = () => res(req.result || []);
      req.onerror = () => rej(req.error);
    });
  }
  async function dbDelete(store, key) {
    const db = await openDB();
    return new Promise((res, rej) => {
      const tx = db.transaction(store, 'readwrite');
      tx.objectStore(store).delete(key);
      tx.oncomplete = () => res();
      tx.onerror = () => rej(tx.error);
    });
  }
  // Get a batch of records by key. Faster than N sequential dbGet calls.
  async function dbGetMany(store, uuids) {
    if (uuids.length === 0) return [];
    const db = await openDB();
    return new Promise((res, rej) => {
      const tx = db.transaction(store, 'readonly');
      const s = tx.objectStore(store);
      const out = new Array(uuids.length);
      let remaining = uuids.length;
      uuids.forEach((uuid, i) => {
        const req = s.get(uuid);
        req.onsuccess = () => {
          out[i] = req.result || null;
          if (--remaining === 0) res(out);
        };
        req.onerror = () => rej(req.error);
      });
    });
  }

  // ============================================================
  //  WARM CACHE — pre-load records + flat rows before modal opens
  // ============================================================
  // Goal: openSuperchat() should feel instant, not wait 500ms-1s for IndexedDB
  // + backfill + row flatten. We do that work in the background and hand the
  // result to the modal when it opens.
  //
  // Shape: { records: Map<uuid,record>, rowsPromise: Promise<Row[]> }
  // - records: ready to mount immediately
  // - rowsPromise: flattening can take ~100ms for 20k msgs; we start it
  //   eagerly but let the modal await if it's not done yet
  //
  // Invalidation: called whenever a chat record changes (fetch completion,
  // background prefetch tick). Debounced so we don't re-read on every tick.
  //
  // v34: only loads chat_meta. Message rows stream in on demand when
  // Superchat actually opens — see streamRowsForChats() in loadAndRender.
  const warmCache = (() => {
    let current = null;       // Promise<{metaList: MetaRecord[]}>
    let rebuildTimer = null;

    const build = async () => {
      const t = performance.now();
      const metaList = await dbGetAll(DB_META_STORE);
      const dbMs = performance.now() - t;
      LOG(`warm cache built: ${metaList.length} meta records, dbGetAll=${dbMs.toFixed(0)}ms`);
      return { metaList };
    };

    const prime = () => {
      if (current) return current;
      LOG('warm cache: priming…');
      current = build().catch(err => {
        LOG('warm cache build failed:', err);
        current = null;
        return { metaList: [] };
      });
      return current;
    };

    const invalidate = () => {
      // Debounce: during a 400-chat refresh we'll be called hundreds of times.
      if (rebuildTimer) return;
      rebuildTimer = setTimeout(() => {
        rebuildTimer = null;
        current = build().catch(err => {
          LOG('warm cache rebuild failed:', err);
          current = null;
          return { metaList: [] };
        });
      }, 800);
    };

    const get = () => current || prime();

    return { prime, invalidate, get };
  })();

  async function initSidebarMeta() {
    try {
      const all = await dbGetAll(DB_META_STORE);
      for (const r of all) {
        sidebarMeta.set(r.uuid, {
          sizeBytes: r.sizeBytes || 0,
          createdAt: r.created_at || null,
          updatedAt: r.updated_at || null,
        });
      }
      // Bulk load: bump epoch once, not per-row. Cheaper than routing every
      // entry through setSidebarMeta.
      sidebarMetaEpoch++;
      LOG(`sidebar meta loaded for ${sidebarMeta.size} chats`);
      scheduleSidebarDecorate();

      // One-time migration: older DB records have updated_at === created_at
      // because we were writing the list-endpoint's updated_at (which equals
      // created_at — the server's chat-row mtime, not activity). Patch
      // updated_at from each chat's last-message timestamp, which is the real
      // activity signal. Runs async in the background; doesn't block init.
      migrateUpdatedAtFromRows().catch(err => LOG('updated_at migration failed:', err));
    } catch (err) {
      LOG('sidebar meta init failed:', err);
    }
  }

  // Background migration: walk all chats in chat_meta, for any whose
  // updated_at is missing OR equal to created_at (both indicate the entry
  // wasn't populated with a real activity timestamp), look at chat_rows to
  // find the last message's timestamp and patch both the DB record and the
  // in-memory sidebarMeta. Idempotent — running repeatedly is safe.
  async function migrateUpdatedAtFromRows() {
    const metas = await dbGetAll(DB_META_STORE);
    const needsMigration = metas.filter(m =>
      !m.updated_at || (m.created_at && m.updated_at === m.created_at)
    );
    if (needsMigration.length === 0) return;
    LOG(`migration: patching updated_at for ${needsMigration.length} chats`);
    let patched = 0, noRows = 0, noTimestamp = 0;
    for (const meta of needsMigration) {
      try {
        const rowsRec = await dbGet(DB_ROWS_STORE, meta.uuid);
        if (!rowsRec || !rowsRec.rows || rowsRec.rows.length === 0) {
          noRows++;
          continue;
        }
        const lastTs = rowsRec.rows[rowsRec.rows.length - 1].timestamp;
        if (!lastTs) { noTimestamp++; continue; }
        if (lastTs === meta.updated_at) continue;  // already correct, skip
        await dbPut(DB_META_STORE, { ...meta, updated_at: lastTs });
        const current = sidebarMeta.get(meta.uuid) || {};
        setSidebarMeta(meta.uuid, { ...current, updatedAt: lastTs });
        patched++;
      } catch {}
    }
    LOG(`migration: patched ${patched} / ${needsMigration.length} chats (noRows=${noRows}, noTimestamp=${noTimestamp})`);
  }
  async function ensureSidebarMeta() {
    if (!sidebarMetaReady) sidebarMetaReady = initSidebarMeta();
    return sidebarMetaReady;
  }
  ensureSidebarMeta();

  // Warm up the Superchat cache on idle, so the first modal open is instant.
  // Gated on sidebar meta ready so we don't contend with claude.ai startup.
  const schedulePrimeWarmCache = () => {
    const go = () => { warmCache.prime().catch(() => {}); };
    ensureSidebarMeta().then(() => {
      if (typeof requestIdleCallback === 'function') {
        requestIdleCallback(go, { timeout: 5000 });
      } else {
        setTimeout(go, 2500);
      }
    });
  };
  schedulePrimeWarmCache();

  // ============================================================
  //  SIDEBAR SIZE BAR INJECTION
  // ============================================================
  const extractChatUuid = (href) => {
    if (!href) return null;
    try {
      const u = new URL(href, location.origin);
      const m = u.pathname.match(/^\/chat\/([0-9a-f-]{8,})/);
      return m ? m[1] : null;
    } catch { return null; }
  };

  // Cached last-known set of which rows have which meta values, so we can
  // skip writes when nothing has changed for a row. Keyed by link element.
  // Stored inline as `link._sbcState = {uuid, frac, badge, state}`.

  let decorateScheduled = false;
  let decorateLastRun = 0;
  const DECORATE_MIN_INTERVAL_MS = 80;  // coalesce React bursts

  function scheduleSidebarDecorate() {
    if (!SHOW_SIDEBAR_SIZE_BAR) return;
    if (decorateScheduled) return;
    decorateScheduled = true;
    // Rate-limit: if we ran very recently, delay the next run instead of
    // firing immediately. Handles bursty React re-renders gracefully.
    const sinceLast = Date.now() - decorateLastRun;
    const delay = sinceLast < DECORATE_MIN_INTERVAL_MS ? (DECORATE_MIN_INTERVAL_MS - sinceLast) : 0;
    const fire = () => requestAnimationFrame(() => {
      decorateScheduled = false;
      decorateLastRun = Date.now();
      decorateSidebar();
    });
    if (delay > 0) setTimeout(fire, delay);
    else fire();
  }

  // Find the tightest DOM ancestor that contains ALL chat links currently
  // in the document. The sidebar usually has at least two sections (starred
  // + recent) under one <nav>; an earlier version stopped at the first
  // ancestor with 2+ links, which missed the other section. This walks up
  // until the ancestor covers every chat link on the page.
  let sidebarContainerCache = null;
  function findSidebarContainer() {
    if (sidebarContainerCache && document.contains(sidebarContainerCache)) {
      // Verify it still covers all chat links — if new sections appeared
      // outside it (e.g. starred section added later), invalidate.
      const all = document.querySelectorAll('a[href^="/chat/"]');
      const inside = sidebarContainerCache.querySelectorAll('a[href^="/chat/"]');
      if (all.length === inside.length) return sidebarContainerCache;
      sidebarContainerCache = null;  // stale — fall through to re-detect
    }
    const allLinks = document.querySelectorAll('a[href^="/chat/"]');
    if (!allLinks.length) return null;
    const totalCount = allLinks.length;
    // Walk up from the first link until the ancestor contains ALL chat
    // links on the page. Stop at <body>.
    let el = allLinks[0].parentElement;
    while (el && el !== document.body) {
      if (el.querySelectorAll('a[href^="/chat/"]').length >= totalCount) {
        sidebarContainerCache = el;
        return el;
      }
      el = el.parentElement;
    }
    sidebarContainerCache = document.body;  // fallback
    return sidebarContainerCache;
  }

  // Cached max size across currently-rendered rows. Recomputed lazily.
  let cachedMaxSize = 0;
  let cachedMaxSizeEpoch = 0;  // bumped when sidebarMeta changes

  function decorateSidebar() {
    if (!SHOW_SIDEBAR_SIZE_BAR) return;
    const container = findSidebarContainer() || document;
    const links = container.querySelectorAll('a[href^="/chat/"]');
    if (!links.length) return;

    // Compute maxSize lazily. Since sidebarMeta entries only monotonically
    // improve (sizes only get measured, never reset), we can just take the
    // max over currently-visible links and reuse it across decorate calls
    // until sidebarMeta gets mutated — which bumps cachedMaxSizeEpoch.
    if (cachedMaxSize === 0 || cachedMaxSizeEpoch !== sidebarMetaEpoch) {
      let maxSize = 1;
      for (const link of links) {
        let uuid = link.dataset.sbcUuid;
        if (!uuid) {
          uuid = extractChatUuid(link.getAttribute('href'));
          if (uuid) link.dataset.sbcUuid = uuid;
        }
        if (!uuid) continue;
        const meta = sidebarMeta.get(uuid);
        if (meta?.sizeBytes > maxSize) maxSize = meta.sizeBytes;
      }
      cachedMaxSize = maxSize;
      cachedMaxSizeEpoch = sidebarMetaEpoch;
    }

    for (const link of links) {
      // Cache parsed UUID on the element — parsing the URL per decorate pass
      // is cheap but unnecessary for stable elements.
      let uuid = link.dataset.sbcUuid;
      if (!uuid) {
        uuid = extractChatUuid(link.getAttribute('href'));
        if (uuid) link.dataset.sbcUuid = uuid;
      }
      if (!uuid) continue;
      const meta = sidebarMeta.get(uuid);

      // Compute the final values we want to apply for this row.
      const badge = (SHOW_DATE_BADGE && meta?.createdAt) ? DATE_FORMAT(meta.createdAt) : '';
      const state = (meta && meta.sizeBytes) ? 'ready' : 'pending';
      const frac = (state === 'ready')
        ? Math.max(0.02, meta.sizeBytes / cachedMaxSize).toFixed(3)
        : '';

      // Dedup: last-applied values stored on the element itself. Skip writes
      // when nothing changed. Big win on busy sidebars where most rows are
      // stable across decorate bursts.
      const last = link._sbcLast || (link._sbcLast = {});
      if (last.state !== state) {
        link.dataset.sbcState = state;
        last.state = state;
      }
      if (state === 'ready' && last.frac !== frac) {
        link.style.setProperty('--sbc-bar-fill', frac);
        last.frac = frac;
      }
      if (last.badge !== badge) {
        const nameSpan = link.querySelector('span.truncate');
        if (nameSpan) {
          if (badge) nameSpan.dataset.sbcChatMeta = badge;
          else if (nameSpan.dataset.sbcChatMeta) delete nameSpan.dataset.sbcChatMeta;
        }
        last.badge = badge;
      }
    }
  }

  function installSidebarObserver() {
    if (!SHOW_SIDEBAR_SIZE_BAR) return;

    // Two-stage observer: a document-level observer watches for the sidebar
    // container appearing (one-off during page init), then we switch to a
    // narrow observer scoped to that container.
    let narrowObserver = null;
    let wideObserver = null;

    const attachNarrow = (container) => {
      narrowObserver?.disconnect();
      narrowObserver = new MutationObserver(() => scheduleSidebarDecorate());
      // subtree: false — the sidebar container's direct children are the
      // chat rows. React rarely swaps deep descendants in a way that affects
      // our decoration; if it does, the row itself will be recreated, which
      // the childList mutation catches anyway.
      narrowObserver.observe(container, { childList: true, subtree: true });
      scheduleSidebarDecorate();
    };

    const tryAttachNarrow = () => {
      const container = findSidebarContainer();
      if (container && container !== document.body) {
        attachNarrow(container);
        wideObserver?.disconnect();  // no longer need the wide watch
        wideObserver = null;
        return true;
      }
      return false;
    };

    const start = () => {
      // Try immediately in case the sidebar already exists.
      if (tryAttachNarrow()) return;
      // Otherwise watch for its appearance. This fires many times during
      // init but exits as soon as a container is found.
      wideObserver = new MutationObserver(() => {
        if (tryAttachNarrow()) return;
        scheduleSidebarDecorate();  // still decorate what we can meanwhile
      });
      wideObserver.observe(document.body, { childList: true, subtree: true });
      scheduleSidebarDecorate();
    };

    if (document.body) start();
    else document.addEventListener('DOMContentLoaded', start, { once: true });

    // Sort toggle button: injected into the sidebar. Toggles sortMode between
    // 'created' and 'activity', then reloads the page. We tried DOM-reorder
    // (React reverted it), route-nav (remounted chat view but not sidebar),
    // and focus/visibility events (no effect — Claude doesn't use refetch-
    // on-focus). Reload is the only reliable option.
    const SORT_TOGGLE_ID = 'sbc-sort-toggle';

    const injectSortToggle = () => {
      if (document.getElementById(SORT_TOGGLE_ID)) return;
      const container = findSidebarContainer();
      if (!container || container === document.body) return;
      const btn = document.createElement('button');
      btn.id = SORT_TOGGLE_ID;
      btn.className = 'sbc-sort-toggle';
      btn.title = 'Toggle sidebar sort: chat-created date vs last-activity';
      btn.textContent = sortMode === 'created' ? '⇅ Sort: created' : '⇅ Sort: activity';
      btn.addEventListener('click', () => {
        const next = sortMode === 'created' ? 'activity' : 'created';
        setSortMode(next);
        REWRITE_UPDATED_AT = next === 'created';
        location.reload();
      });
      // Insert as first child of the container so it sits above the chat list.
      container.insertBefore(btn, container.firstChild);
    };

    // Re-attach when navigation happens, or when our cached container
    // quietly gets detached (React can swap the sidebar subtree without
    // firing a history event). The interval is cheap — one DOM-contains
    // check every 2s.
    const reAttach = () => {
      if (!sidebarContainerCache || !document.contains(sidebarContainerCache)) {
        sidebarContainerCache = null;
        tryAttachNarrow();
      }
      // Also re-inject sort toggle if React clobbered it.
      injectSortToggle();
    };
    window.addEventListener('popstate', reAttach);
    setInterval(reAttach, 2000);
    injectSortToggle();  // initial injection attempt; reAttach retries if container not ready yet
    // Monkey-patch pushState/replaceState so SPA nav triggers re-check too.
    // (Claude.ai's React router uses these.) Only patch once.
    if (!window.__sbcNavPatched) {
      window.__sbcNavPatched = true;
      const origPush = history.pushState;
      const origReplace = history.replaceState;
      history.pushState = function (...a) { const r = origPush.apply(this, a); queueMicrotask(reAttach); return r; };
      history.replaceState = function (...a) { const r = origReplace.apply(this, a); queueMicrotask(reAttach); return r; };
    }
  }
  installSidebarObserver();

  // ============================================================
  //  CHAT CONTENT FETCH
  // ============================================================
  // Shared rate-limit backoff. When any fetch hits 429, bump rateLimitUntil
  // so other concurrent workers also wait. Prevents thundering herd.
  let rateLimitUntil = 0;

  async function fetchChatContent(orgId, chatUuid, signal) {
    const url = `/api/organizations/${orgId}/chat_conversations/${chatUuid}?tree=True&rendering_mode=messages&render_all_tools=true&consistency=eventual`;
    let attempt = 0;
    while (true) {
      // Respect shared rate-limit window
      const wait = rateLimitUntil - Date.now();
      if (wait > 0) await new Promise(r => setTimeout(r, wait));
      if (signal.aborted) throw new DOMException('aborted', 'AbortError');

      const resp = await originalFetch(url, { credentials: 'include', signal });
      if (resp.ok) return resp.json();

      if (resp.status === 429 && attempt < 5) {
        // Exponential backoff: 500ms, 1s, 2s, 4s, 8s
        const backoff = 500 * Math.pow(2, attempt);
        rateLimitUntil = Math.max(rateLimitUntil, Date.now() + backoff);
        LOG(`429 rate-limited on ${chatUuid.slice(0, 8)}, backing off ${backoff}ms (attempt ${attempt + 1})`);
        attempt++;
        continue;
      }
      throw new Error(`HTTP ${resp.status}`);
    }
  }

  function needsRefetch(cachedMeta, apiMeta) {
    if (!cachedMeta) return true;
    if (!cachedMeta.updated_at || !apiMeta.updated_at) return true;
    return new Date(cachedMeta.updated_at).getTime() < new Date(apiMeta.updated_at).getTime();
  }

  // Extract all message rows from a raw chat response into the compact
  // per-row format used by the virtualizer. One pass, no sorting (global
  // sort happens later). Returns [{sender, timestamp, text}, ...].
  function extractRowsFromContent(content, chatUuid, chatName) {
    if (!content) return [];
    const messages = content.chat_messages || content.messages || content.data || [];
    const rows = [];
    for (let i = 0; i < messages.length; i++) {
      const m = messages[i];
      const sender = normalizeSender(m.sender || m.role);
      if (sender === 'unknown') continue;
      const text = extractMessageText(m);
      if (!text || !text.trim()) continue;
      const timestamp = m.created_at || m.timestamp || '';
      // _ts: pre-parsed numeric timestamp. Saves ~500k Date allocations in the
      // sort comparator for a 25k-row dataset.
      const _ts = timestamp ? new Date(timestamp).getTime() : 0;
      rows.push({
        chatUuid,
        chatName,
        sender,
        timestamp,
        _ts,
        text,
        messageUuid: m.uuid || m.id || `${chatUuid}-${i}`,
      });
    }
    return rows;
  }

  // Unified single-chat fetch. Stores meta and rows separately.
  // De-dupes via inFlight: concurrent callers for the same uuid share the
  // same promise, so no wasted fetches and no stale-DB reads.
  async function fetchOneChat(apiMeta, orgId, signal) {
    const existing = inFlight.get(apiMeta.uuid);
    if (existing) return existing;
    const p = (async () => {
      try {
        const cachedMeta = await dbGet(DB_META_STORE, apiMeta.uuid);
        if (!needsRefetch(cachedMeta, apiMeta)) return cachedMeta;

        const fresh = await fetchChatContent(orgId, apiMeta.uuid, signal);
        if (signal.aborted) return null;

        const rows = extractRowsFromContent(fresh, apiMeta.uuid, apiMeta.name);
        const sizeBytes = measureSize(fresh);

        // The list endpoint's `updated_at` often equals `created_at` — it's
        // the chat row's db mtime, not a real activity signal. The real
        // activity time is the last message's timestamp. Prefer that; fall
        // back to the list-endpoint value if no messages (shouldn't happen
        // but belt-and-braces).
        let activityAt = apiMeta.updated_at;
        if (rows.length > 0) {
          // rows are in chronological order from extractRowsFromContent —
          // last row is the most recent message.
          const lastTs = rows[rows.length - 1].timestamp;
          if (lastTs) activityAt = lastTs;
        }

        const metaRec = {
          uuid: apiMeta.uuid,
          name: apiMeta.name,
          created_at: apiMeta.created_at,
          updated_at: activityAt,
          sizeBytes,
          messageCount: rows.length,
          cachedAt: Date.now(),
        };
        const rowsRec = { uuid: apiMeta.uuid, rows };

        await dbPut(DB_META_STORE, metaRec);
        await dbPut(DB_ROWS_STORE, rowsRec);

        setSidebarMeta(apiMeta.uuid, {
          sizeBytes,
          createdAt: apiMeta.created_at || sidebarMeta.get(apiMeta.uuid)?.createdAt || null,
          updatedAt: activityAt || sidebarMeta.get(apiMeta.uuid)?.updatedAt || null,
        });
        scheduleSidebarDecorate();
        return metaRec;
      } finally {
        inFlight.delete(apiMeta.uuid);
      }
    })();
    inFlight.set(apiMeta.uuid, p);
    return p;
  }

  async function fetchChatsConcurrent(chats, orgId, signal, concurrency, onRecord, delayMs = 0) {
    let idx = 0, done = 0;
    const worker = async () => {
      while (idx < chats.length) {
        if (signal.aborted) return;
        const my = idx++;
        const meta = chats[my];
        let record;
        let errored = false;
        try {
          record = await fetchOneChat(meta, orgId, signal);
        } catch (err) {
          if (err.name === 'AbortError' || signal.aborted) return;
          errored = true;
          // Synthesize a minimal record so progress counters still advance,
          // but flag it so callers know not to overwrite valid cached data.
          record = {
            uuid: meta.uuid,
            name: meta.name,
            created_at: meta.created_at,
            error: err.message,
            _errored: true,
          };
        }
        if (signal.aborted) return;
        done++;
        if (record && onRecord) onRecord(record, done, chats.length);
        if (delayMs > 0) await new Promise(r => setTimeout(r, delayMs));
      }
    };
    await Promise.all(Array.from({ length: concurrency }, () => worker()));
  }

  async function fetchAllChatMetadata(orgId, limit, signal) {
    const fetchOne = async (starred) => {
      const url = `/api/organizations/${orgId}/chat_conversations_v2?limit=${limit}&starred=${starred}&consistency=eventual`;
      const resp = await originalFetch(url, { credentials: 'include', signal });
      if (!resp.ok) return [];
      const data = await resp.json();
      return extractList(data).list || [];
    };
    const [starred, unstarred] = await Promise.all([fetchOne(true), fetchOne(false)]);
    return [...starred, ...unstarred];
  }

  // ============================================================
  //  BACKGROUND PREFETCH (silent)
  // ============================================================
  let bgController = null;
  let bgDone = false;
  // When did we last successfully pull the full chat_conversations_v2 list?
  // Used by the modal to skip redundant refresh calls within ~5 min.
  let lastMetadataRefreshAt = 0;

  async function runBackgroundPrefetch() {
    if (!BACKGROUND_PREFETCH || bgDone) return;
    if (bgController) return;
    if (!cachedOrgId) { setTimeout(runBackgroundPrefetch, 2000); return; }
    if (document.hidden) {
      document.addEventListener('visibilitychange', () => {
        if (!document.hidden) runBackgroundPrefetch();
      }, { once: true });
      return;
    }

    bgController = new AbortController();
    const signal = bgController.signal;
    LOG('background prefetch: starting');

    try {
      await ensureSidebarMeta();
      if (signal.aborted) return;

      const metaList = await fetchAllChatMetadata(cachedOrgId, cachedLimit || 500, signal);
      if (signal.aborted) return;
      lastMetadataRefreshAt = Date.now();

      const seen = new Set();
      const uniq = metaList.filter(c => !seen.has(c.uuid) && seen.add(c.uuid));

      const needFetch = [];
      for (const meta of uniq) {
        if (signal.aborted) return;
        const cached = await dbGet(DB_META_STORE, meta.uuid);
        if (needsRefetch(cached, meta)) needFetch.push(meta);
      }

      if (needFetch.length === 0) {
        LOG('background prefetch: all cached');
        bgDone = true;
        setSuperchatButtonProgress(null);
        warmCache.prime();  // cache already full — prime modal warm cache now
        return;
      }

      LOG(`background prefetch: ${needFetch.length} chats, concurrency=${BG_CONCURRENCY}`);
      setSuperchatButtonProgress(0);
      await fetchChatsConcurrent(
        needFetch, cachedOrgId, signal, BG_CONCURRENCY,
        (_r, done, total) => {
          setSuperchatButtonProgress(done / total);
          warmCache.invalidate();  // keep warm cache fresh during prefetch
          if (done === total || done % 10 === 0) {
            LOG(`background prefetch: ${done}/${total}`);
          }
        },
        BG_BETWEEN_FETCH_MS,
      );

      if (!signal.aborted) {
        bgDone = true;
        setSuperchatButtonProgress(null);
        warmCache.invalidate();
        LOG('background prefetch: complete');
      }
    } catch (err) {
      if (err.name === 'AbortError' || signal.aborted) return;
      LOG('background prefetch error:', err);
      setTimeout(() => { bgController = null; runBackgroundPrefetch(); }, 30000);
    } finally {
      bgController = null;
    }
  }

  function scheduleBackgroundPrefetch() {
    if (!BACKGROUND_PREFETCH) return;
    setTimeout(() => {
      if (cachedOrgId) runBackgroundPrefetch();
      else {
        const ticker = setInterval(() => {
          if (cachedOrgId) { clearInterval(ticker); runBackgroundPrefetch(); }
        }, 1500);
        setTimeout(() => clearInterval(ticker), 60000);
      }
    }, BG_START_DELAY_MS);
  }
  scheduleBackgroundPrefetch();

  // ============================================================
  //  MESSAGE EXTRACTION
  // ============================================================
  function extractMessageText(m) {
    if (!m) return '';
    if (typeof m.text === 'string' && m.text.length) return m.text;
    if (typeof m.content === 'string') return m.content;
    if (Array.isArray(m.content)) {
      return m.content
        .map(c => {
          if (typeof c === 'string') return c;
          if (typeof c?.text === 'string') return c.text;
          if (typeof c?.input === 'object') return `[tool use: ${c?.name || ''}]`;
          return '';
        })
        .filter(Boolean)
        .join('\n');
    }
    return '';
  }
  function normalizeSender(raw) {
    const s = String(raw || '').toLowerCase();
    if (s === 'human' || s === 'user') return 'user';
    if (s === 'assistant' || s === 'claude') return 'claude';
    if (s === 'system') return 'system';
    return s || 'unknown';
  }
  // (extractAllMessages / flattenAllMessages removed in v29 — virtualizer
  // flattens inline via flattenRecordsToRows)

  // ============================================================
  //  SUPERCHAT MODAL
  // ============================================================
  let modalEl = null;
  let activeController = null;

  function openSuperchat() {
    if (modalEl) return;
    if (!cachedOrgId) setOrgIdFrom('open-scan', scanForOrgId());
    injectStyles();

    // Pause bg prefetch so we don't step on each other
    if (bgController) { bgController.abort(); bgController = null; }

    const overlay = document.createElement('div');
    overlay.className = 'sbc-sc-overlay';
    overlay.innerHTML = `
      <div class="sbc-sc-modal">
        <div class="sbc-sc-header">
          <h2 class="sbc-sc-title">Superchat</h2>
          <span class="sbc-sc-progress">Loading…</span>
          <button class="sbc-sc-close" title="Close (Esc)">×</button>
        </div>
        <div class="sbc-sc-toolbar">
          <input class="sbc-sc-search" type="text" placeholder="Search messages (Enter)" autocomplete="off" spellcheck="false">
          <div class="sbc-sc-sender-toggle" role="group" aria-label="Sender filter">
            <button class="sbc-sender-btn active" data-sender="all">All</button>
            <button class="sbc-sender-btn" data-sender="user">Me</button>
            <button class="sbc-sender-btn" data-sender="claude">Claude</button>
          </div>
          <button class="sbc-sc-chat-filter" title="Filter chats">Chats: all</button>
          <button class="sbc-sc-starred-only" title="Show only starred messages (s on a row to star)" aria-pressed="false">★ only</button>
          <button class="sbc-sc-theme-toggle" title="Toggle theme: dark contrast vs. match site">🌓</button>
          <span class="sbc-sc-count"></span>
        </div>
        <div class="sbc-sc-chat-panel" hidden></div>
        <div class="sbc-bar"><div class="sbc-bar-fill" style="width:0%"></div></div>
        <div class="sbc-sc-body"><div class="sbc-sc-empty">Loading cached messages…</div></div>
      </div>
    `;
    document.body.appendChild(overlay);
    modalEl = overlay;

    // Apply theme based on current mode. 'contrast' = dark (default, no class);
    // 'themed' = match claude.ai — add .sbc-light if site is in light mode.
    const applyTheme = () => {
      const modal = overlay.querySelector('.sbc-sc-modal');
      if (!modal) return;
      const useLight = themeMode === 'themed' && detectSiteTheme() === 'light';
      modal.classList.toggle('sbc-light', useLight);
    };
    overlay._sbcApplyTheme = applyTheme;  // so loadAndRender's toolbar can call
    applyTheme();

    activeController = new AbortController();
    const signal = activeController.signal;

    const close = () => {
      if (overlay._sbcNavKeyHandler) {
        document.removeEventListener('keydown', overlay._sbcNavKeyHandler);
      }
      activeController?.abort();
      activeController = null;
      overlay._sbcController?.destroy();
      overlay.remove();
      modalEl = null;
      if (!bgDone) { bgController = null; runBackgroundPrefetch(); }
    };
    overlay.addEventListener('click', (e) => { if (e.target === overlay) close(); });
    overlay.querySelector('.sbc-sc-close').addEventListener('click', close);

    loadAndRender(overlay, signal).catch(err => {
      if (err.name === 'AbortError' || signal.aborted) return;
      LOG('superchat error:', err);
      overlay.querySelector('.sbc-sc-body').innerHTML =
        `<div class="sbc-sc-empty">Failed: ${escapeHTML(err.message || String(err))}</div>`;
    });
  }

  async function loadAndRender(overlay, signal) {
    const progressEl = overlay.querySelector('.sbc-sc-progress');
    const barContainer = overlay.querySelector('.sbc-bar');
    const barEl = overlay.querySelector('.sbc-bar-fill');
    const bodyEl = overlay.querySelector('.sbc-sc-body');

    // v34: warm cache returns { metaList } — tiny, fast.
    const warm = await warmCache.get();
    if (signal.aborted) return;

    // Load persisted stars before building UI so star icons render correctly
    // on first paint. Awaiting here adds ~10ms worst case; worth it to avoid
    // a visual flash of unstarred → starred as stars hydrate asynchronously.
    await loadStarredIds();
    if (signal.aborted) return;

    // records map holds META records only (no content, no rows).
    // uuid → { uuid, name, created_at, updated_at, sizeBytes, messageCount, cachedAt }
    const records = new Map(warm.metaList.map(r => [r.uuid, r]));

    // Total message count is pre-computed per meta record — no iteration needed.
    const totalMsgCount = () => {
      let n = 0;
      for (const r of records.values()) n += (r.messageCount || 0);
      return n;
    };

    const controller = createSuperchat(bodyEl);
    overlay._sbcController = controller;

    // ----- toolbar wiring -----
    const searchInput = overlay.querySelector('.sbc-sc-search');
    const senderBtns = overlay.querySelectorAll('.sbc-sender-btn');
    const chatFilterBtn = overlay.querySelector('.sbc-sc-chat-filter');
    const starredOnlyBtn = overlay.querySelector('.sbc-sc-starred-only');
    const themeToggleBtn = overlay.querySelector('.sbc-sc-theme-toggle');
    const chatPanel = overlay.querySelector('.sbc-sc-chat-panel');
    const countEl = overlay.querySelector('.sbc-sc-count');

    const uiFilter = {
      query: '',
      sender: 'all',
      chats: null,
    };

    const escapeRegex = (s) => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');

    // allMsgRows: the full flat array of message rows across all chats.
    // Populated incrementally as chat_rows records load from IndexedDB.
    // Virtualizer reads from here via setFlatRows.
    let allMsgRows = [];

    const applyUiFilter = () => {
      const senders = uiFilter.sender === 'all' ? null : new Set([uiFilter.sender]);
      const queryRe = uiFilter.query ? new RegExp(escapeRegex(uiFilter.query), 'gi') : null;
      controller.setFilter({ queryRe, senders, chatUuids: uiFilter.chats });
      updateCount();
    };

    const updateCount = () => {
      // The virtualizer computed visibleMsgCount as a side-effect of
      // applyFilter — no need to re-walk allMsgRows here. Falls back to total
      // if the controller hasn't populated it yet (first call before setFlatRows).
      const total = totalMsgCount();
      const visible = controller.getVisibleMsgCount?.() ?? allMsgRows.length ?? total;
      countEl.textContent = visible === total
        ? `${total.toLocaleString()} messages`
        : `${visible.toLocaleString()} / ${total.toLocaleString()}`;
    };

    searchInput.addEventListener('keydown', (e) => {
      if (e.key === 'Enter') {
        uiFilter.query = searchInput.value.trim();
        applyUiFilter();
      } else if (e.key === 'Escape' && searchInput.value) {
        e.stopPropagation();
        searchInput.value = '';
        uiFilter.query = '';
        applyUiFilter();
      }
    });

    senderBtns.forEach(b => {
      b.addEventListener('click', () => {
        senderBtns.forEach(x => x.classList.toggle('active', x === b));
        uiFilter.sender = b.dataset.sender;
        applyUiFilter();
      });
    });

    const renderChatPanel = () => {
      const entries = [...records.values()]
        .filter(r => r.name)
        .sort((a, b) => (a.name || '').localeCompare(b.name || ''));
      const rowsHTML = entries.map(r => {
        const checked = !uiFilter.chats || uiFilter.chats.has(r.uuid);
        return `<label class="sbc-chat-row">
          <input type="checkbox" data-uuid="${escapeHTML(r.uuid)}" ${checked ? 'checked' : ''}>
          <span>${escapeHTML(r.name)}</span>
        </label>`;
      }).join('');
      chatPanel.innerHTML = `
        <div class="sbc-chat-panel-head">
          <button class="sbc-chat-all">Select all</button>
          <button class="sbc-chat-none">Clear all</button>
          <span class="sbc-chat-count">${entries.length} chats</span>
        </div>
        <div class="sbc-chat-list">${rowsHTML}</div>
      `;
    };

    chatFilterBtn.addEventListener('click', () => {
      const nowOpen = chatPanel.hasAttribute('hidden');
      if (nowOpen) {
        renderChatPanel();
        chatPanel.removeAttribute('hidden');
      } else {
        chatPanel.setAttribute('hidden', '');
      }
    });

    // Starred-only toggle: show only messages the user has starred.
    let starredOnlyState = false;
    starredOnlyBtn.addEventListener('click', () => {
      starredOnlyState = !starredOnlyState;
      starredOnlyBtn.classList.toggle('active', starredOnlyState);
      starredOnlyBtn.setAttribute('aria-pressed', starredOnlyState ? 'true' : 'false');
      controller.setStarredOnly(starredOnlyState);
      updateCount();
    });

    // Theme toggle: cycle 'contrast' ↔ 'themed'. Re-applies theme class.
    // applyTheme is defined in openSuperchat's closure, exposed via overlay.
    themeToggleBtn.addEventListener('click', () => {
      const next = themeMode === 'contrast' ? 'themed' : 'contrast';
      setThemeMode(next);
      overlay._sbcApplyTheme?.();
      toast.show(next === 'themed' ? 'Theme: match site' : 'Theme: dark contrast', true);
    });

    chatPanel.addEventListener('change', (e) => {
      if (e.target.tagName !== 'INPUT') return;
      const uuid = e.target.dataset.uuid;
      if (!uiFilter.chats) uiFilter.chats = new Set(records.keys());
      if (e.target.checked) uiFilter.chats.add(uuid);
      else uiFilter.chats.delete(uuid);
      if (uiFilter.chats.size === records.size) uiFilter.chats = null;
      chatFilterBtn.textContent = uiFilter.chats
        ? `Chats: ${uiFilter.chats.size}/${records.size}`
        : 'Chats: all';
      applyUiFilter();
    });

    chatPanel.addEventListener('click', (e) => {
      if (e.target.classList.contains('sbc-chat-all')) {
        uiFilter.chats = null;
        chatFilterBtn.textContent = 'Chats: all';
        applyUiFilter();
        renderChatPanel();
      } else if (e.target.classList.contains('sbc-chat-none')) {
        uiFilter.chats = new Set();
        chatFilterBtn.textContent = `Chats: 0/${records.size}`;
        applyUiFilter();
        renderChatPanel();
      }
    });

    overlay.addEventListener('click', (e) => {
      if (chatPanel.hasAttribute('hidden')) return;
      if (e.target === chatFilterBtn || chatPanel.contains(e.target)) return;
      chatPanel.setAttribute('hidden', '');
    });

    // Keyboard navigation handler: attached to document (not overlay) so it
    // fires regardless of which element inside/outside the modal has focus.
    // Previously attached to overlay — but when focus was on <body> (common
    // after clicking a non-focusable row), events bubbled through body→html
    // →document without passing through overlay, so j/k/arrows/c/s all
    // silently broke.
    const onNavKey = (e) => {
      // Skip if modal is gone (paranoid — close() removes this listener, but
      // a race could have a stray event in-flight).
      if (!modalEl || !document.body.contains(modalEl)) return;

      if ((e.ctrlKey || e.metaKey) && e.key === 'f') {
        e.preventDefault();
        searchInput.focus();
        searchInput.select();
        return;
      }

      // Skip when focus is in the search input (arrow keys should move
      // text cursor, not selection).
      const inInput = e.target === searchInput ||
        (e.target.tagName === 'INPUT' || e.target.tagName === 'TEXTAREA');
      if (inInput) return;

      // Skip when modifier keys are held (don't interfere with browser shortcuts)
      if (e.ctrlKey || e.metaKey || e.altKey) return;

      if (e.key === 'ArrowDown' || e.key === 'j') {
        e.preventDefault();
        controller.moveSelection(1);
      } else if (e.key === 'ArrowUp' || e.key === 'k') {
        e.preventDefault();
        controller.moveSelection(-1);
      } else if (e.key === 'PageDown') {
        e.preventDefault();
        controller.moveSelection(10);
      } else if (e.key === 'PageUp') {
        e.preventDefault();
        controller.moveSelection(-10);
      } else if (e.key === 'Enter') {
        const row = controller.getSelectedRow?.();
        if (row && row.chatUuid) {
          e.preventDefault();
          location.href = `/chat/${row.chatUuid}`;
        }
      } else if (e.key === 'c' && !e.shiftKey) {
        // Copy selected row's text
        const row = controller.getSelectedRow?.();
        if (row && row.text) {
          e.preventDefault();
          navigator.clipboard.writeText(row.text).then(
            () => toast.show('Copied to clipboard', true),
            () => toast.show('Copy failed'),
          );
        }
      } else if (e.key === 's' && !e.shiftKey) {
        // Toggle star on selected row
        const row = controller.getSelectedRow?.();
        if (row && row.id) {
          e.preventDefault();
          toggleStar(row.id).then(nowStarred => {
            toast.show(nowStarred ? 'Starred' : 'Unstarred', true);
            controller.notifyStarChanged();
          });
        }
      } else if (e.key === 'Escape') {
        // Esc: clear selection if active, otherwise close the modal.
        if (controller.getSelectedRow?.()) {
          e.stopImmediatePropagation();
          e.preventDefault();
          controller.clearSelection();
        } else {
          // No selection — close modal. We handle this here rather than in
          // a separate onKey listener because the listener order matters
          // for the selection-vs-close precedence.
          e.preventDefault();
          const closeBtn = overlay.querySelector('.sbc-sc-close');
          if (closeBtn) closeBtn.click();
        }
      }
    };
    document.addEventListener('keydown', onNavKey);
    overlay._sbcNavKeyHandler = onNavKey;  // so close() can remove it

    // ----- empty state handling -----

    if (records.size === 0) {
      if (!cachedOrgId) {
        bodyEl.innerHTML = `<div class="sbc-sc-empty">
          No cached data, org ID not detected.<br>Navigate the sidebar once, then reopen.
        </div>`;
        barContainer.classList.add('hidden');
        return;
      }
      // Have orgId but no cache: the cold-start skeleton injection (below)
      // will paint within ~200ms. Show a single progress string meanwhile;
      // avoid writing placeholder HTML into bodyEl that would then flash-replace.
      progressEl.textContent = 'Loading chat list…';
    }

    // ----- stream rows from chat_rows store in batches -----
    // Strategy (post-v36):
    //   - Stream newest chats first (sort by updated_at desc). First batch
    //     contains the messages user is most likely looking for.
    //   - Render ONCE after batch 1 (first paint ~300ms), then suppress
    //     further renders until streaming finishes. Rebuilds during streaming
    //     were thrashing the list visually AND taking ~700ms of main thread.
    //   - One final setFlatRows at end. Total streaming time unchanged or
    //     better, but the list stays stable mid-stream.
    const ROWS_BATCH = 40;
    const YIELD_MS = 0;
    progressEl.textContent = `Loading messages from ${records.size} chats…`;
    barContainer.classList.remove('hidden');

    // Sort uuids by updated_at descending so the first batches contain the
    // user's most-recent messages. Falls back to created_at then uuid order.
    const uuids = [...records.values()]
      .sort((a, b) => {
        const ta = new Date(a.updated_at || a.created_at || 0).getTime();
        const tb = new Date(b.updated_at || b.created_at || 0).getTime();
        return tb - ta;  // newest first regardless of OLDEST_FIRST (that's for display order)
      })
      .map(r => r.uuid);
    let loadedCount = 0;

    for (let i = 0; i < uuids.length; i += ROWS_BATCH) {
      if (signal.aborted) return;
      const batch = uuids.slice(i, i + ROWS_BATCH);
      const results = await dbGetMany(DB_ROWS_STORE, batch);
      if (signal.aborted) return;

      for (const rec of results) {
        if (!rec || !rec.rows) continue;
        for (const row of rec.rows) allMsgRows.push(row);
        loadedCount++;
      }

      progressEl.textContent = `Loaded ${loadedCount} / ${uuids.length} chats · ${allMsgRows.length.toLocaleString()} messages`;
      barEl.style.width = `${Math.round((loadedCount / uuids.length) * 100)}%`;

      const isFirst = i === 0;
      const isLast = (i + ROWS_BATCH) >= uuids.length;
      // Render exactly twice during streaming: after batch 1 (first paint of
      // newest chats), and after the final batch. No `.slice()` — setFlatRows
      // only sorts in place; the caller doesn't need immutable input after.
      if (isFirst || isLast) {
        controller.setFlatRows(allMsgRows);
        updateCount();
      }

      await new Promise(r => setTimeout(r, YIELD_MS));
    }
    barContainer.classList.add('hidden');

    // ----- optional background refresh via API -----

    if (!cachedOrgId) {
      progressEl.textContent = `${totalMsgCount().toLocaleString()} messages from ${records.size} chats · org not detected`;
      return;
    }

    // If background prefetch has already finished and we refreshed the list
    // within the last 5 minutes, skip the metadata fetch + diff. Saves 500ms-
    // several seconds after a warm open with no new activity. Tradeoff: new
    // chats created in another tab within 5min won't appear until reload.
    const METADATA_REFRESH_TTL_MS = 5 * 60 * 1000;
    const refreshAge = Date.now() - lastMetadataRefreshAt;
    if (bgDone && refreshAge < METADATA_REFRESH_TTL_MS) {
      progressEl.textContent = `${totalMsgCount().toLocaleString()} messages · up to date`;
      return;
    }

    let metaList;
    try {
      metaList = await fetchAllChatMetadata(cachedOrgId, cachedLimit || 500, signal);
      lastMetadataRefreshAt = Date.now();
    } catch (err) {
      if (err.name === 'AbortError' || signal.aborted) return;
      // Metadata refresh failed (offline, 429, etc). We've already streamed
      // whatever was cached — keep that on screen rather than throwing to the
      // outer catch that would replace the whole body with "Failed:".
      LOG('metadata refresh failed, keeping cached view:', err);
      barContainer.classList.add('hidden');
      progressEl.textContent = `${totalMsgCount().toLocaleString()} messages · offline (cached)`;
      return;
    }
    if (signal.aborted) return;

    const seen = new Set();
    const uniq = metaList.filter(c => !seen.has(c.uuid) && seen.add(c.uuid));
    const needFetch = [];
    for (const m of uniq) {
      const existing = records.get(m.uuid);
      if (!existing || needsRefetch(existing, m)) needFetch.push(m);
    }

    if (needFetch.length === 0) {
      progressEl.textContent = `${totalMsgCount().toLocaleString()} messages · up to date`;
      return;
    }

    barContainer.classList.remove('hidden');
    progressEl.textContent = `0 / ${needFetch.length} updating…`;
    barEl.style.width = '0%';

    // Cold-start UX: if allMsgRows was empty (no cache yet), inject a
    // "skeleton" row per needFetch chat immediately. Gives instant visual
    // feedback of scope — user sees hundreds of chat names + dates even
    // before any rows actually arrive. Skeletons are tagged with _skel so
    // we can swap them out as each chat's real rows arrive.
    const coldStart = allMsgRows.length === 0;
    if (coldStart) {
      for (const m of needFetch) {
        allMsgRows.push({
          chatUuid: m.uuid,
          chatName: m.name || 'Untitled',
          sender: 'user',  // neutral default for skeleton styling
          timestamp: m.created_at || m.updated_at || new Date().toISOString(),
          text: '⋯ loading messages…',
          messageUuid: `skel:${m.uuid}`,
          _skel: true,
        });
      }
      controller.setFlatRows(allMsgRows);
      updateCount();
    }

    let lastRebuild = 0;
    const REBUILD_INTERVAL_MS = coldStart ? 200 : 800;  // snappier on first load
    let rebuildCount = 0;

    await fetchChatsConcurrent(
      needFetch, cachedOrgId, signal, FETCH_CONCURRENCY,
      async (metaRec, done, total) => {
        if (signal.aborted) return;
        // On fetch error: advance the progress counter but do NOT overwrite
        // cached records or mutate allMsgRows. The existing data (skeleton
        // or previously-cached rows) stays on screen.
        if (!metaRec._errored) {
          records.set(metaRec.uuid, metaRec);
          const rowsRec = await dbGet(DB_ROWS_STORE, metaRec.uuid);
          if (rowsRec && rowsRec.rows) {
            // Remove any prior rows (skeleton or real) for this chat, append new
            allMsgRows = allMsgRows.filter(r => r.chatUuid !== metaRec.uuid);
            for (const r of rowsRec.rows) allMsgRows.push(r);
          }
        }

        progressEl.textContent = `${done} / ${total} updating · ${allMsgRows.length.toLocaleString()} messages`;
        barEl.style.width = `${Math.round((done / total) * 100)}%`;
        warmCache.invalidate();

        const now = Date.now();
        const interval = (coldStart && rebuildCount < 30) ? 200 : 800;
        if (done === total || now - lastRebuild >= interval) {
          lastRebuild = now;
          rebuildCount++;
          controller.setFlatRows(allMsgRows);
          updateCount();
        }
      },
    );

    if (signal.aborted) return;

    // Final rebuild strips any lingering skeletons for chats that somehow
    // failed to fetch (network error, 429 retries exhausted).
    allMsgRows = allMsgRows.filter(r => !r._skel);
    controller.setFlatRows(allMsgRows);
    updateCount();
    barContainer.classList.add('hidden');
    progressEl.textContent = `${totalMsgCount().toLocaleString()} messages from ${records.size} chats`;
    bgDone = true;
  }

  // Escape untrusted text for safe HTML injection.
  const escapeHTML = (s) => String(s)
    .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;').replace(/'/g, '&#39;');

  // Wrap query matches in <mark> tags. Input must be already-escaped or raw text;
  // we escape first, then wrap matches by re-matching against the escaped string.
  // Query regex is case-insensitive and escaped upstream.
  function highlightHTML(text, queryRe) {
    if (!queryRe) return escapeHTML(text);
    const escaped = escapeHTML(text);
    // Reset lastIndex to avoid state leakage across calls (queryRe has /g flag)
    queryRe.lastIndex = 0;
    return escaped.replace(queryRe, (m) => `<mark class="sbc-hl">${m}</mark>`);
  }

  // ============================================================
  //  SUPERCHAT VIRTUALIZER
  // ============================================================
  // Renders only the rows visible in the viewport (plus a small overscan
  // buffer). Row heights are variable and measured on first layout; unseen
  // rows use an estimated height which is refined as scrolling reveals them.
  //
  // Why: rendering 20k+ full DOM rows eagerly crashes the browser. This
  // keeps DOM at ~40-80 nodes regardless of message count.
  //
  // Contract: createSuperchat(bodyEl) → controller with:
  //   setRecords(records)     – replace the full data set (called once per full refresh)
  //   upsertRecord(record)    – add/replace one chat's messages (incremental during fetch)
  //   destroy()               – tear down listeners / DOM
  //
  // Internal row types: 'day' (header) or 'msg' (message).
  const createSuperchat = (bodyEl) => {
    const OVERSCAN_PX = 600;            // render this much above/below viewport
    const ESTIMATED_MSG_HEIGHT = 120;   // initial guess for unmeasured message rows
    const ESTIMATED_DAY_HEIGHT = 40;    // day-header row estimate
    const MIN_RERENDER_SCROLL = 50;     // pixels of scroll before re-evaluating window

    // Flat ordered list of rows. Each is either {type:'day', id, label}
    // or {type:'msg', id, chatUuid, chatName, sender, timestamp, text}.
    let rows = [];
    // All rows before filtering — source of truth. `rows` is the filtered view.
    let allRows = [];
    // Filter state: {queryRe, senders:Set|null, chatUuids:Set|null}
    //   queryRe   — RegExp or null (text search, case-insensitive, global)
    //   senders   — Set of allowed sender strings, or null = all
    //   chatUuids — Set of allowed chat uuids, or null = all
    let filterState = null;
    // uuid → array of row indices belonging to that chat (for targeted invalidation)
    let rowIndicesByChat = new Map();
    // Keyboard selection: tracked by row ID so it survives filter/sort changes.
    // The index is recomputed on demand from the current `rows` array.
    let selectedRowId = null;
    // Starred-only filter: when true, applyFilter drops rows whose id isn't
    // in starredIds. Toggled via the ★-only button in the toolbar.
    let starredOnly = false;
    // rowId → measured height (px). Estimate used until measured.
    // Persisted to IndexedDB so gaps never re-flicker across sessions.
    const heightCache = new Map();
    // Pending writes to persist; flushed on idle.
    const pendingHeightWrites = new Map();
    let heightFlushScheduled = false;
    const scheduleHeightFlush = () => {
      if (heightFlushScheduled) return;
      heightFlushScheduled = true;
      const run = async () => {
        heightFlushScheduled = false;
        await flushHeightWrites();
      };
      if (typeof requestIdleCallback === 'function') {
        requestIdleCallback(run, { timeout: 2000 });
      } else {
        setTimeout(run, 500);
      }
    };
    // Fire-and-forget flush of any pending writes. Called from scheduler and
    // from destroy() to capture last-second measurements before the modal closes.
    const flushHeightWrites = async () => {
      if (pendingHeightWrites.size === 0) return;
      const batch = [...pendingHeightWrites.entries()].map(([id, px]) => ({ id, px }));
      pendingHeightWrites.clear();
      try { await dbPutBatch(DB_HEIGHTS_STORE, batch); } catch (e) { /* ignore */ }
    };
    const rememberHeight = (id, px) => {
      heightCache.set(id, px);
      pendingHeightWrites.set(id, px);
      scheduleHeightFlush();
    };
    // Hydrate from persistent store in background. Populates heightCache;
    // already-mounted rows will benefit on next render. This is async but
    // non-blocking: if it arrives after initial render, subsequent renders
    // pick it up automatically via getHeight().
    (async () => {
      try {
        const all = await dbGetAll(DB_HEIGHTS_STORE);
        for (const rec of all) {
          // Only populate entries we haven't already measured in this session.
          // Fresh measurements (via rememberHeight) take precedence over DB
          // values — otherwise hydration could overwrite a height measured
          // while dbGetAll was in flight.
          if (rec && rec.id && rec.px > 0 && !heightCache.has(rec.id)) {
            heightCache.set(rec.id, rec.px);
          }
        }
        // If we had rows already, redo offsets with real heights
        if (allRows.length > 0) {
          rebuildOffsets();
          scheduleRender();
        }
      } catch (e) { /* ignore */ }
    })();
    // rowId → currently-mounted <div> (sparse — only visible rows)
    const mounted = new Map();
    // Recycled DOM elements we can reuse instead of creating new ones
    const freePool = [];

    // Cumulative offsets: offsets[i] = sum of heights of rows[0..i-1].
    // Rebuilt when rows change or heights update. O(N) rebuild — fine because
    // N changes bounded by chat-completion events, not every scroll.
    let offsets = [];
    let totalHeight = 0;

    const spacer = document.createElement('div');
    spacer.className = 'sbc-vt-spacer';
    bodyEl.innerHTML = '';
    bodyEl.appendChild(spacer);

    // Sticky day-header: sits pinned at the top of the scroll area, contents
    // updated on each render to the current day at viewport top. Lives outside
    // the spacer so it isn't affected by the absolute-positioned rows.
    const stickyDay = document.createElement('div');
    stickyDay.className = 'sbc-vt-sticky sbc-day';
    stickyDay.style.display = 'none';
    bodyEl.appendChild(stickyDay);

    // Scroll pill: a floating label showing the month/year of the viewport
    // top. Appears while scrolling, fades out after brief idle. Gives a
    // temporal sense of where you are in a long history.
    const scrollPill = document.createElement('div');
    scrollPill.className = 'sbc-scroll-pill';
    bodyEl.appendChild(scrollPill);
    let scrollPillFadeTimer = null;
    const showScrollPill = (text) => {
      if (scrollPill.textContent !== text) scrollPill.textContent = text;
      scrollPill.classList.add('visible');
      clearTimeout(scrollPillFadeTimer);
      scrollPillFadeTimer = setTimeout(() => scrollPill.classList.remove('visible'), 800);
    };

    // Date rail: vertical strip along the right edge of the modal body area.
    // Positioned OUTSIDE bodyEl (sibling in modal) so it doesn't scroll with
    // content and doesn't interfere with the virtualizer's contain:strict.
    // Built once per setFlatRows / setFilter; ticks are absolutely positioned
    // by percentage of totalHeight.
    const dateRail = document.createElement('div');
    dateRail.className = 'sbc-date-rail';
    // bodyEl's parent is .sbc-sc-modal. Append there so rail overlays the
    // body's right edge via absolute positioning.
    (bodyEl.parentElement || bodyEl).appendChild(dateRail);
    // Array of { label, firstRowIdx, isYear }
    let railEntries = [];
    const rebuildDateRail = () => {
      railEntries = [];
      let prevYear = null, prevMonth = null;
      for (let i = 0; i < rows.length; i++) {
        const r = rows[i];
        if (r.type !== 'msg' || !r.timestamp) continue;
        const d = new Date(r.timestamp);
        if (isNaN(d)) continue;
        const y = d.getFullYear(), m = d.getMonth();
        if (y !== prevYear) {
          railEntries.push({ label: String(y), firstRowIdx: i, isYear: true });
          prevYear = y; prevMonth = m;
        } else if (m !== prevMonth) {
          const months = ['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'];
          railEntries.push({ label: months[m], firstRowIdx: i, isYear: false });
          prevMonth = m;
        }
      }
      if (totalHeight === 0 || railEntries.length === 0) {
        dateRail.innerHTML = '';
        return;
      }
      // Positioning: each tick's vertical position = percentage of total scroll
      // height. When user clicks, we scrollTop to offsets[firstRowIdx].
      //
      // Collision handling with year-merging:
      //  1. Compute each entry's pixel position.
      //  2. Walk entries; when a year would overlap the previous rendered
      //     year, merge them into a range label ('2023–24', '2023–25', ...)
      //     rather than dropping either.
      //  3. Months drop if they'd overlap the last rendered entry. Year
      //     labels take precedence, so dropped months don't displace years.
      const railPx = dateRail.clientHeight || 600;  // fallback if not yet laid out
      // Separate gap thresholds: years need more breathing room (they're
      // bolder + larger font, and the range-merging logic prefers to fire
      // on collision). Months can pack tighter since they're dimmer.
      const YEAR_GAP_PX = 22;
      const MONTH_GAP_PX = 12;
      // First, annotate entries with pixel position.
      const annotated = railEntries.map(e => {
        const pct = (offsets[e.firstRowIdx] / totalHeight) * 100;
        return { ...e, pct, topPx: (pct / 100) * railPx };
      });

      // Walk + merge years + drop overlapping months. Output: `visible[]`.
      // Collision threshold depends on the INCOMING entry type: years need
      // YEAR_GAP; months only need MONTH_GAP. This lets months pack denser
      // while years trigger range-merging more aggressively.
      const visible = [];
      let lastRenderedPx = -Infinity;
      for (const e of annotated) {
        if (e.isYear) {
          if (e.topPx - lastRenderedPx < YEAR_GAP_PX && visible.length) {
            // Collides with the previous rendered entry. If that entry is also
            // a year, extend its label into a range (e.g., '2023' → '2023–24').
            // If it was a month, replace the month with this year (years win).
            const prev = visible[visible.length - 1];
            if (prev.isYear) {
              // Extract the start year from prev.label — it may already be a
              // range like '2023–24'; in which case extend the end.
              const m = prev.label.match(/^(\d{4})(?:–(\d{2,4}))?$/);
              const startYear = m ? parseInt(m[1], 10) : parseInt(prev.label, 10);
              const thisYear = parseInt(e.label, 10);
              if (!isNaN(startYear) && !isNaN(thisYear) && thisYear > startYear) {
                // Abbreviate trailing year to 2 digits if same century
                const endStr = Math.floor(thisYear / 100) === Math.floor(startYear / 100)
                  ? String(thisYear).slice(-2)
                  : String(thisYear);
                prev.label = `${startYear}–${endStr}`;
                // Don't update firstRowIdx — clicking the range jumps to the earliest year.
              }
              // Skip pushing `e` separately — it's been folded into prev.
              continue;
            } else {
              // Previous was a month; replace it with this year.
              visible.pop();
              visible.push(e);
              lastRenderedPx = e.topPx;
              continue;
            }
          }
          visible.push(e);
          lastRenderedPx = e.topPx;
        } else {
          // Month: drop if too close to last rendered.
          if (e.topPx - lastRenderedPx < MONTH_GAP_PX) continue;
          visible.push(e);
          lastRenderedPx = e.topPx;
        }
      }

      dateRail.innerHTML = visible.map(e => {
        return `<button class="sbc-rail-tick${e.isYear ? ' year' : ''}"
                       data-idx="${e.firstRowIdx}"
                       style="top:${e.pct.toFixed(2)}%"
                       title="Jump to ${escapeHTML(e.label)}">${escapeHTML(e.label)}</button>`;
      }).join('');
    };
    dateRail.addEventListener('click', (e) => {
      const tick = e.target.closest('.sbc-rail-tick');
      if (!tick) return;
      const idx = parseInt(tick.dataset.idx, 10);
      if (isNaN(idx) || idx < 0 || idx >= rows.length) return;
      bodyEl.scrollTop = Math.max(0, offsets[idx] - 40);
    });

    // Height estimation is critical for gap-free scrolling. Observed real
    // heights: short messages ~45-80px, medium ~120-300px, code dumps 500+.
    // Flat 120px estimate was off by 300-1500px avg → huge white gaps.
    //
    // Formula: 50px base (header + padding) + ~22px per wrapped line,
    // assuming ~80 chars per line of text. Won't be exact (depends on width,
    // line wrapping, markdown) but dramatically better than a constant.
    const BASE_ROW_PX = 50;
    const PX_PER_LINE = 22;
    const CHARS_PER_LINE = 80;
    const estimateHeight = (row) => {
      if (row.type === 'day') return ESTIMATED_DAY_HEIGHT;
      const len = row.text?.length || 0;
      // At minimum 1 line; round up to full wrapped lines.
      const lines = Math.max(1, Math.ceil(len / CHARS_PER_LINE));
      return BASE_ROW_PX + lines * PX_PER_LINE;
    };

    const getHeight = (row) => heightCache.get(row.id) ?? estimateHeight(row);

    const rebuildOffsets = () => {
      offsets = new Array(rows.length);
      let acc = 0;
      for (let i = 0; i < rows.length; i++) {
        offsets[i] = acc;
        acc += getHeight(rows[i]);
      }
      totalHeight = acc;
      spacer.style.height = `${totalHeight}px`;
    };

    // Binary search: find lowest index whose offset >= targetPx
    const indexForOffset = (targetPx) => {
      let lo = 0, hi = rows.length - 1;
      while (lo < hi) {
        const mid = (lo + hi) >> 1;
        if (offsets[mid] + getHeight(rows[mid]) <= targetPx) lo = mid + 1;
        else hi = mid;
      }
      return lo;
    };

    // Build a row element. For message rows we reuse from freePool when possible.
    // Child refs are cached on first creation (el._sbc = {time, sender, context, text})
    // so recycled rows don't pay for querySelector on every hydrate.
    const buildRow = (row) => {
      if (row.type === 'day') {
        const d = document.createElement('div');
        d.className = 'sbc-vt-row sbc-day';
        d.textContent = row.label;
        return d;
      }
      let el = freePool.pop();
      if (!el) {
        el = document.createElement('div');
        el.className = 'sbc-vt-row sbc-msg';
        el.innerHTML = `
          <div class="sbc-msg-header">
            <span class="sbc-msg-time"></span>
            <span class="sbc-msg-sender"></span>
            <span class="sbc-msg-context"></span>
            <button class="sbc-msg-star" title="Star message (s)" aria-label="Star">☆</button>
            <button class="sbc-msg-copy" title="Copy message (c)" aria-label="Copy">⧉</button>
            <a class="sbc-msg-open" href="#" title="Open chat" tabindex="0">Open ↗</a>
          </div>
          <div class="sbc-msg-text"></div>
        `;
        el._sbc = {
          time: el.querySelector('.sbc-msg-time'),
          sender: el.querySelector('.sbc-msg-sender'),
          context: el.querySelector('.sbc-msg-context'),
          star: el.querySelector('.sbc-msg-star'),
          copy: el.querySelector('.sbc-msg-copy'),
          open: el.querySelector('.sbc-msg-open'),
          text: el.querySelector('.sbc-msg-text'),
        };
        // Star toggle.
        el._sbc.star.addEventListener('click', async (e) => {
          e.stopPropagation();
          const current = el._row;
          if (!current || !current.id) return;
          const nowStarred = await toggleStar(current.id);
          el._sbc.star.classList.toggle('filled', nowStarred);
          el._sbc.star.textContent = nowStarred ? '★' : '☆';
          el.classList.toggle('sbc-msg-starred', nowStarred);
          notifyStarChanged();
        });
        // Copy button: copies the message text. Rest of the row is free for
        // native text selection — no click-copy hijacking anymore.
        el._sbc.copy.addEventListener('click', async (e) => {
          e.stopPropagation();
          const current = el._row;
          if (!current || !current.text) return;
          try {
            await navigator.clipboard.writeText(current.text);
            toast.show('Copied to clipboard', true);
            // Brief visual confirmation on the button itself: glyph swap + colour
            el._sbc.copy.classList.add('copied');
            el._sbc.copy.textContent = '✓';
            setTimeout(() => {
              el._sbc.copy.classList.remove('copied');
              el._sbc.copy.textContent = '⧉';
            }, 900);
          } catch (err) {
            toast.show('Copy failed');
          }
        });
      }
      const refs = el._sbc;
      el._row = row;  // for click-copy handler
      // Star visual state — read fresh from the module-global set on every hydrate
      // so recycled rows reflect the current starredIds. Done here not in `if (!el)`
      // so recycled elements update when the row they're hydrated with changes.
      const isStarred = starredIds.has(row.id);
      if (refs.star.classList.contains('filled') !== isStarred) {
        refs.star.classList.toggle('filled', isStarred);
        refs.star.textContent = isStarred ? '★' : '☆';
      }
      if (el.classList.contains('sbc-msg-starred') !== isStarred) {
        el.classList.toggle('sbc-msg-starred', isStarred);
      }
      const isSkel = !!row._skel;
      if (el.classList.contains('sbc-msg-skel') !== isSkel) {
        el.classList.toggle('sbc-msg-skel', isSkel);
      }
      const isSelected = row.id === selectedRowId;
      if (el.classList.contains('sbc-msg-selected') !== isSelected) {
        el.classList.toggle('sbc-msg-selected', isSelected);
      }
      const time = new Date(row.timestamp).toLocaleTimeString('en-GB', { hour: '2-digit', minute: '2-digit' });
      const href = `/chat/${row.chatUuid}`;
      if (refs.open.getAttribute('href') !== href) refs.open.setAttribute('href', href);
      if (refs.open.title !== `Open ${row.chatName}`) refs.open.title = `Open ${row.chatName}`;
      const senderClass = `sbc-msg-sender ${row.sender}`;
      if (refs.sender.className !== senderClass) refs.sender.className = senderClass;
      if (refs.sender.textContent !== row.sender) refs.sender.textContent = row.sender;
      if (refs.time.textContent !== time) refs.time.textContent = time;
      if (refs.context.textContent !== row.chatName) refs.context.textContent = row.chatName;
      const queryRe = filterState?.queryRe;
      const querySrc = queryRe ? queryRe.source : '';
      const key = `${row.id}|${querySrc}`;
      if (el._sbcKey !== key) {
        if (queryRe) {
          refs.text.innerHTML = highlightHTML(row.text, queryRe);
        } else {
          refs.text.textContent = row.text;
        }
        el._sbcKey = key;
      }
      return el;
    };

    const releaseRow = (el) => {
      if (el.classList.contains('sbc-msg') && freePool.length < 100) {
        el._sbcKey = null;  // force text re-render next time this el is reused
        el._row = null;     // drop row reference so click handler doesn't fire on stale row
        freePool.push(el);
      }
    };

    // Core render step: compute visible window, diff against mounted, patch.
    let renderScheduled = false;
    let offsetsDirty = false;  // set when measurements invalidate offsets
    const scheduleRender = () => {
      if (renderScheduled) return;
      renderScheduled = true;
      requestAnimationFrame(() => {
        renderScheduled = false;
        render();
      });
    };

    const render = () => {
      if (rows.length === 0) {
        for (const [, el] of mounted) el.remove();
        mounted.clear();
        return;
      }
      const scrollTop = bodyEl.scrollTop;
      const viewTop = Math.max(0, scrollTop - OVERSCAN_PX);
      const viewBot = scrollTop + bodyEl.clientHeight + OVERSCAN_PX;

      const startIdx = indexForOffset(viewTop);
      let endIdx = indexForOffset(viewBot);
      if (endIdx < rows.length - 1) endIdx++;

      const wanted = new Set();
      for (let i = startIdx; i <= endIdx; i++) wanted.add(rows[i].id);

      // Unmount rows outside the window
      for (const [id, el] of mounted) {
        if (!wanted.has(id)) {
          el.remove();
          releaseRow(el);
          mounted.delete(id);
        }
      }

      // Mount rows in the window, measure any new ones
      let anyMeasured = false;
      for (let i = startIdx; i <= endIdx; i++) {
        const row = rows[i];
        if (mounted.has(row.id)) {
          const el = mounted.get(row.id);
          const want = `translateY(${offsets[i]}px)`;
          if (el.style.transform !== want) el.style.transform = want;
          continue;
        }
        const el = buildRow(row);
        el.style.transform = `translateY(${offsets[i]}px)`;
        spacer.appendChild(el);
        mounted.set(row.id, el);

        if (!heightCache.has(row.id)) {
          const h = el.getBoundingClientRect().height;
          if (h > 0) {
            rememberHeight(row.id, h);
            if (Math.abs(h - estimateHeight(row)) > 1) anyMeasured = true;
          }
        }
      }

      // If measurements corrected estimates, schedule an offset rebuild + re-render
      // on the next frame. Splits cost across two frames so scrolling stays smooth,
      // and the re-render catches any visibility changes caused by the correction.
      if (anyMeasured && !offsetsDirty) {
        offsetsDirty = true;
        requestAnimationFrame(() => {
          offsetsDirty = false;
          rebuildOffsets();
          const idToIndex = new Map();
          for (let i = 0; i < rows.length; i++) idToIndex.set(rows[i].id, i);
          for (const [id, el] of mounted) {
            const idx = idToIndex.get(id);
            if (idx != null) {
              const want = `translateY(${offsets[idx]}px)`;
              if (el.style.transform !== want) el.style.transform = want;
            }
          }
          scheduleRender();
        });
      }

      // Sticky day header: find the last 'day' row whose offset <= viewport top.
      let stickyText = '';
      let stickyRow = null;
      for (let i = startIdx; i >= 0; i--) {
        if (rows[i].type === 'day') { stickyText = rows[i].label; stickyRow = rows[i]; break; }
      }
      if (stickyText) {
        if (stickyDay.textContent !== stickyText) stickyDay.textContent = stickyText;
        stickyDay.style.display = 'block';
      } else {
        stickyDay.style.display = 'none';
      }

      // Scroll pill: show the month/year of whichever message is at viewport
      // top. Different from stickyDay (which shows exact day) — the pill is
      // coarser and floats, so users get a temporal orientation while moving
      // through thousands of messages. Skips when viewing "Today"/"Yesterday"
      // (they're already obvious from context).
      const topMsg = rows[startIdx];
      if (topMsg && topMsg.type === 'msg' && topMsg.timestamp) {
        const d = new Date(topMsg.timestamp);
        if (!isNaN(d)) {
          const months = ['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'];
          const pillText = `${months[d.getMonth()]} ${d.getFullYear()}`;
          // Only show pill when scroll position has changed enough to warrant it.
          if (pillText !== lastPillText) {
            showScrollPill(pillText);
            lastPillText = pillText;
          }
        }
      }
    };

    let lastPillText = '';

    // Count of visible (kept) message rows after the last applyFilter call.
    // Day headers excluded. Exposed via getVisibleMsgCount() so the toolbar
    // doesn't need to re-walk allMsgRows independently.
    let visibleMsgCount = 0;

    const applyFilter = () => {
      const noTextFilter = !filterState ||
        (!filterState.queryRe && !filterState.senders && !filterState.chatUuids);
      if (noTextFilter && !starredOnly) {
        rows = allRows;
        // Count messages (excluding day headers) once for no-filter case too.
        let n = 0;
        for (let i = 0; i < allRows.length; i++) if (allRows[i].type === 'msg') n++;
        visibleMsgCount = n;
        return;
      }
      const out = [];
      let pendingDay = null;
      let n = 0;
      const q = filterState?.queryRe;
      const senders = filterState?.senders;
      const chats = filterState?.chatUuids;
      for (let i = 0; i < allRows.length; i++) {
        const r = allRows[i];
        if (r.type === 'day') { pendingDay = r; continue; }
        if (starredOnly && !starredIds.has(r.id)) continue;
        if (senders && !senders.has(r.sender)) continue;
        if (chats && !chats.has(r.chatUuid)) continue;
        if (q) {
          q.lastIndex = 0;
          if (!q.test(r.text) && !q.test(r.chatName)) continue;
        }
        if (pendingDay) { out.push(pendingDay); pendingDay = null; }
        out.push(r);
        n++;
      }
      rows = out;
      visibleMsgCount = n;
    };

    // ----- public API -----

    // Replace the entire dataset with an already-flat array of message rows
    // (shape: {chatUuid, chatName, sender, timestamp, text, messageUuid}).
    // Sorts + inserts day headers. Used by v34+ where rows are stored
    // pre-extracted in IndexedDB.
    const setFlatRows = (msgRows) => {
      const scrollRatio = totalHeight > 0 ? bodyEl.scrollTop / totalHeight : 0;
      allRows = buildRowsFromFlat(msgRows);
      rowIndicesByChat = indexRowsByChat(allRows);
      applyFilter();
      rebuildOffsets();
      rebuildDateRail();
      bodyEl.scrollTop = totalHeight * scrollRatio;
      for (const [, el] of mounted) { el.remove(); releaseRow(el); }
      mounted.clear();
      scheduleRender();
    };

    // Rebuild rows array from the full record set. Kept for back-compat with
    // any call-site still passing raw records (shouldn't exist in v34+).
    const setRecords = (records) => {
      const scrollRatio = totalHeight > 0 ? bodyEl.scrollTop / totalHeight : 0;
      allRows = flattenRecordsToRows(records);
      rowIndicesByChat = indexRowsByChat(allRows);
      applyFilter();
      rebuildOffsets();
      rebuildDateRail();
      bodyEl.scrollTop = totalHeight * scrollRatio;
      for (const [, el] of mounted) { el.remove(); releaseRow(el); }
      mounted.clear();
      scheduleRender();
    };

    // Change filter/search without re-fetching data. Re-applies filter in-place,
    // resets scroll to top (so user lands on first match), re-renders.
    const setFilter = (newFilter) => {
      filterState = newFilter;
      applyFilter();
      rebuildOffsets();
      rebuildDateRail();
      bodyEl.scrollTop = 0;
      for (const [, el] of mounted) { el.remove(); releaseRow(el); }
      mounted.clear();
      // Highlighting via <mark> is inline and doesn't affect layout/wrap,
      // so cached measured heights remain valid across filter changes.
      scheduleRender();
    };

    // Incremental update: replace one chat's messages without rebuilding the
    // entire flat list. We still rebuild offsets afterward because row indices
    // after the inserted chat may have shifted, but this avoids re-flattening
    // the entire record set every 5-chat fetch completion.
    //
    // NB: because messages from a single chat cluster by timestamp but not
    // strictly (chats can span days), naively "removing chat X's rows and
    // inserting its new messages in one spot" would produce a mis-ordered
    // list. Simpler correct behaviour: re-flatten. This is still O(total
    // messages) but only on chat-complete events (≤400 times total), not
    // on every render (which is where the old code died).
    const upsertRecord = (record, allRecordsGetter) => {
      setRecords(allRecordsGetter());
    };

    const destroy = () => {
      bodyEl.removeEventListener('scroll', onScroll);
      resizeObs.disconnect();
      // Fire-and-forget: persist any un-flushed measurements so they survive
      // the modal close. The dbPutBatch runs independently of the destroy().
      flushHeightWrites();
      for (const [, el] of mounted) el.remove();
      mounted.clear();
      freePool.length = 0;
      heightCache.clear();
      spacer.remove();
      stickyDay.remove();
      scrollPill.remove();
      dateRail.remove();
      clearTimeout(scrollPillFadeTimer);
    };

    // ----- wiring -----
    // Throttle: only schedule a render if scroll moved >= MIN_RERENDER_SCROLL
    // OR we're near the edge of the overscan buffer. Otherwise rAF is a no-op.
    let lastRenderScroll = 0;
    const onScroll = () => {
      const delta = Math.abs(bodyEl.scrollTop - lastRenderScroll);
      if (delta < MIN_RERENDER_SCROLL) return;  // skip — overscan covers it
      lastRenderScroll = bodyEl.scrollTop;
      scheduleRender();
    };
    bodyEl.addEventListener('scroll', onScroll, { passive: true });

    // Rerender on container resize so row widths recompute (affects wrap height).
    // Suppress the first fire (initial observation) — setRecords handles that.
    let resizeInitialFire = true;
    const resizeObs = new ResizeObserver(() => {
      if (resizeInitialFire) { resizeInitialFire = false; return; }
      // Width change invalidates all cached heights since text wraps differently
      heightCache.clear();
      rebuildOffsets();
      for (const [, el] of mounted) { el.remove(); releaseRow(el); }
      mounted.clear();
      scheduleRender();
    });
    resizeObs.observe(bodyEl);

    const getVisibleMsgCount = () => visibleMsgCount;

    // Find current selection index in `rows`; -1 if not found or none.
    const currentSelectedIdx = () => {
      if (!selectedRowId) return -1;
      for (let i = 0; i < rows.length; i++) if (rows[i].id === selectedRowId) return i;
      return -1;
    };

    // Scroll the row at idx into view if it's outside the current viewport.
    const scrollRowIntoView = (idx) => {
      if (idx < 0 || idx >= rows.length) return;
      const top = offsets[idx];
      const bottom = top + getHeight(rows[idx]);
      const viewTop = bodyEl.scrollTop;
      const viewBottom = viewTop + bodyEl.clientHeight;
      // Account for the sticky day header at top — pad a bit so selected
      // row isn't obscured when jumping up.
      const padTop = 60;
      if (top < viewTop + padTop) {
        bodyEl.scrollTop = Math.max(0, top - padTop);
      } else if (bottom > viewBottom) {
        bodyEl.scrollTop = bottom - bodyEl.clientHeight + 12;
      }
    };

    // Move selection by `delta` message rows (skipping day headers).
    // Wraps at ends (no cycling — stops at first/last).
    const moveSelection = (delta) => {
      if (rows.length === 0) return;
      let idx = currentSelectedIdx();
      if (idx < 0) {
        // No prior selection — start from the top-visible row
        const scrollTop = bodyEl.scrollTop;
        idx = indexForOffset(scrollTop);
        // Ensure idx points at a message row (skip leading day header)
        while (idx < rows.length && rows[idx].type !== 'msg') idx++;
        if (idx >= rows.length) return;
      } else {
        // Step in direction, skipping day headers
        const step = Math.sign(delta);
        const count = Math.abs(delta);
        for (let n = 0; n < count; n++) {
          let next = idx + step;
          while (next >= 0 && next < rows.length && rows[next].type !== 'msg') next += step;
          if (next < 0 || next >= rows.length) break;  // hit boundary, stop
          idx = next;
        }
      }
      selectedRowId = rows[idx].id;
      scrollRowIntoView(idx);
      scheduleRender();
    };

    const clearSelection = () => {
      if (selectedRowId === null) return;
      selectedRowId = null;
      scheduleRender();
    };

    // Returns the currently-selected row object (or null).
    const getSelectedRow = () => {
      const idx = currentSelectedIdx();
      return idx >= 0 ? rows[idx] : null;
    };

    // Toggle the starred-only filter. Re-applies filter, rebuilds offsets,
    // resets scroll. Same pattern as setFilter.
    const setStarredOnly = (v) => {
      starredOnly = !!v;
      applyFilter();
      rebuildOffsets();
      rebuildDateRail();
      bodyEl.scrollTop = 0;
      for (const [, el] of mounted) { el.remove(); releaseRow(el); }
      mounted.clear();
      scheduleRender();
    };

    // Lightweight: after starring/unstarring a row, re-sync visuals without
    // resetting scroll or rebuilding the whole filter. If starred-only is
    // active, we DO need to re-filter since the row may now drop/appear;
    // otherwise it's just a visual update via re-hydrate on next render.
    const notifyStarChanged = () => {
      if (starredOnly) {
        // Row may need to drop out of view — full refilter, but keep scroll.
        const scrollTop = bodyEl.scrollTop;
        applyFilter();
        rebuildOffsets();
        rebuildDateRail();
        bodyEl.scrollTop = Math.min(scrollTop, Math.max(0, totalHeight - bodyEl.clientHeight));
        for (const [, el] of mounted) { el.remove(); releaseRow(el); }
        mounted.clear();
      }
      scheduleRender();
    };

    return { setRecords, setFlatRows, setFilter, upsertRecord, destroy, getVisibleMsgCount,
             moveSelection, clearSelection, getSelectedRow, setStarredOnly, notifyStarChanged };
  };

  // Flatten records into a single ordered list of rows (day headers + messages).
  // One allocation pass; no re-sorts unless the caller changes order preference.
  function flattenRecordsToRows(records) {
    const msgs = [];
    for (const r of records) {
      if (!r || !r.content) continue;
      const list = r.content.chat_messages || r.content.messages || r.content.data || [];
      for (const m of list) {
        const sender = normalizeSender(m.sender || m.role);
        if (sender === 'unknown') continue;
        const text = extractMessageText(m);
        if (!text || !text.trim()) continue;
        msgs.push({
          chatUuid: r.uuid,
          chatName: r.name || 'Untitled',
          sender,
          timestamp: m.created_at || m.timestamp || r.created_at,
          text,
          messageUuid: m.uuid || m.id,
        });
      }
    }
    // Sort once, in place. Use pre-computed _ts if present, else parse.
    msgs.sort((a, b) => {
      const da = a._ts ?? (a._ts = a.timestamp ? new Date(a.timestamp).getTime() : 0);
      const db = b._ts ?? (b._ts = b.timestamp ? new Date(b.timestamp).getTime() : 0);
      return OLDEST_FIRST ? da - db : db - da;
    });

    const today = new Date();
    const yest = new Date(Date.now() - 86400000);
    const sameDay = (a, b) =>
      a.getFullYear() === b.getFullYear() && a.getMonth() === b.getMonth() && a.getDate() === b.getDate();
    const dayLabel = (iso) => {
      const d = new Date(iso);
      if (sameDay(d, today)) return 'Today';
      if (sameDay(d, yest))  return 'Yesterday';
      return `${DATE_FORMAT(iso)}, ${d.getFullYear()}`;
    };

    const rows = [];
    let lastDay = null;
    for (const m of msgs) {
      const label = dayLabel(m.timestamp);
      if (label !== lastDay) {
        rows.push({ type: 'day', id: `d:${label}`, label });
        lastDay = label;
      }
      const id = m.messageUuid ? `m:${m.messageUuid}` : `m:${m.chatUuid}:${rows.length}`;
      rows.push({ type: 'msg', id, ...m });
    }
    return rows;
  }

  // Given an already-flat array of message rows (from chat_rows store),
  // sort and insert day headers. Used by v34+ load path.
  function buildRowsFromFlat(msgs) {
    msgs.sort((a, b) => {
      // Prefer pre-computed _ts; lazily populate for legacy rows missing it.
      const da = a._ts ?? (a._ts = a.timestamp ? new Date(a.timestamp).getTime() : 0);
      const db = b._ts ?? (b._ts = b.timestamp ? new Date(b.timestamp).getTime() : 0);
      return OLDEST_FIRST ? da - db : db - da;
    });

    const today = new Date();
    const yest = new Date(Date.now() - 86400000);
    const sameDay = (a, b) =>
      a.getFullYear() === b.getFullYear() && a.getMonth() === b.getMonth() && a.getDate() === b.getDate();
    const dayLabel = (iso) => {
      const d = new Date(iso);
      if (sameDay(d, today)) return 'Today';
      if (sameDay(d, yest))  return 'Yesterday';
      return `${DATE_FORMAT(iso)}, ${d.getFullYear()}`;
    };

    const rows = [];
    let lastDay = null;
    for (const m of msgs) {
      const label = dayLabel(m.timestamp);
      if (label !== lastDay) {
        rows.push({ type: 'day', id: `d:${label}`, label });
        lastDay = label;
      }
      const id = m.messageUuid ? `m:${m.messageUuid}` : `m:${m.chatUuid}:${rows.length}`;
      rows.push({ type: 'msg', id, ...m });
    }
    return rows;
  }

  function indexRowsByChat(rows) {
    const map = new Map();
    for (let i = 0; i < rows.length; i++) {
      const r = rows[i];
      if (r.type !== 'msg') continue;
      let arr = map.get(r.chatUuid);
      if (!arr) { arr = []; map.set(r.chatUuid, arr); }
      arr.push(i);
    }
    return map;
  }

  // ============================================================
  //  BUTTON + HOTKEY
  // ============================================================
  // Reference to the button so background prefetch can drive its progress ring.
  let superchatBtn = null;

  function injectSuperchatButton() {
    if (!ENABLE_SUPERCHAT) return;
    if (document.querySelector('.sbc-sc-btn')) return;
    injectStyles();
    const btn = document.createElement('button');
    btn.className = 'sbc-sc-btn';
    btn.title = 'Open Superchat — message-level view across all chats (Ctrl+Shift+T)';
    btn.innerHTML = `
      <svg class="sbc-sc-btn-ring hidden" viewBox="0 0 14 14">
        <circle class="track" cx="7" cy="7" r="5.5"></circle>
        <circle class="fill"  cx="7" cy="7" r="5.5"></circle>
      </svg>
      <span class="sbc-sc-btn-dot"></span>
      <span class="sbc-sc-btn-label">Superchat</span>
    `;
    btn.addEventListener('click', openSuperchat);
    document.body.appendChild(btn);
    superchatBtn = btn;
  }

  // Called by background prefetch: progress is 0..1, null to hide ring.
  function setSuperchatButtonProgress(progress) {
    if (!superchatBtn) return;
    const ring = superchatBtn.querySelector('.sbc-sc-btn-ring');
    const dot = superchatBtn.querySelector('.sbc-sc-btn-dot');
    const fill = ring?.querySelector('.fill');
    if (progress == null) {
      ring.classList.add('hidden');
      dot.classList.remove('hidden');
      return;
    }
    ring.classList.remove('hidden');
    dot.classList.add('hidden');
    const clamped = Math.max(0, Math.min(1, progress));
    superchatBtn.style.setProperty('--sbc-progress', clamped);
    // Also set directly in case the CSS calc pipeline doesn't animate reliably
    if (fill) fill.setAttribute('stroke-dashoffset', (34.56 * (1 - clamped)).toFixed(2));
  }
  const whenReady = (fn) => {
    if (document.body) fn();
    else document.addEventListener('DOMContentLoaded', fn, { once: true });
  };
  whenReady(injectSuperchatButton);

  document.addEventListener('keydown', (e) => {
    if (ENABLE_SUPERCHAT && SUPERCHAT_HOTKEY(e)) { e.preventDefault(); openSuperchat(); }
  });

  // ============================================================
  //  PATCHED FETCH
  // ============================================================
  window.fetch = async function patchedFetch(...args) {
    const url = getURL(args[0]);
    if (!cachedOrgId && typeof url === 'string') setOrgIdFrom('fetch', extractOrgId(url));
    if (!isConversationListURL(url)) return originalFetch.apply(this, args);

    await ensureSidebarMeta();

    const init = extractInit(args);
    // If this is a paginated request (has a cursor-like param), don't
    // override the limit — Claude's infinite-scroll relies on the limit it
    // asked for matching the cursor's expected page size. Overriding breaks
    // pagination state and the user ends up seeing only one page.
    const urlObj = new URL(url, location.origin);
    const hasCursor = urlObj.searchParams.has('before') ||
                      urlObj.searchParams.has('after') ||
                      urlObj.searchParams.has('cursor') ||
                      urlObj.searchParams.has('page') ||
                      urlObj.searchParams.has('offset');
    let targetURL;
    if (hasCursor) {
      targetURL = url;  // pass through untouched
    } else {
      const limit = await ensureLimit(url, init);
      // Fall back to 500 if probe returned null — better than letting
      // Claude's default (often 50) through, which breaks the sidebar.
      const effectiveLimit = limit || 500;
      targetURL = withLimit(url, effectiveLimit);
    }

    const resp = await originalFetch(targetURL, init);
    if (!resp.ok) return resp;

    try {
      const data = await resp.clone().json();
      const { list, key } = extractList(data);
      if (!list) return resp;

      // In 'created' mode: sort by created_at AND rewrite updated_at so Claude's
      // UI re-sort (which uses updated_at) produces the order we want.
      // In 'activity' mode: don't sort, don't rewrite — let Claude's native
      // updated_at sort take effect. We still run transformItems to populate
      // sidebarMeta so date badges still render.
      const orderedList = sortMode === 'created' ? sortByCreated(list) : list;
      const sorted = transformItems(orderedList);
      const body = Array.isArray(data)
        ? JSON.stringify(sorted)
        : JSON.stringify({ ...data, [key]: sorted });

      const label = urlObj.searchParams.get('starred') === 'true' ? 'starred' : 'chats';
      LOG(`sorted ${sorted.length} ${label} (${sortMode} mode${hasCursor ? ', paginated' : ''})`);
      toast.show(`${sorted.length} chats • ${sortMode}`, true);
      scheduleSidebarDecorate();

      return new Response(body, { status: resp.status, statusText: resp.statusText, headers: resp.headers });
    } catch (err) {
      LOG('passthrough (error):', err);
      return resp;
    }
  };

  LOG(`installed v43.9 — split rail gaps year=22 month=12 (${sortMode} mode, ${themeMode} theme)`);
})();
