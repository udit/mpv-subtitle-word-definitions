--[[
  sublookup.lua - click a word in the subtitles to see its definition.

  How it works
    * Hides mpv's native subtitle and redraws the same text as an OSD overlay.
    * Measures every word's pixel position with osd-overlay's compute_bounds.
    * Highlights the hovered word; click it to look it up (dictionaryapi.dev via curl).
    * The mouse-click binding is only active while hovering a word, so uosc's own
      mouse handling (timeline, controls, menus, click-to-pause) is never blocked.

  Install:  put this file in  <mpv config>/scripts/sublookup.lua
  Default key: Ctrl+l toggles interactive subtitles (script-binding sublookup/toggle)
  Esc closes the popup. Config: <mpv config>/script-opts/sublookup.conf
]]

local mp = require "mp"
local utils = require "mp.utils"
local options = require "mp.options"
local msg = require "mp.msg"
local is_windows = package.config:sub(1, 1) == "\\"

local opts = {
    curl_extra = "",                   -- extra curl args, e.g. "--proxy http://host:port" or "-k"
    provider = "auto",                 -- "auto" (dictionaryapi, then Wiktionary), "dictionaryapi", "wiktionary"
    wikt_host = "en.wiktionary.org",   -- e.g. fr.wiktionary.org for French-language definitions
    lang = "en",                       -- dictionaryapi.dev: en, es, fr, de, it, ru, ja, ko, pt-BR, ar, tr, hi
    api_url = "https://api.dictionaryapi.dev/api/v2/entries/%s/%s",
    curl_path = "curl",
    pause_on_lookup = true,
    enabled_on_start = false,
    max_meanings = 3,                  -- parts of speech shown
    defs_per_meaning = 2,
    wrap_chars = 48,
    popup_font = "",                   -- empty = same as sub-font
    popup_font_size = 20,              -- at 720p, scaled with window height
    hover_color = "FFD54A",            -- RGB hex
    accent_color = "FFD54A",
    popup_bg = "1B1B1F",
    popup_fg = "FFFFFF",
}
options.read_options(opts, "sublookup")

-- ---------------------------------------------------------------- state
local enabled = false
local ours_visible = true   -- toggled by mpv's own subtitle toggle (v) while enabled
local saved_sub_visibility = true
local sub_text = ""
local layout = nil          -- built from sub_text
local hover = nil           -- {l = line index, w = word index}
local anchor = nil          -- where the popup attaches
local popup_active = false
local paused_by_us = false
local click_bound = false
local req_id = 0
local cache = {}
local last_W, last_H = 0, 0
local pstate = nil          -- popup geometry + hit regions (overlay popup only)
local phover = nil          -- hovered popup item (language chip / picker cell)
local current_word = nil
local history = {}        -- words visited via clicks inside the popup (for Back)

local sub_ov = mp.create_osd_overlay("ass-events")
local pop_ov = mp.create_osd_overlay("ass-events")
pop_ov.z = 10

-- ---------------------------------------------------------------- languages
-- Language of the word being looked up (Wiktionary/dictionaryapi code)
local LANGS = {
    { "en", "English" }, { "es", "Spanish" }, { "fr", "French" }, { "de", "German" },
    { "it", "Italian" }, { "pt", "Portuguese" }, { "nl", "Dutch" }, { "sv", "Swedish" },
    { "pl", "Polish" }, { "ru", "Russian" }, { "tr", "Turkish" }, { "ar", "Arabic" },
    { "hi", "Hindi" }, { "ja", "Japanese" }, { "ko", "Korean" }, { "zh", "Chinese" },
    { "la", "Latin" },
}

local function lang_name(code)
    for _, l in ipairs(LANGS) do
        if l[1] == code then return l[2] end
    end
    return code
end

-- remembered across sessions in <mpv config>/sublookup_lang.txt
local lang_path = mp.command_native({ "expand-path", "~~/sublookup_lang.txt" })

local function load_lang()
    local f = lang_path and io.open(lang_path, "r")
    if not f then return end
    local c = f:read("*l")
    f:close()
    if c and c:match("^[%a%-]+$") then opts.lang = c end
end

local function save_lang(code)
    local f = lang_path and io.open(lang_path, "w")
    if f then
        f:write(code, "\n")
        f:close()
    else
        msg.warn("could not save language to " .. tostring(lang_path))
    end
end

load_lang()

-- ---------------------------------------------------------------- helpers
local function rgb(hex)
    hex = tostring(hex):gsub("^#", "")
    hex = hex:sub(1, 6)
    -- ASS wants BGR
    return hex:sub(5, 6) .. hex:sub(3, 4) .. hex:sub(1, 2)
end

local function mp_color(s) -- mpv "#AARRGGBB" or "#RRGGBB" -> "RRGGBB"
    s = tostring(s):gsub("^#", "")
    if #s == 8 then s = s:sub(3) end
    return s
end

local function esc(s)
    s = s:gsub("\\", "\\\239\187\191")
    s = s:gsub("{", "\\{")
    s = s:gsub("^ ", "\\h")
    return s
end

local function ulen(s)
    return select(2, s:gsub("[^\128-\191]", ""))
end

local function urlenc(s)
    return (s:gsub("[^%w%-_%.~]", function(c) return string.format("%%%02X", c:byte()) end))
end

local punct_mb = { "“", "”", "‘", "’", "«", "»", "…", "—", "–", "¿", "¡", "„", "。", "、" }
local function clean(tok)
    local s = tok
    local changed = true
    while changed do
        changed = false
        local t = s:gsub("^%p+", ""):gsub("%p+$", "")
        for _, mb in ipairs(punct_mb) do
            if t:sub(1, #mb) == mb then t = t:sub(#mb + 1) end
            if #t >= #mb and t:sub(-#mb) == mb then t = t:sub(1, #t - #mb) end
        end
        if t ~= s then s = t; changed = true end
    end
    return s
end

local function wrap(text, width)
    local out, line = {}, ""
    for word in text:gmatch("%S+") do
        if line ~= "" and ulen(line) + ulen(word) + 1 > width then
            out[#out + 1] = line
            line = word
        else
            line = (line == "") and word or (line .. " " .. word)
        end
    end
    if line ~= "" then out[#out + 1] = line end
    return out
end

local function osd_dims()
    local d = mp.get_property_native("osd-dimensions")
    if d and d.w and d.w > 0 and d.h and d.h > 0 then return d.w, d.h end
    return 1280, 720
end

local function sub_metrics()
    local W, H = osd_dims()
    local sc = H / 720
    local m = { W = W, H = H, sc = sc }
    m.font = mp.get_property("sub-font") or "sans-serif"
    m.fs = mp.get_property_number("sub-font-size", 55) * mp.get_property_number("sub-scale", 1) * sc
    m.bold = mp.get_property_bool("sub-bold", false) and 1 or 0
    m.bord = mp.get_property_number("sub-border-size", 3) * sc
    m.shad = mp.get_property_number("sub-shadow-offset", 0) * sc
    m.color = mp_color(mp.get_property("sub-color", "#FFFFFF"))
    m.bcolor = mp_color(mp.get_property("sub-border-color", "#000000"))
    m.bottom = H * mp.get_property_number("sub-pos", 100) / 100
        - mp.get_property_number("sub-margin-y", 22) * sc
    return m
end

-- Measure ASS text with one reusable hidden overlay: returns x0, y0, x1, y1 (or nil)
local meas_ov = mp.create_osd_overlay("ass-events")
meas_ov.compute_bounds = true
meas_ov.hidden = true
local meas_hidden_ok = true

local function measure_done() meas_ov:remove() end

local function measure(m, data)
    meas_ov.res_x, meas_ov.res_y = m.W, m.H
    meas_ov.data = data
    local r
    if meas_hidden_ok then
        meas_ov.hidden = true
        r = meas_ov:update()
    end
    if not (r and r.x1) then
        -- some builds only report bounds for visible overlays; show it for one update
        meas_ov.hidden = false
        r = meas_ov:update()
        meas_ov:remove()
        meas_ov.hidden = true
        if r and r.x1 then meas_hidden_ok = false end
    end
    if r and r.x1 then return r.x0, r.y0, r.x1, r.y1 end
    return nil
end

-- ---------------------------------------------------------------- layout
local function build_layout()
    layout, hover = nil, nil
    if sub_text == "" then return end

    local m = sub_metrics()
    local base = string.format("{\\an7\\pos(0,0)\\fn%s\\fs%.1f\\bord0\\shad0\\b%d}", m.font, m.fs, m.bold)

    local _, _, _, h1 = measure(m, base .. "Hg")
    if not h1 then
        mp.osd_message("sublookup: this mpv build can't measure OSD overlays (update mpv)", 5)
        return
    end
    local _, _, _, h2 = measure(m, base .. "Hg\\NHg")
    local lh = (h2 and h2 > h1) and (h2 - h1) or m.fs * 1.2

    local _, _, sa = measure(m, base .. "A A")
    local _, _, sb = measure(m, base .. "AA")
    local sp = (sa and sb and sa > sb) and (sa - sb) or m.fs * 0.3

    local lines = {}
    for raw in (sub_text .. "\n"):gmatch("(.-)\n") do
        local toks = {}
        for t in raw:gmatch("%S+") do toks[#toks + 1] = t end
        if #toks > 0 then lines[#lines + 1] = { toks = toks, words = {} } end
    end
    if #lines == 0 then return end

    local N = #lines
    for k, line in ipairs(lines) do
        local toks, prev = line.toks, 0
        for i, tok in ipairs(toks) do
            local _, _, e = measure(m, base .. esc(table.concat(toks, " ", 1, i)))
            e = e or (prev + ulen(tok) * m.fs * 0.5 + sp)
            local l = (i == 1) and 0 or (prev + sp / 2)
            local r = (i == #toks) and e or (e + sp / 2)
            line.words[i] = { text = tok, clean = clean(tok), l = l, r = r }
            prev = e
        end
        line.w = prev
        line.xoff = (m.W - prev) / 2
        line.y = m.bottom - (N - k + 1) * lh
    end

    layout = { m = m, lh = lh, lines = lines }
    last_W, last_H = m.W, m.H
    measure_done()
end

local function render()
    if not enabled then return end
    if not layout or not ours_visible then sub_ov:remove(); return end
    local m = layout.m
    local out = {}
    for li, line in ipairs(layout.lines) do
        local parts = {}
        for wi, w in ipairs(line.words) do
            local t = esc(w.text)
            if hover and hover.l == li and hover.w == wi then
                t = string.format("{\\1c&H%s&\\u1}%s{\\1c&H%s&\\u0}", rgb(opts.hover_color), t, m.color and rgb(m.color) or "FFFFFF")
            end
            parts[#parts + 1] = t
        end
        out[#out + 1] = string.format(
            "{\\an7\\pos(%.1f,%.1f)\\fn%s\\fs%.1f\\b%d\\bord%.1f\\shad%.1f\\1c&H%s&\\3c&H%s&\\4c&H000000&}%s",
            line.xoff, line.y, m.font, m.fs, m.bold, m.bord, m.shad,
            rgb(m.color), rgb(m.bcolor), table.concat(parts, " "))
    end
    sub_ov.res_x, sub_ov.res_y = m.W, m.H
    sub_ov.data = table.concat(out, "\n")
    sub_ov:update()
end

local function hit_test(mx, my)
    if not layout then return nil end
    local pad = layout.lh * 0.1
    for li, line in ipairs(layout.lines) do
        if my >= line.y - pad and my <= line.y + layout.lh + pad then
            for wi, w in ipairs(line.words) do
                if mx >= line.xoff + w.l and mx < line.xoff + w.r then return li, wi end
            end
        end
    end
    return nil
end

-- ---------------------------------------------------------------- dictionary
local function candidates(word)
    local lw = word:lower()
    local c, seen = {}, {}
    local function add(w)
        if #w > 1 and not seen[w] then seen[w] = true; c[#c + 1] = w end
    end
    add(lw)
    if word ~= lw then add(word) end
    if opts.lang == "en" then
        add((lw:gsub("['’]s$", "")))
        add((lw:gsub("ies$", "y")))
        add((lw:gsub("es$", "")))
        add((lw:gsub("s$", "")))
        add((lw:gsub("ed$", "")))
        add((lw:gsub("ed$", "e")))
        add((lw:gsub("ing$", "")))
        add((lw:gsub("ing$", "e")))
        add((lw:gsub("ly$", "")))
    end
    return c
end

local function run_curl(url, cb, timeout)
    local args = { opts.curl_path, "-sS", "-L", "--max-time", tostring(timeout or 10), "-A", "mpv-sublookup" }
    if is_windows then args[#args + 1] = "--ssl-no-revoke" end
    for a in opts.curl_extra:gmatch("%S+") do args[#args + 1] = a end
    args[#args + 1] = url
    msg.info("running: " .. table.concat(args, " "))
    mp.command_native_async({
        name = "subprocess",
        args = args,
        capture_stdout = true,
        capture_stderr = true,
        playback_only = false,
    }, function(success, res, err)
        if not success or not res or res.status ~= 0 then
            local detail = "curl failed"
            if res then
                local es = (res.stderr or ""):gsub("%s+$", "")
                detail = string.format("exit %s %s %s", tostring(res.status),
                    tostring(res.error_string or ""), es)
            elseif err then
                detail = tostring(err)
            end
            msg.error(detail)
            return cb(nil, "network", detail)
        end
        local j = utils.parse_json(res.stdout or "")
        if type(j) == "table" then return cb(j) end
        cb(nil, "notfound")
    end)
end

local dapi_down = false

local function strip_html(s)
    s = s:gsub("<[^>]*>", "")
    local ents = { ["&nbsp;"] = " ", ["&lt;"] = "<", ["&gt;"] = ">", ["&quot;"] = '"',
                   ["&#39;"] = "'", ["&#160;"] = " ", ["&amp;"] = "&" }
    for k, v in pairs(ents) do s = s:gsub(k, v) end
    return (s:gsub("%s+", " "):gsub("^ ", ""):gsub(" $", ""))
end

local function fetch_dapi(word, cb)
    local code = (opts.lang == "pt") and "pt-BR" or opts.lang
    local url = string.format(opts.api_url, code, urlenc(word))
    run_curl(url, function(j, err, detail)
        if j and j[1] then return cb(j) end
        cb(nil, err or "notfound", detail)
    end, 5)
end

-- Wiktionary result is normalised into dictionaryapi.dev's shape so collect() works on both
local function fetch_wikt(word, cb)
    local url = string.format("https://%s/api/rest_v1/page/definition/%s", opts.wikt_host, urlenc(word))
    run_curl(url, function(j, err, detail)
        if not j then return cb(nil, err, detail) end
        local entries = j[opts.lang:match("^[^-]+")]
        if type(entries) ~= "table" then return cb(nil, "notfound") end
        local meanings = {}
        for _, e in ipairs(entries) do
            local defs = {}
            for _, d in ipairs(e.definitions or {}) do
                local t = strip_html(d.definition or "")
                if t ~= "" then defs[#defs + 1] = { definition = t } end
            end
            if #defs > 0 then
                meanings[#meanings + 1] = { partOfSpeech = e.partOfSpeech or "", definitions = defs }
            end
        end
        if #meanings == 0 then return cb(nil, "notfound") end
        cb({ { meanings = meanings } })
    end, 8)
end

local function fetch(word, cb)
    if opts.provider == "wiktionary" or (opts.provider == "auto" and dapi_down) then
        return fetch_wikt(word, cb)
    end
    fetch_dapi(word, function(data, err, detail)
        if data then return cb(data) end
        if opts.provider == "auto" then
            if err == "network" then
                dapi_down = true
                msg.warn("dictionaryapi.dev unreachable, switching to Wiktionary")
            end
            return fetch_wikt(word, cb)
        end
        cb(nil, err, detail)
    end)
end

local function lookup_word(word, done)
    local lang = opts.lang
    local cands = candidates(word)
    local function try(i)
        if lang ~= opts.lang then return end -- language changed mid-lookup
        if i > #cands then return done(nil, nil, "notfound") end
        local c = cands[i]
        local key = lang .. ":" .. c
        if cache[key] ~= nil then
            if cache[key] then return done(cache[key], c) end
            return try(i + 1)
        end
        fetch(c, function(data, err, detail)
            if lang ~= opts.lang then return end
            if err == "network" then return done(nil, nil, "network", detail) end
            cache[key] = data or false
            if data then done(data, c) else try(i + 1) end
        end)
    end
    try(1)
end

local function collect(data)
    local info = { phon = nil, groups = {} }
    for _, e in ipairs(data) do
        if not info.phon then
            local ph = e.phonetic
            if not ph or ph == "" then
                for _, p in ipairs(e.phonetics or {}) do
                    if p.text and p.text ~= "" then ph = p.text; break end
                end
            end
            if ph and ph ~= "" then info.phon = ph end
        end
        for _, mn in ipairs(e.meanings or {}) do
            if #info.groups >= opts.max_meanings then break end
            local defs = {}
            for _, d in ipairs(mn.definitions or {}) do
                if #defs >= opts.defs_per_meaning then break end
                if d.definition then defs[#defs + 1] = d.definition end
            end
            if #defs > 0 then
                info.groups[#info.groups + 1] = { pos = mn.partOfSpeech or "", defs = defs }
            end
        end
    end
    return info
end

-- ---------------------------------------------------------------- popup
local function dismiss(resume)
    req_id = req_id + 1
    popup_active = false
    pop_ov:remove()
    pstate, phover, history = nil, nil, {}
    if not hover then
        click_bound = false
        mp.remove_key_binding("sublookup-click")
    end
    mp.remove_key_binding("sublookup-close")
    if paused_by_us then
        paused_by_us = false
        if resume then mp.set_property_bool("pause", false) end
    end
end

local function box(x, y, w, h, fill, border, bwidth, alpha)
    return string.format(
        "{\\an7\\pos(%.1f,%.1f)\\bord%.1f\\3c&H%s&\\shad0\\1c&H%s&\\1a&H%s&\\p1}m 0 0 l %.1f 0 %.1f %.1f 0 %.1f{\\p0}",
        x, y, bwidth, border, fill, alpha, w, w, h, h)
end

local function label(x, y, font, fs, color, s)
    return string.format("{\\an7\\pos(%.1f,%.1f)\\fn%s\\fs%.1f\\bord0\\shad0\\b0\\1c&H%s&}%s",
        x, y, font, fs, color, s)
end

local function paint_popup()
    if not pstate then return end
    local g, m = pstate.geom, anchor.m
    local fs = g.fs
    local fg, bg, acc = rgb(opts.popup_fg), rgb(opts.popup_bg), rgb(opts.accent_color)
    local hov = rgb(opts.hover_color)
    local chip_bg = rgb("45454F")
    local out, items = {}, {}

    out[#out + 1] = box(g.bx, g.by, g.bw, g.bh, bg, acc, 2 * m.sc, "10")

    -- text rows; words in definitions are clickable
    for k, r in ipairs(g.rows) do
        local y = g.by + g.pad + (k - 1) * g.lh
        local x = g.bx + g.pad + r.x
        if r.kind == "plain" then
            out[#out + 1] = label(x, y, g.font, fs, fg, r.ass)
        else
            local parts = {}
            for i, t in ipairs(r.toks) do
                local text = esc(t.text)
                if t.clickable then
                    local key = "w:" .. k .. ":" .. i
                    items[#items + 1] = { key = key, word = t.clean,
                        x0 = x + t.l, x1 = x + t.r, y0 = y, y1 = y + g.lh }
                    if phover and phover.key == key then
                        text = string.format("{\\1c&H%s&\\u1}%s{\\1c&H%s&\\u0}", hov, text, fg)
                    end
                end
                parts[#parts + 1] = text
            end
            out[#out + 1] = label(x, y, g.font, fs, fg, table.concat(parts, " "))
        end
    end

    local function button(b, key)
        local hot = phover and phover.key == key
        out[#out + 1] = box(b.x, b.y, b.w, b.h, hot and acc or chip_bg, acc, m.sc, "00")
        out[#out + 1] = label(b.x + fs * 0.5, b.y + (b.h - fs * 1.2) / 2, g.font, fs,
            hot and bg or fg, b.text)
        items[#items + 1] = { key = key, x0 = b.x, y0 = b.y, x1 = b.x + b.w, y1 = b.y + b.h }
    end
    button(g.chip, "chip")
    if g.back then button(g.back, "back") end

    -- opened language list
    if pstate.picker then
        local c = g.chip
        local cols = 3
        local rows = math.ceil(#LANGS / cols)
        local ch, pp = fs * 1.6, fs * 0.4
        local pw, ph = cols * g.cell_w + 2 * pp, rows * ch + 2 * pp
        local px = math.max(10, math.min(c.x, m.W - pw - 10))
        local py = c.y - 8 * m.sc - ph
        if py < 10 then py = math.min(c.y + c.h + 8 * m.sc, m.H - ph - 10) end
        py = math.max(10, py)
        out[#out + 1] = box(px, py, pw, ph, bg, acc, 2 * m.sc, "00")
        for idx, l in ipairs(LANGS) do
            local col, row = (idx - 1) % cols, math.floor((idx - 1) / cols)
            local cx, cy = px + pp + col * g.cell_w, py + pp + row * ch
            local key = "lang:" .. l[1]
            local hot = phover and phover.key == key
            if hot then out[#out + 1] = box(cx, cy, g.cell_w, ch, acc, acc, 0, "00") end
            local color = hot and bg or ((l[1] == opts.lang) and acc or fg)
            out[#out + 1] = label(cx + fs * 0.3, cy + (ch - fs * 1.2) / 2, g.font, fs, color, esc(l[2]))
            items[#items + 1] = { key = key, code = l[1], x0 = cx, y0 = cy, x1 = cx + g.cell_w, y1 = cy + ch }
        end
    end

    pstate.items = items
    pop_ov.res_x, pop_ov.res_y = m.W, m.H
    pop_ov.data = table.concat(out, "\n")
    pop_ov:update()
end

local function plain_ass(r, acc, fg)
    if r.kind == "head" then
        local t = string.format("{\\b1\\1c&H%s&}%s{\\b0\\1c&H%s&}", acc, esc(r.word), fg)
        if r.used and r.used ~= r.word:lower() then
            t = t .. string.format("{\\i1}  → %s{\\i0}", esc(r.used))
        end
        if r.phon then t = t .. "   " .. esc(r.phon) end
        return t
    elseif r.kind == "pos" then
        return string.format("{\\i1\\1c&H%s&}%s{\\i0\\1c&H%s&}", acc, esc(r.text), fg)
    end
    return "{\\i1}" .. esc(r.text) .. "{\\i0}"
end

-- rows: { kind = "head" | "pos" | "def" | "msg", ... }; every row is one line
local function draw_popup(rows)
    local m = anchor.m
    local fs = opts.popup_font_size * m.sc
    local font = (opts.popup_font ~= "") and opts.popup_font or m.font
    local pad = fs * 0.6
    local fg, acc = rgb(opts.popup_fg), rgb(opts.accent_color)
    local base = string.format("{\\an7\\pos(0,0)\\fn%s\\fs%.1f\\bord0\\shad0\\b0}", font, fs)

    local _, _, _, h1 = measure(m, base .. "Hg")
    local _, _, _, h2 = measure(m, base .. "Hg\\NHg")
    local lh = (h1 and h2 and h2 > h1) and (h2 - h1) or fs * 1.25
    local _, _, sa = measure(m, base .. "A A")
    local _, _, sb = measure(m, base .. "AA")
    local sp = (sa and sb and sa > sb) and (sa - sb) or fs * 0.3

    local indent = fs * 1.4
    local maxw = 0
    local out_rows = {}
    for k, r in ipairs(rows) do
        local x = r.indent and indent or 0
        if r.kind == "def" then
            local toks = {}
            for t in r.text:gmatch("%S+") do toks[#toks + 1] = t end
            local lt, prev = {}, 0
            for i, t in ipairs(toks) do
                local _, _, e = measure(m, base .. esc(table.concat(toks, " ", 1, i)))
                e = e or (prev + ulen(t) * fs * 0.5 + sp)
                local c = clean(t)
                lt[i] = {
                    text = t, clean = c,
                    l = (i == 1) and 0 or (prev + sp / 2),
                    r = (i == #toks) and e or (e + sp / 2),
                    clickable = c ~= "" and not c:match("^[%d%p]+$"),
                }
                prev = e
            end
            maxw = math.max(maxw, x + prev)
            out_rows[k] = { kind = "def", x = x, toks = lt }
        else
            local ass = plain_ass(r, acc, fg)
            local _, _, e = measure(m, base .. ass)
            maxw = math.max(maxw, x + (e or ulen(r.text or r.word or "") * fs * 0.55))
            out_rows[k] = { kind = "plain", x = x, ass = ass }
        end
    end
    measure_done()

    local chip_text = lang_name(opts.lang) .. " ▾"
    local chip_w = ulen(chip_text) * fs * 0.55 + fs
    local chip_h, gap = fs * 1.6, fs * 0.5
    local back_text = "◂ Back"
    local back_w = ulen(back_text) * fs * 0.55 + fs
    local has_back = #history > 0
    local btn_w = chip_w + (has_back and (gap + back_w) or 0)

    local maxc = 0
    for _, l in ipairs(LANGS) do maxc = math.max(maxc, ulen(l[2])) end

    local th = #rows * lh
    local bw = math.max(maxw, btn_w) + 2 * pad
    local bh = th + gap + chip_h + 2 * pad
    local bx = math.max(10, math.min(anchor.cx - bw / 2, m.W - bw - 10))
    local by = anchor.top - 14 * m.sc - bh
    if by < 10 then
        by = math.max(10, math.min(anchor.bottom + 14 * m.sc, m.H - bh - 10))
    end

    local btn_y = by + pad + th + gap
    pstate = {
        picker = false,
        geom = {
            fs = fs, font = font, pad = pad, lh = lh, rows = out_rows,
            bx = bx, by = by, bw = bw, bh = bh,
            cell_w = maxc * fs * 0.55 + fs * 0.6,
            chip = { x = bx + pad, y = btn_y, w = chip_w, h = chip_h, text = chip_text },
            back = has_back and { x = bx + pad + chip_w + gap, y = btn_y, w = back_w, h = chip_h, text = back_text } or nil,
        },
    }
    paint_popup()
end

local function popup_rows(word, used, info)
    local rows = { { kind = "head", word = word, used = used, phon = info.phon } }
    for _, g in ipairs(info.groups) do
        rows[#rows + 1] = { kind = "pos", text = g.pos }
        for i, d in ipairs(g.defs) do
            for k, s in ipairs(wrap(string.format("%d. %s", i, d), opts.wrap_chars)) do
                rows[#rows + 1] = { kind = "def", text = s, indent = (k > 1) }
            end
        end
    end
    return rows
end

local function show_message(text)
    draw_popup({ { kind = "msg", text = text } })
end

local function start_lookup(word)
    current_word = word
    phover = nil
    popup_active = true
    mp.add_forced_key_binding("ESC", "sublookup-close", function() dismiss(true) end)
    show_message("Looking up…")

    req_id = req_id + 1
    local my = req_id
    lookup_word(word, function(data, used, err, detail)
        if my ~= req_id or not popup_active then return end
        if not data then
            if err == "network" then
                local d = (detail or ""):gsub("%s+", " ")
                show_message("Lookup failed: " .. d:sub(1, 120))
            else
                show_message("No definition found for “" .. word .. "” (" .. lang_name(opts.lang) .. ")")
            end
            return
        end
        local info = collect(data)
        if #info.groups == 0 then
            show_message("No definition found for “" .. word .. "” (" .. lang_name(opts.lang) .. ")")
        else
            draw_popup(popup_rows(word, used, info))
        end
    end)
end

local function do_lookup(li, wi)
    local line = layout.lines[li]
    local w = line.words[wi]
    local word = w.clean
    if word == "" then return end

    anchor = {
        cx = line.xoff + (w.l + w.r) / 2,
        top = layout.lines[1].y,
        bottom = layout.lines[#layout.lines].y + layout.lh,
        m = layout.m,
    }

    if opts.pause_on_lookup and not mp.get_property_bool("pause") then
        mp.set_property_bool("pause", true)
        paused_by_us = true
    end
    history = {}
    start_lookup(word)
end

local function set_language(code)
    if not code or code == "" then return end
    if code == opts.lang then
        if pstate and pstate.picker then
            pstate.picker = false
            paint_popup()
        end
        return
    end
    opts.lang = code
    save_lang(code)
    if popup_active and current_word then
        start_lookup(current_word)
    else
        mp.osd_message("Dictionary language: " .. lang_name(code))
    end
end

local function lookup_from_popup(word)
    if not word or word == "" or not popup_active then return end
    if current_word and word:lower() == current_word:lower() then return end
    if current_word then history[#history + 1] = current_word end
    start_lookup(word)
end

local function go_back()
    local w = table.remove(history)
    if w then start_lookup(w) end
end

-- ---------------------------------------------------------------- mouse
local function on_click()
    if phover then
        local h = phover
        phover = nil
        if h.key == "chip" and pstate then
            pstate.picker = not pstate.picker
            paint_popup()
        elseif h.key == "back" then
            go_back()
        elseif h.word then
            lookup_from_popup(h.word)
        elseif h.code then
            set_language(h.code)
        end
        return
    end
    if hover and layout then do_lookup(hover.l, hover.w) end
end

local function bind_click()
    -- (re-)adding moves our binding section to the top of mpv's binding stack,
    -- above whatever uosc enabled for its controls
    mp.add_forced_key_binding("MBTN_LEFT", "sublookup-click", on_click)
    click_bound = true
end

local function set_click(on)
    if on == click_bound then return end
    if on then
        bind_click()
    else
        click_bound = false
        mp.remove_key_binding("sublookup-click")
    end
end

-- uosc can re-enable its own bindings after we do (e.g. when the cursor sits over
-- its controls), so re-assert ours shortly after the mouse stops moving.
local reassert = mp.add_timeout(0.1, function()
    if enabled and (hover or phover) then bind_click() end
end)
reassert:kill()

-- Keyboard fallback: looks up the word under the cursor (nothing in uosc claims it)
mp.add_key_binding("Ctrl+d", "lookup-hover", on_click)

local function popup_hit(mx, my)
    if not (popup_active and pstate and pstate.items) then return nil end
    for i = #pstate.items, 1, -1 do
        local it = pstate.items[i]
        if mx >= it.x0 and mx <= it.x1 and my >= it.y0 and my <= it.y1 then return it end
    end
    return nil
end

mp.observe_property("mouse-pos", "native", function(_, pos)
    if not enabled or not ours_visible or not pos then return end
    local li, wi, ph
    if pos.hover then
        ph = popup_hit(pos.x, pos.y)
        if not ph and layout then li, wi = hit_test(pos.x, pos.y) end
    end
    local pchanged = (phover and phover.key) ~= (ph and ph.key)
    local changed = (li ~= (hover and hover.l)) or (wi ~= (hover and hover.w))
    if pchanged then
        phover = ph
        paint_popup()
    end
    if changed then
        hover = li and { l = li, w = wi } or nil
        render()
    end
    if pchanged or changed then set_click(hover ~= nil or phover ~= nil) end
    if hover or phover then
        reassert:kill()
        reassert:resume()
    end
end)

-- ---------------------------------------------------------------- events
local function refresh()
    set_click(false)
    build_layout()
    render()
end

mp.observe_property("sub-text", "string", function(_, v)
    sub_text = v or ""
    if popup_active then dismiss(false) end
    if enabled then refresh() end
end)

mp.observe_property("osd-dimensions", "native", function()
    if not enabled or sub_text == "" then return end
    local W, H = osd_dims()
    if W ~= last_W or H ~= last_H then
        if popup_active then dismiss(false) end
        refresh()
    end
end)

mp.observe_property("pause", "bool", function(_, v)
    if v == false and popup_active then dismiss(false) end
end)

-- Our mode only changes WHO draws the subtitles, never whether they are shown.
-- Native subs are kept hidden (sub-visibility = no) while the mode is on, so mpv's
-- sub-visibility no longer tells us what the user wants. We track that ourselves
-- (ours_visible) from the events that change it:
--   * `v` (cycle sub-visibility) turns the property from our "no" into "yes"
--     with no track change              -> toggle ours
--   * uosc's subtitle menu runs `set sid <id|no>` and then `set sub-visibility yes`
--     (it never toggles)               -> "show subtitles", not a toggle
local last_sid_change = -1
local echo_until = nil

local function set_vis(val)
    if val and not mp.get_property_bool("sub-visibility", true) then
        echo_until = mp.get_time() + 0.3 -- mpv will echo this change back to us
    end
    mp.set_property_bool("sub-visibility", val)
end

local function apply_visibility()
    if ours_visible then
        sub_text = mp.get_property("sub-text") or ""
        refresh()
    else
        if popup_active then dismiss(true) end
        set_click(false)
        hover = nil
        sub_ov:remove()
    end
end

mp.observe_property("sid", "native", function(_, sid)
    last_sid_change = mp.get_time()
    msg.verbose("sid -> " .. tostring(sid))
end)

mp.observe_property("sub-visibility", "bool", function(_, v)
    if v ~= true then return end
    local now = mp.get_time()
    if echo_until then
        local fresh = now < echo_until
        echo_until = nil
        if fresh then -- echo of our own set_vis(true)
            if enabled then set_vis(false) end
            return
        end
    end
    if not enabled then return end
    set_vis(false) -- native subtitles must stay hidden whatever happened

    -- Decide a moment later so a `sid` change arriving after this event is also seen
    mp.add_timeout(0.15, function()
        if not enabled then return end
        local was = ours_visible
        if math.abs(last_sid_change - now) < 0.5 then
            ours_visible = true  -- picked/loaded/cleared a track: show subtitles
        else
            ours_visible = not ours_visible -- plain toggle
        end
        msg.verbose("sub-visibility yes; ours_visible = " .. tostring(ours_visible))
        apply_visibility()
        if ours_visible ~= was then
            mp.osd_message("Subtitles: " .. (ours_visible and "on" or "off"))
        end
    end)
end)

local function set_enabled(v)
    if v == enabled then return end
    enabled = v
    if v then
        -- start in exactly the state the user's subtitles are in (shown or hidden)
        saved_sub_visibility = mp.get_property_bool("sub-visibility", true)
        ours_visible = saved_sub_visibility
        set_vis(false)
        sub_text = mp.get_property("sub-text") or ""
        refresh()
        mp.osd_message("Click-to-define subtitles: on" ..
            (ours_visible and "" or " (subtitles are hidden - toggle them on)"))
    else
        dismiss(true)
        set_click(false)
        hover, layout = nil, nil
        sub_ov:remove()
        set_vis(ours_visible) -- leave native subtitles as the user last had them
        mp.osd_message("Click-to-define subtitles: off")
    end
end

mp.add_key_binding("Ctrl+l", "toggle", function() set_enabled(not enabled) end)
mp.register_script_message("toggle", function() set_enabled(not enabled) end)

if opts.enabled_on_start then
    mp.register_event("file-loaded", function() set_enabled(true) end)
end

mp.add_key_binding(nil, "cycle-lang", function()
    local idx = 0
    for i, l in ipairs(LANGS) do
        if l[1] == opts.lang then idx = i end
    end
    set_language(LANGS[idx % #LANGS + 1][1])
end)