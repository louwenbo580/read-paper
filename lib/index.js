// paper-review — host half.
// Converts uploaded PDFs to structured selectable HTML and Markdown via
// poppler, serves everything over same-origin routes, materializes papers as
// project folders under a "Paper" workspace, and keeps one paper store per
// linked session so each project's viewer shows its own paper.
import { execFile } from 'node:child_process'
import { existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync, unlinkSync, rmSync } from 'node:fs'
import { join, basename } from 'node:path'
import os from 'node:os'
import { promisify } from 'node:util'

const run = promisify(execFile)
const MAX_BYTES = 30 * 1024 * 1024
const TOOL_TIMEOUT = 180000

function paperDir() {
  const home = process.env.DSH_HOME || join(os.homedir(), '.dsh')
  return join(home, 'paper-review')
}

function decodeName(value) {
  if (typeof value !== 'string' || value === '') return null
  try { return decodeURIComponent(value).slice(0, 200) } catch (error) { return String(value).slice(0, 200) }
}

function htmlEscape(s) {
  return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
}

function xmlUnescape(s) {
  return String(s)
    .replace(/&amp;/g, '&').replace(/&lt;/g, '<').replace(/&gt;/g, '>')
    .replace(/&quot;/g, '"').replace(/&apos;/g, "'")
    .replace(/&#(\d+);/g, (m, d) => String.fromCodePoint(parseInt(d, 10)))
    .replace(/&#x([0-9a-fA-F]+);/g, (m, h) => String.fromCodePoint(parseInt(h, 16)))
    .replace(/[\u2060\u200B\u200C\u200D\uFEFF]/g, '')
}

function median(arr) {
  if (arr.length === 0) return 0
  const s = arr.slice().sort((a, b) => a - b)
  const mid = Math.floor(s.length / 2)
  return s.length % 2 ? s[mid] : (s[mid - 1] + s[mid]) / 2
}

function formatSize(bytes) {
  if (!bytes) return ''
  if (bytes < 1024) return bytes + ' B'
  if (bytes < 1024 * 1024) return (bytes / 1024).toFixed(1) + ' KB'
  return (bytes / 1024 / 1024).toFixed(1) + ' MB'
}

function isTableRowLine(l) {
  if (l.words.length < 3) return false
  const words = l.words.slice().sort((a, b) => a.x - b.x)
  const gaps = []
  for (let i = 1; i < words.length; i++) gaps.push(words[i].x - words[i - 1].x2)
  const smallest = Math.min.apply(null, gaps)
  const threshold = Math.max(12, Math.min(24, smallest * 3))
  const big = gaps.filter((g) => g >= threshold)
  // 2-column rows (Parameter | Value) show a single large gap; 3+ column
  // rows show at least two.
  if (big.length >= 2) return true
  return big.length >= 1 && big[0] >= 25 && words.length >= 4
}

function detectColumns(run) {
  const minShare = Math.max(2, Math.ceil(run.length * 0.6))
  const votes = new Map()
  run.forEach((l) => {
    const seen = new Set()
    l.words.forEach((w) => {
      const key = Math.round(w.x / 3)
      if (!seen.has(key)) { votes.set(key, (votes.get(key) || 0) + 1); seen.add(key) }
    })
  })
  const cols = [...votes.entries()].filter((e) => e[1] >= minShare).map((e) => e[0] * 3).sort((a, b) => a - b)
  if (cols.length < 2 || cols.length > 12) return []
  for (let i = 1; i < cols.length; i++) if (cols[i] - cols[i - 1] < 12) return []
  return cols
}

function renderSegments(segs) {
  let out = ''
  for (const s of segs) {
    const t = htmlEscape(s.t)
    const html = s.kind === 'sub' ? '<sub>' + t + '</sub>' : s.kind === 'sup' ? '<sup>' + t + '</sup>' : t
    if (out !== '' && s.kind === 'n') out += ' '
    out += html
  }
  return out
}

function plainSegments(segs) {
  let out = ''
  for (const s of segs) {
    if (out !== '' && s.kind === 'n') out += ' '
    out += s.t
  }
  return out
}

function completeLine(l) {
  l.words.sort((a, b) => a.x - b.x)
  l.x = Math.min.apply(null, l.words.map((w) => w.x))
  const baseH = median(l.heights)
  // Store it: the body-size MODE, heading levels, and paragraph spacing
  // all consume l.baseH, and without it the mode is NaN and every
  // size-based rule silently dies.
  l.baseH = baseH
  // Caps-only text has no descenders, so its bbox height understates the
  // font size (≈0.72em vs ≈0.95em); normalize it for size comparisons.
  const hasLower = l.words.some((w) => /[a-z]/.test(w.t))
  l.hbody = hasLower ? baseH : baseH * 1.3
  const normals = l.words.filter((w) => (w.y2 - w.y) >= baseH * 0.85)
  const refCy = normals.length > 0
    ? median(normals.map((w) => (w.y + w.y2) / 2))
    : l.cy
  const segs = []
  l.words.forEach((w, idx) => {
    const h = w.y2 - w.y
    const cy = (w.y + w.y2) / 2
    let kind = 'n'
    if (h < baseH * 0.8) {
      const prev = l.words[idx - 1]
      const next = l.words[idx + 1]
      const nearPrev = !!prev && (w.x - prev.x2) < baseH * 0.9
      const nearNext = !!next && (next.x - w.x2) < baseH * 0.9
      if (nearPrev || nearNext) {
        if (cy > refCy + baseH * 0.15) kind = 'sub'
        else if (cy < refCy - baseH * 0.15) kind = 'sup'
      }
    }
    const parts = w.t.split(/\s+/).filter((p) => p.length > 0)
    for (const part of parts) {
      const isDots = /^[.\u22C5\u2026]+$/.test(part)
      const last = segs.length > 0 ? segs[segs.length - 1] : null
      if (isDots && last && last.dots) {
        last.t += part
        continue
      }
      segs.push({ t: part, x: w.x, kind, dots: isDots })
    }
  })
  l.segments = segs
  l.html = renderSegments(segs)
  l.plain = plainSegments(segs)
  return l
}

function makeSplitLine(words) {
  return completeLine({
    words,
    heights: words.map((w) => w.y2 - w.y),
    cy: median(words.map((w) => (w.y + w.y2) / 2)),
    h: Math.max.apply(null, words.map((w) => w.y2 - w.y)),
  })
}

function rowCells(line, cols) {
  return cols.map((c) => {
    const segs = (line.segments || []).filter((s) => Math.abs(s.x - c) <= 6)
    return { h: segs.length > 0 ? renderSegments(segs) : '', p: segs.length > 0 ? plainSegments(segs) : '' }
  })
}

function renderBlock(b) {
  if (b.type === 'title') return '<h1 class="pp-doc-title">' + b.html + '</h1>'
  if (b.type === 'meta') return '<div class="pp-meta">' + b.html + '</div>'
  if (b.type === 'abstract') return '<p class="pp-abstract">' + b.html + '</p>'
  if (b.type === 'h') return '<h' + b.level + '>' + b.html + '</h' + b.level + '>'
  if (b.type === 'p') return '<p>' + b.html + '</p>'
  if (b.type === 'toc') {
    return '<div class="pp-toc"><span class="pp-toc-entry">' + b.entry + '</span><span class="pp-toc-page">' + b.page + '</span></div>'
  }
  if (b.type === 'math') {
    return '<div class="pp-math">' + b.html + '</div>'
  }
  if (b.type === 'table') {
    const head = b.rows.length > 0
      ? '<tr>' + b.rows[0].map((c) => '<th>' + c.h + '</th>').join('') + '</tr>'
      : ''
    const bodyRows = b.rows.slice(1)
      .map((r) => '<tr>' + r.map((c) => '<td>' + c.h + '</td>').join('') + '</tr>')
      .join('')
    return '<table>' + head + bodyRows + '</table>'
  }
  if (b.type === 'figure') {
    return '<figure><img src="/paper-review/fig/' + encodeURIComponent(b.file) + '" alt="Figure ' + b.n + ' (page ' + b.page + ')"/><figcaption>Figure ' + b.n + ' \u2014 page ' + b.page + '</figcaption></figure>'
  }
  if (b.type === 'figureimg') {
    return '<figure class="pp-figcrop"><img src="/paper-review/fig/' + encodeURIComponent(b.file) + '" alt="Figure" style="width:' + Math.round(b.w) + 'pt"/></figure>'
  }
  if (b.type === 'eqimg') {
    return '<div class="pp-eq"><img src="/paper-review/fig/' + encodeURIComponent(b.file) + '" alt="' + htmlEscape(b.plain) + '" style="width:' + Math.round(b.w) + 'pt"/><span class="pp-eq-sr">' + htmlEscape(b.plain) + '</span></div>'
  }
  return ''
}

function renderMdBlock(b) {
  if (b.type === 'title') return '# ' + b.plain
  if (b.type === 'meta') return b.plain
  if (b.type === 'abstract') return b.plain
  if (b.type === 'h') return '#'.repeat(Math.min(b.level, 6)) + ' ' + b.plain
  if (b.type === 'p') return b.plain
  if (b.type === 'toc') return '- ' + b.entryPlain + ' — page ' + b.pagePlain
  if (b.type === 'math') return b.plain
  if (b.type === 'table') {
    const rows = b.rows.map((r) => '| ' + r.map((c) => c.p).join(' | ') + ' |')
    return rows.join('\n')
  }
  if (b.type === 'figure') return '![Figure ' + b.n + ' (page ' + b.page + ')](figs/' + encodeURIComponent(b.file) + ')'
  if (b.type === 'figureimg') return '![Figure](figs/' + encodeURIComponent(b.file) + ')'
  if (b.type === 'eqimg') return '(equation rendered as an image)'
  return ''
}

async function convertPdf(pdfPath, dir) {
  const bboxPath = join(dir, 'bbox.xml')
  const figPrefix = join(dir, 'fig')
  const pagesDir = join(dir, 'pages')
  try { rmSync(pagesDir, { recursive: true, force: true }) } catch (error) {}
  // Page crops are regenerated on every conversion, so stale ones from an
  // earlier run of the same PDF must not linger.
  try {
    for (const f of readdirSync(dir)) {
      if (f.startsWith('crop-') && f.endsWith('.png')) unlinkSync(join(dir, f))
    }
  } catch (error) {}
  await run('pdftotext', ['-bbox', '-enc', 'UTF-8', pdfPath, bboxPath], { timeout: TOOL_TIMEOUT, maxBuffer: 64 * 1024 * 1024 })
  const bboxXml = readFileSync(bboxPath, 'utf8')

  const pages = []
  const pageRe = /<page width="([\d.]+)" height="([\d.]+)">([\s\S]*?)<\/page>/g
  let total = 0
  let pm
  while ((pm = pageRe.exec(bboxXml)) !== null) {
    const words = []
    const wordRe = /<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">([\s\S]*?)<\/word>/g
    let wm
    while ((wm = wordRe.exec(pm[3])) !== null) {
      // Drop rotated/multi-line artifacts (plot axis labels, margin dates,
      // watermarks): their bounding boxes are tens to hundreds of points tall
      // or wide, and they poison the line-height heuristics. Rotated text is
      // taller than it is wide; real words are wider than tall.
      const hRaw = +wm[4] - +wm[2]
      const wRaw = +wm[3] - +wm[1]
      if (hRaw > 35 || wRaw > 250) continue
      if (hRaw >= 15 && hRaw > wRaw * 1.1) continue
      words.push({ x: +wm[1], y: +wm[2], x2: +wm[3], y2: +wm[4], t: xmlUnescape(wm[5]) })
    }
    total += words.length
    pages.push({ width: +pm[1], height: +pm[2], words })
  }

  if (total === 0) {
    mkdirSync(pagesDir, { recursive: true })
    await run('pdftoppm', ['-png', '-r', '150', pdfPath, join(pagesDir, 'page')], { timeout: TOOL_TIMEOUT, maxBuffer: 64 * 1024 * 1024 })
    const files = readdirSync(pagesDir).filter((f) => /^page-.*\.png$/.test(f)).sort()
    const parts = []
    for (let i = 0; i < files.length; i++) {
      parts.push('<div class="pp-pageimg-wrap"><img class="pp-pageimg" src="/paper-review/pages/' + encodeURIComponent(files[i]) + '" alt="Page ' + (i + 1) + '"/></div>')
    }
    return { fallback: true, pages: files.length, html: parts.join('\n'), md: '', title: null, abstract: null }
  }

  // Raster figures. `pdfimages -list` reports every raster object in the
  // PDF, and each image with an alpha channel appears TWICE: an `image`
  // row plus its `smask` companion. A smask is not content — rendered
  // alone it is a blank gray rectangle. A pixel-size threshold is
  // meaningless on its own (resolution varies per object), so classify by
  // PHYSICAL size in points: a content figure is at least MIN_FIGURE_PT on
  // both axes, while inline icons and badges (e.g. ORCID logos at ~9 pt)
  // fall far below. Output files are numbered by the `num` column, so map
  // each surviving image to its file by number instead of trusting a
  // filtered list to stay aligned with the alphabetical file order.
  const MIN_FIGURE_PT = 40
  const images = []
  try {
    const { stdout } = await run('pdfimages', ['-list', pdfPath], { timeout: TOOL_TIMEOUT })
    for (const line of stdout.split('\n').slice(2)) {
      const p = line.trim().split(/\s+/)
      if (p.length < 15 || !/^\d+$/.test(p[0]) || !/^\d+$/.test(p[1]) || p[2] !== 'image') continue
      const ppi = +p[12] || 0
      const ptW = ppi > 0 ? (+p[3] / ppi) * 72 : 0
      const ptH = ppi > 0 ? (+p[4] / ppi) * 72 : 0
      if (ptW >= MIN_FIGURE_PT && ptH >= MIN_FIGURE_PT) images.push({ num: +p[1], page: +p[0], w: +p[3] || 0, h: +p[4] || 0 })
    }
  } catch (error) {}
  if (images.length > 0) {
    try {
      await run('pdfimages', ['-png', pdfPath, figPrefix], { timeout: TOOL_TIMEOUT })
    } catch (error) {}
  }
  images.forEach((img) => {
    const file = 'fig-' + String(img.num).padStart(3, '0') + '.png'
    img.file = existsSync(join(dir, file)) ? file : null
  })
  // Drop extracted files that no surviving figure references (smask
  // companions, sub-figure-size icons, leftovers from earlier runs).
  const usedFigFiles = new Set(images.map((im) => im.file).filter(Boolean))
  try {
    for (const f of readdirSync(dir)) {
      if (f.startsWith('fig-') && f.endsWith('.png') && !usedFigFiles.has(f)) unlinkSync(join(dir, f))
    }
  } catch (error) {}

  const bodyHeights = []

  // Cluster words into lines by y-proximity (within one column).
  function clusterWords(words) {
    const sorted = words.slice().sort((a, b) => a.y - b.y || a.x - b.x)
    const lines = []
    let cur = null
    for (const w of sorted) {
      const h = w.y2 - w.y
      const cy = (w.y + w.y2) / 2
      if (cur && Math.abs(cy - cur.cy) <= Math.max(3, cur.h * 0.6)) {
        cur.words.push(w)
        cur.heights.push(h)
        cur.h = Math.max(cur.h, h)
        cur.cy = (cur.cy * (cur.words.length - 1) + cy) / cur.words.length
      } else {
        cur = { cy, h, heights: [h], words: [w] }
        lines.push(cur)
      }
    }
    return lines
  }

  // Two-column pages interleave both columns' words in the content stream.
  // The column gutter is the x where (almost) no word straddles. A gutter is
  // trusted only when it repeats at the same x across the majority of pages
  // (tables in single-column papers create spurious one-page valleys).
  function pageSplits(pages) {
    const valleys = pages.map((page) => {
      const words = page.words.filter((w) => w.y > page.height * 0.18)
      if (words.length < 30) return null
      let best = null
      for (let x = Math.floor(page.width * 0.22); x <= Math.floor(page.width * 0.78); x += 6) {
        let strad = 0
        for (const w of words) if (w.x < x && w.x2 > x) strad++
        if (best === null || strad < best.strad) best = { strad, x }
      }
      return best && best.strad <= Math.max(6, words.length * 0.02) ? best : null
    })
    const clusters = new Map()
    valleys.forEach((v) => {
      if (!v) return
      let key = null
      for (const k of clusters.keys()) if (Math.abs(k - v.x) <= 12) { key = k; break }
      if (key === null) { key = v.x; clusters.set(key, []) }
      clusters.get(key).push(v.x)
    })
    let majority = null
    for (const [k, arr] of clusters) {
      if (!majority || arr.length > majority.arr.length) majority = { k, arr }
    }
    const strong = majority && majority.arr.length >= Math.max(2, Math.ceil(pages.length * 0.5))
    if (!strong) return valleys.map(() => null)
    // Apply the majority gutter to every page: full-width lines (titles,
    // spanning tables) split at the gutter and are re-merged afterwards, so
    // irregular pages survive; pages whose own valley disagrees keep none.
    return valleys.map((v) => (v === null || Math.abs(v.x - majority.k) <= 24 ? majority.k : null))
  }

  // Linearize a split page. Left and right fragments of the SAME visual
  // line share a y band, so cluster both sides into y-groups first. Within
  // a group, a word gap that straddles the gutter AND is anomalous for the
  // group (the median-ratio test) separates two column lines; without it
  // the group is one full-width line (title, spanning table row, centered
  // author line). The column band starts below the contiguous top run of
  // full-width groups, so front-matter labels ("ABSTRACT", "Accepted XXX")
  // and centered author lines never split, and the flows read full-width,
  // then left column, then right column, then full-width footers.
  function mergeSpanning(linesA, linesB, split, pageHeight) {
    linesA.forEach((l) => { l.side = 'A'; l.words.forEach((w) => { w.side = 'A' }) })
    linesB.forEach((l) => { l.side = 'B'; l.words.forEach((w) => { w.side = 'B' }) })
    const groups = []
    for (const l of [...linesA, ...linesB].sort((a, b) => a.cy - b.cy)) {
      const g = groups[groups.length - 1]
      // Tolerance must absorb superscript offset between a line's halves
      // (an author line with "1,2" markers can sit ±6pt apart per side)
      // while staying well below the ~12pt line pitch.
      if (g && Math.abs(l.cy - g.cy) <= 6) g.lines.push(l)
      else groups.push({ cy: l.cy, lines: [l] })
    }
    const startsB = linesB.map((l) => Math.min.apply(null, l.words.map((w) => w.x))).sort((a, b) => a - b)
    const edgeB = startsB.length > 0 ? startsB[Math.floor(startsB.length / 2)] : null
    const analyze = (g) => {
      const words = g.lines.flatMap((l) => l.words).sort((a, b) => a.x - b.x)
      const posGaps = []
      for (let i = 1; i < words.length; i++) {
        const gap = words[i].x - words[i - 1].x2
        if (gap > 0) posGaps.push(gap)
      }
      const medianGap = posGaps.length > 0 ? median(posGaps) : 0
      // The gutter gap is wider than any inter-word space of a single line;
      // a floor of 16pt admits journals whose columns sit only ~20pt apart.
      const splitGap = Math.max(16, medianGap * 2.5)
      const cuts = []
      for (let i = 1; i < words.length; i++) {
        const prev = words[i - 1]
        const gap = words[i].x - prev.x2
        if (gap >= splitGap && prev.x2 <= split && words[i].x >= split) cuts.push(i)
      }
      return { words, cuts }
    }
    const fullCys = []
    for (const g of groups) {
      const sides = new Set(g.lines.map((l) => l.side))
      if (sides.size === 2 && analyze(g).cuts.length === 0) fullCys.push(g.cy)
    }
    fullCys.sort((a, b) => a - b)
    // The column band: the contiguous top run of groups that need no gutter
    // split (true full-width lines), tolerating front-matter spacing. Only
    // groups in the TOP HALF of the page can seed the run: a continuation
    // page has no full-width front matter, and its only full-width group is
    // the page footer — seeding with that pushes the band top to the page
    // bottom and glues both columns into alternating full-width lines.
    const topCys = fullCys.filter((cy) => cy < pageHeight * 0.5)
    let topFullMax = topCys.length > 0 ? topCys[0] : -Infinity
    for (let i = 1; i < topCys.length; i++) {
      // Front-matter spacing can reach ~100pt (title/author/abstract
      // blocks); a mid-page full-width figure sits far below (≥ 200pt),
      // so it never joins the top run.
      if (topCys[i] - topCys[i - 1] > 140) break
      topFullMax = topCys[i]
    }
    const bandTop = topFullMax - 20
    const full = []
    const left = []
    const right = []
    const makeRun = (run) => ({
      cy: median(run.map((w) => (w.y + w.y2) / 2)),
      h: Math.max.apply(null, run.map((w) => w.y2 - w.y)),
      heights: run.map((w) => w.y2 - w.y),
      words: run,
    })
    for (const g of groups) {
      const { words, cuts } = analyze(g)
      const inBand = g.cy >= bandTop
      const runs = []
      if (inBand && cuts.length > 0) {
        let start = 0
        for (const c of cuts) {
          runs.push(words.slice(start, c))
          start = c
        }
        runs.push(words.slice(start))
      } else {
        runs.push(words)
      }
      for (const run of runs) {
        const sides = new Set(run.map((w) => w.side))
        const x = Math.min.apply(null, run.map((w) => w.x))
        let dest
        if (sides.has('A') && sides.has('B')) dest = full
        else if (sides.has('A')) dest = inBand ? left : full
        else if (inBand && edgeB !== null && x >= edgeB - 15) dest = right
        else dest = full
        const line = makeRun(run)
        line.col = dest === left ? 'A' : dest === right ? 'B' : ''
        dest.push(line)
      }
    }
    full.sort((a, b) => a.cy - b.cy)
    left.sort((a, b) => a.cy - b.cy)
    right.sort((a, b) => a.cy - b.cy)
    // Full-width footer lines (journal credits) render after the columns.
    // With no top-matter seed every full-width line is a footer (page
    // bottom), so demote them all instead of comparing against -Infinity.
    const topLines = []
    const bottomLines = []
    if (topFullMax === -Infinity) {
      bottomLines.push(...full)
    } else {
      let inBottom = false
      for (const l of full) {
        const isFooter = l.cy - topFullMax > 60 && full[0] !== l && l.cy > topFullMax
        if (!inBottom && isFooter) inBottom = true
        if (inBottom) bottomLines.push(l)
        else topLines.push(l)
      }
    }
    return topLines.concat(left, right, bottomLines)
  }

  const splits = pageSplits(pages)
  pages.forEach((page, pi) => {
    const split = splits[pi]
    let lines
    if (split !== null) {
      const colA = page.words.filter((w) => (w.x + w.x2) / 2 < split)
      const colB = page.words.filter((w) => (w.x + w.x2) / 2 >= split)
      lines = mergeSpanning(clusterWords(colA), clusterWords(colB), split, page.height)
    } else {
      lines = clusterWords(page.words)
    }
    lines.forEach(completeLine)
    if (split === null) {
      lines.sort((a, b) => a.cy - b.cy)
      lines.forEach((l) => { l.col = '' })
    }
    page.lines = lines
    lines.forEach((l) => bodyHeights.push(l.baseH))
  })
  // Body font size: the MODE of line heights (the most common line height is
  // body text; tables and headings cannot skew it the way a median can).
  let body = 12
  {
    const buckets = new Map()
    for (const h of bodyHeights) {
      const k = Math.round(h)
      buckets.set(k, (buckets.get(k) || 0) + 1)
    }
    let bestCount = 0
    for (const [k, c] of buckets) {
      if (c > bestCount) { bestCount = c; body = k }
    }
  }

  // ── front matter: title, masthead, authors, abstract ─────────────────────
  // Two heading shapes are invisible to a pure size test: section titles set
  // in caps at body size, and numbered section lines ("2.1. Energy Balance
  // Model"). Both are body text in almost no other context, so they are
  // principled heading signals.
  function stripSectionNo(s) {
    return String(s).replace(/^(?:[\d.]+\s*|[IVX]+\.?\s*)+/, '')
  }
  function isCapsLine(l) {
    const ws = l.words.map((w) => w.t)
    const rest = /^(?:[\d.]+|[IVX]+\.?)$/.test(ws[0]) ? ws.slice(1) : ws
    // Caps headings are multi-letter pure-letter runs ("II:" in a caps
    // title may keep its colon); journal names ("MNRAS,"), DOI artifacts,
    // and equation fragments ("P", "L L", "10 K", "CSM") are body text.
    return rest.length >= 1 && rest.every((t) => /^[A-Z][A-Z\s]{3,}:?$/.test(t))
  }
  function isNumberedHeading(l) {
    const p = l.plain.trim()
    // Section numbers carry a trailing dot ("2.", "2.1.") or a Roman
    // numeral ("I.", "IV.2"); a bare digit/letter before a word is a
    // superscript/affiliation marker or the pronoun "I", not a heading.
    let rest
    if (/^\d+(\.\d+)*\.\s+[A-Za-z]{3,}/.test(p)) {
      rest = l.words.slice(1)
    } else if (/^[IVX]+(\.[IVX\d]+)*\.\s+[A-Za-z]{3,}/.test(p) || /^[IVX]{2,}\s+[A-Za-z]{3,}/.test(p)) {
      rest = l.words.slice(1)
    } else if (/^I\s+[A-Za-z]{3,}/.test(p)) {
      // A bare "I" is the pronoun unless EVERY following word is
      // capitalized ("I Introduction" vs "I Introduce the model").
      rest = l.words.slice(1)
      if (rest.some((w) => !/^[A-Z]/.test(w.t))) return false
    } else {
      return false
    }
    if (/\.{4,}/.test(p) || l.words.length > 10) return false
    // A heading is Title Case and ends with a complete word: sentences that
    // happen to start with a number ("0. Conversely, at e = 0.9 ...") are
    // mostly lowercase and end mid-sentence.
    const ws = rest.map((w) => w.t)
    if (!/[A-Za-z]$/.test(ws[ws.length - 1])) return false
    const caps = ws.filter((t) => /^[A-Z]/.test(t)).length
    return caps / ws.length >= 0.5
  }
  // Mixed-case titles have body-sized ink extents, so size alone cannot mark
  // them: score the first page's top band by size × length. The scored lines
  // are adopted only when no earlier heading already serves as the title
  // (a masthead like "MNRAS" or "THE ASTROPHYSICAL JOURNAL" would otherwise
  // outscore the real title).
  let titleLines = []
  let titleTop = null
  let abstractTop = null
  if (pages.length > 0) {
    const p0 = pages[0]
    let best = null
    let firstHeadLine = null
    for (const l of p0.lines) {
      if (l.cy < p0.height * 0.05 || l.cy > p0.height * 0.28) continue
      const p = l.plain.trim()
      if (p.length < 8 || !/[A-Za-z]{3,}/.test(p)) continue
      if (l.hbody < body * 0.95) continue
      const score = l.hbody * Math.min(1, p.length / 20)
      if (!best || score > best.score) best = { line: l, score }
    }
    // First plausible heading on the page: used as the masthead anchor when
    // the scored title is not adopted (and to gate title adoption itself).
    let firstHead = null
    firstHeadLine = null
    for (const l of p0.lines) {
      const lvl = l.hbody >= body * 1.55 ? 1 : l.hbody >= body * 1.32 ? 2 : l.hbody >= body * 1.2 ? 3 : 0
      if (lvl > 0 || isCapsLine(l) || isNumberedHeading(l)) { firstHead = l.plain.trim(); firstHeadLine = l; break }
    }
    if (best) {
      const lines = p0.lines
      const idx = lines.indexOf(best.line)
      const absorbed = []
      for (let k = idx - 1; k >= Math.max(0, idx - 2); k--) {
        const prv = lines[k]
        if (prv.cy < p0.height * 0.05) break
        if (prv.hbody < best.line.hbody * 0.95) break
        const pp = prv.plain.trim()
        if (pp.length < 1 || !/[A-Za-z]{2,}/.test(pp)) break
        absorbed.unshift(prv)
      }
      absorbed.push(best.line)
      for (let k = idx + 1; k < lines.length && k <= idx + 3; k++) {
        const nxt = lines[k]
        if (nxt.cy > p0.height * 0.28) break
        // Same-size only: author lines sit slightly smaller (and their
        // superscripts pull the median down further), so they must not
        // be absorbed into the title.
        if (nxt.hbody < best.line.hbody * 0.9) break
        const np = nxt.plain.trim()
        if (np.length < 2 || !/[A-Za-z]{2,}/.test(np)) break
        absorbed.push(nxt)
      }
      const t0 = firstHead ? stripSectionNo(firstHead) : ''
      if (!firstHead || /^(abstract|introduction|contents)$/i.test(t0) || t0.length < 15 || /:$/.test(t0)) {
        titleLines = absorbed
        titleTop = Math.min.apply(null, absorbed.map((l) => l.cy))
      } else if (best && firstHeadLine === best.line) {
        // The first heading IS the scored title (a large mixed-case title is
        // size-classified as a heading): adopt the absorbed title lines.
        titleLines = absorbed
        titleTop = Math.min.apply(null, absorbed.map((l) => l.cy))
      } else if (firstHeadLine && isCapsLine(firstHeadLine)) {
        // The first heading is a caps line in the title band: a multi-line
        // ALL-CAPS title reports its LAST line as a heading ("FLAGS II:
        // ... OF DIRECT OBSERVABLES"). Adopt the whole same-size caps
        // cluster as the title.
        const ls = p0.lines
        const idx = ls.indexOf(firstHeadLine)
        const cluster = []
        for (let k = idx; k >= 0; k--) {
          const prv = ls[k]
          if (!isCapsLine(prv) || Math.abs(prv.hbody - firstHeadLine.hbody) >= firstHeadLine.hbody * 0.35 || prv.cy < p0.height * 0.03) break
          cluster.unshift(prv)
        }
        for (let k = idx + 1; k < ls.length; k++) {
          const nxt = ls[k]
          if (!isCapsLine(nxt) || Math.abs(nxt.hbody - firstHeadLine.hbody) >= firstHeadLine.hbody * 0.35 || nxt.cy > p0.height * 0.28) break
          cluster.push(nxt)
        }
        if (cluster.length >= 2) {
          titleLines = cluster
          titleTop = Math.min.apply(null, cluster.map((l) => l.cy))
        }
      }
    }
    // Anchor for the masthead band: the tagged title when we have one,
    // otherwise the first heading line when it sits in the title band (a
    // masthead like "MNRAS 000, 1-20" is body-sized text and would otherwise
    // drift into the left column flow and glue itself to the abstract).
    let anchor = titleTop
    if (anchor === null && firstHeadLine && firstHeadLine.cy < p0.height * 0.25) anchor = firstHeadLine.cy
    if (anchor !== null) {
      // Journal banner lines above the title never belong to a column: pull
      // them out of the left/right flows to the very front.
      const mast = p0.lines.filter((l) => l.cy < anchor - 2)
      const rest = p0.lines.filter((l) => l.cy >= anchor - 2)
      mast.sort((a, b) => a.cy - b.cy)
      mast.forEach((l) => { l.inMasthead = true; l.col = '' })
      p0.lines = mast.concat(rest)
      const absHead = p0.lines.find((l) => /^abstract$/i.test(l.plain.trim()) && l.cy > anchor)
      if (absHead) abstractTop = absHead.cy
      const titleBottom = titleLines.length > 0 ? Math.max.apply(null, titleLines.map((l) => l.cy)) : anchor
      // Gap-based abstract detection: a wide gap followed by a CONTINUOUS run
      // of at least six prose lines (an author/affiliation block of several
      // lines followed by another gap does not qualify).
      let gapStart = null
      let gapPitch = null
      {
        const ls = p0.lines
        const pitches = []
        for (let i = 1; i < ls.length; i++) {
          const d = ls[i].cy - ls[i - 1].cy
          if (d > 0 && d < 40) pitches.push(d)
        }
        const pitch = pitches.length > 0 ? median(pitches) : 14
        gapPitch = pitch
        const lowerRatio = (s) => {
          const letters = String(s).match(/[A-Za-z]/g) || []
          const lower = String(s).match(/[a-z]/g) || []
          return letters.length > 0 ? lower.length / letters.length : 0
        }
        for (let i = 1; i < ls.length; i++) {
          const gap = ls[i].cy - ls[i - 1].cy
          if (gap < pitch * 1.4 || ls[i].cy >= p0.height * 0.5 || ls[i].cy <= titleBottom + 2) continue
          let run = 1
          for (let j = i + 1; j < ls.length && ls[j].cy - ls[j - 1].cy < pitch * 1.25; j++) run++
          if (run < 6) continue
          // The run must read as prose: author names and affiliations are
          // capitalized mid-line ("Jack C. Turner , Stephen M. Wilkins"),
          // while an abstract is overwhelmingly lowercase.
          const firstLines = ls.slice(i, i + 3).map((l) => lowerRatio(l.plain))
          if (firstLines.some((r) => r < 0.85)) continue
          gapStart = ls[i].cy
          ls[i].startAbstract = true
          break
        }
      }
      // The gap start only competes with the label when it sits right at the
      // label (a label printed below its abstract); otherwise the label (or
      // the gap, when no label exists) governs.
      let abstractStart = abstractTop
      if (gapStart !== null) {
        if (abstractTop === null) {
          abstractStart = gapStart
        } else if (gapStart < abstractTop && gapStart >= abstractTop - gapPitch * 2) {
          abstractStart = gapStart
          const hl = p0.lines.find((l) => /^abstract$/i.test(l.plain.trim()) && l.cy === abstractTop)
          if (hl) hl.skipAbstract = true
        }
      }
      p0.lines.forEach((l) => {
        if (titleLines.includes(l)) l.isTitle = true
        else if (l.cy < anchor - 2) l.inMasthead = true
        else if (abstractStart !== null && l.cy > titleBottom + 2 && l.cy < abstractStart - 2 && !/^abstract$/i.test(l.plain.trim())) l.inAuthors = true
      })
    }
  }

  // ── figure regions and display equations, rendered as page crops ──────────
  // Vector-drawn figures and LaTeX display equations have no raster images to
  // extract; instead, locate their bounding boxes from the text layout and
  // rasterize them with pdftoppm.
  const MATH_RE = /[=\u2190-\u21FF\u2200-\u2216\u2218-\u22FF\u27C0-\u27FF\u0370-\u03FF\u{1D400}-\u{1D7FF}]/gu
  function mathyCount(s) {
    const m = String(s).match(MATH_RE)
    return m ? m.length : 0
  }
  function isEqLine(l) {
    // Display equations are SHORT math-dense lines; long prose lines with a
    // small inline equation must stay selectable text.
    if (l.plain.length > 90 || l.words.length > 10) return false
    const mathy = mathyCount(l.plain)
    return mathy >= 3 || (mathy >= 1 && /[=:]/.test(l.plain))
  }

  async function cropPageRegions(pdfPath, pageNum, rects, outDir) {
    const files = []
    for (let n = 0; n < rects.length; n++) {
      const r = rects[n]
      const scale = 150 / 72
      const x = Math.max(0, Math.floor(r.left * scale))
      const y = Math.max(0, Math.floor(r.top * scale))
      const w = Math.max(8, Math.ceil((r.right - r.left) * scale))
      const h = Math.max(8, Math.ceil((r.bottom - r.top) * scale))
      const name = 'crop-' + pageNum + '-' + n
      try {
        await run('pdftoppm', ['-f', String(pageNum), '-l', String(pageNum), '-r', '150', '-x', String(x), '-y', String(y), '-W', String(w), '-H', String(h), '-png', '-singlefile', pdfPath, join(outDir, name)], { timeout: TOOL_TIMEOUT })
        const file = name + '.png'
        files.push(existsSync(join(outDir, file)) ? file : null)
      } catch (error) {
        files.push(null)
      }
    }
    return files
  }

  for (let pi = 0; pi < pages.length; pi++) {
    const page = pages[pi]
    // Column left margin: the MEDIAN line start (margin headers at x≈20
    // would skew the minimum and make everything look "indented").
    const colMin = {}
    const starts = {}
    page.lines.forEach((l) => {
      const t = l.col || ''
      if (!starts[t]) starts[t] = []
      starts[t].push(l.x)
    })
    for (const t of Object.keys(starts)) {
      colMin[t] = median(starts[t])
    }
    // Figure regions: runs bounded by two large vertical gaps in one column.
    const groups = {}
    page.lines.forEach((l) => {
      const t = l.col || ''
      if (!groups[t]) groups[t] = []
      groups[t].push(l)
    })
    const rects = []
    const figMarkers = []
    for (const t of Object.keys(groups)) {
      const ls = groups[t]
      const gapOf = (a, b) => b.cy - a.cy - (a.h + b.h) / 2
      // Split the column into blocks at large vertical gaps (column edges
      // included), then classify each block by TEXT DENSITY: figures are
      // mostly-empty regions with sparse labels, while paragraphs, title
      // blocks, and tables are dense. One principled measure replaces the
      // old per-paper label heuristics.
      const spans = []
      let start = 0
      for (let k = 0; k < ls.length - 1; k++) {
        if (gapOf(ls[k], ls[k + 1]) >= 30) {
          spans.push({ from: start, to: k })
          start = k + 1
        }
      }
      spans.push({ from: start, to: ls.length - 1 })
      const blocks = spans.map((b) => {
        let wordArea = 0
        let minX = Infinity
        let maxX = -Infinity
        let wordCount = 0
        const xStarts = new Set()
        for (let k = b.from; k <= b.to; k++) {
          for (const w of ls[k].words) {
            wordArea += Math.max(0.5, w.x2 - w.x) * Math.max(0.5, w.y2 - w.y)
            if (w.x < minX) minX = w.x
            if (w.x2 > maxX) maxX = w.x2
            wordCount++
            xStarts.add(Math.round(w.x / 4))
          }
        }
        const top = ls[b.from].cy - ls[b.from].h / 2
        const bottom = ls[b.to].cy + ls[b.to].h / 2
        const h = bottom - top
        const w = Math.max(30, maxX - minX)
        const lineCount = b.to - b.from + 1
        // Plot labels are scattered (nearly one x-position per word, one or
        // two words per line); prose and table cells reuse few x-positions.
        const scatter = wordCount > 0 ? xStarts.size / wordCount : 0
        const wordsPerLine = lineCount > 0 ? wordCount / lineCount : 0
        const figLike = h > 0 && wordArea / (h * w) < 0.12
          || (scatter > 0.8 && wordsPerLine < 2.5)
        return { ...b, top, bottom, h, minX, maxX, density: h > 0 ? wordArea / (h * w) : 1, figLike }
      }).filter((b) => b.to >= b.from && b.h >= 8)
      // A figure = a maximal run of consecutive figure-like blocks.
      let runStart = 0
      while (runStart < blocks.length) {
        if (!blocks[runStart].figLike) { runStart++; continue }
        let runEnd = runStart
        while (runEnd + 1 < blocks.length && blocks[runEnd + 1].figLike) runEnd++
        const top = blocks[runStart].top
        const bottom = blocks[runEnd].bottom
        const h = bottom - top
        const lineCount = blocks.slice(runStart, runEnd + 1).reduce((s, b) => s + (b.to - b.from + 1), 0)
        if (h >= 50 && h <= 640 && (runEnd > runStart || lineCount >= 3)) {
          let minX = Infinity
          let maxX = -Infinity
          for (let b = runStart; b <= runEnd; b++) {
            if (blocks[b].minX < minX) minX = blocks[b].minX
            if (blocks[b].maxX > maxX) maxX = blocks[b].maxX
          }
          let left = Math.max(0, minX - 8)
          let right = Math.min(page.width, maxX + 8)
          if (t === 'A') right = Math.min(right, page.width * 0.5 + 6)
          if (t === 'B') left = Math.max(left, page.width * 0.5 - 6)
          const region = { top, bottom, left, right, file: null }
          for (let b = runStart; b <= runEnd; b++) {
            for (let k = blocks[b].from; k <= blocks[b].to; k++) ls[k].inFig = region
          }
          rects.push(region)
          figMarkers.push(region)
        }
        runStart = runEnd + 1
      }
    }
    // Display equations: indented, math-dense lines, grouped when consecutive.
    const eqGroups = []
    for (const t of Object.keys(groups)) {
      const ls = groups[t]
      let i = 0
      while (i < ls.length) {
        const l = ls[i]
        const indented = (l.x - (colMin[t] || l.x)) >= 25
        const headingLike = l.hbody >= body * 1.25
        if (!l.inFig && indented && isEqLine(l) && !headingLike) {
          const grp = [l]
          let j = i + 1
          while (j < ls.length && !ls[j].inFig) {
            const m = ls[j]
            const ind2 = (m.x - (colMin[t] || m.x)) >= 25
            if (!ind2 || !isEqLine(m) || m.hbody >= body * 1.25) break
            const gap = m.cy - ls[j - 1].cy - (ls[j - 1].h + m.h) / 2
            if (gap > body * 1.1) break
            grp.push(m)
            j++
          }
          const left = Math.max(0, Math.min.apply(null, grp.map((x) => x.x)) - 6)
          const right = Math.min(page.width, Math.max.apply(null, grp.map((x) => Math.max.apply(null, x.words.map((w) => w.x2)))) + 6)
          const top = grp[0].cy - grp[0].h / 2 - 4
          const bottom = grp[grp.length - 1].cy + grp[grp.length - 1].h / 2 + 4
          const group = { top, bottom, left, right, file: null, lines: grp, plain: grp.map((x) => x.plain).join(' ') }
          grp.forEach((x) => { x.eqGroup = group })
          rects.push(group)
          eqGroups.push(group)
          i = j
          continue
        }
        i++
      }
    }
    if (rects.length > 0) {
      const files = await cropPageRegions(pdfPath, pi + 1, rects, dir)
      rects.forEach((r, idx) => { r.file = files[idx] })
    }
    page.figRegions = figMarkers
    page.eqGroups = eqGroups
  }

  const parts = []
  const mdParts = []
  let firstHeading = null
  let abstractText = null
  let pendingAbstract = false

  pages.forEach((page, pi) => {
    // Typical line pitch of this page (used to tell heading spacing apart
    // from ordinary line spacing).
    const pitches = []
    for (let i = 1; i < page.lines.length; i++) {
      const d = page.lines[i].cy - page.lines[i - 1].cy
      if (d > 0 && d < 40) pitches.push(d)
    }
    const pagePitch = pitches.length > 0 ? median(pitches) : body * 1.15
    const splitLines = []
    for (const l of page.lines) {
      const firstWord = l.words.length > 0 ? l.words[0] : null
      const firstH = firstWord ? (firstWord.y2 - firstWord.y) : 0
      // Split an oversized lead-in ("FLAGS" before "II: Constraining…")
      // from the rest of the line; caps/body-size headings are handled by
      // the isCapsLine/isNumberedHeading rules below instead. Display
      // equations (big symbols, not prose) are never heading lead-ins.
      if (l.words.length > 1 && firstH >= body * 1.25 && !isEqLine(l)) {
        let k = 1
        while (k < l.words.length && (l.words[k].y2 - l.words[k].y) >= body * 1.12) k++
        if (k < l.words.length && k <= 6) {
          const headLine = makeSplitLine(l.words.slice(0, k))
          headLine.forceHeading = true
          const restLine = makeSplitLine(l.words.slice(k))
          for (const f of [headLine, restLine]) {
            f.inMasthead = l.inMasthead
            f.inAuthors = l.inAuthors
            f.isTitle = l.isTitle
            f.startAbstract = l.startAbstract
            f.skipAbstract = l.skipAbstract
          }
          splitLines.push(headLine)
          splitLines.push(restLine)
          continue
        }
      }
      splitLines.push(l)
    }
    const lines = splitLines
    const blocks = []
    let para = null
    const flushPara = () => {
      if (para) {
        // The abstract is the first paragraph AFTER the "ABSTRACT" heading;
        // decide at flush time so earlier paragraphs are never mislabeled.
        let type = 'p'
        if (pendingAbstract && abstractText === null) {
          type = 'abstract'
          abstractText = para.map((x) => x.plain).join(' ')
          pendingAbstract = false
        }
        blocks.push({ type, html: para.map((x) => x.html).join(' '), plain: para.map((x) => x.plain).join(' ') })
        para = null
      }
    }
    const isMathLine = (line) => line.words.length <= 4
      && line.words.filter((w) => /[^\x00-\x7F]/.test(w.t)).length >= Math.ceil(line.words.length * 0.6)
    let i = 0
    let lastFig = null
    const emittedFigs = new Set()
    while (i < lines.length) {
      const l = lines[i]
      // Lines inside a figure region are swallowed: the figure renders as an
      // image; internal labels are dropped from the text flow.
      if (l.inFig) {
        if (l.inFig !== lastFig) {
          flushPara()
          if (l.inFig.file && !emittedFigs.has(l.inFig.file)) {
            blocks.push({ type: 'figureimg', file: l.inFig.file, w: l.inFig.right - l.inFig.left, h: l.inFig.bottom - l.inFig.top })
            emittedFigs.add(l.inFig.file)
          }
          lastFig = l.inFig
        }
        i++
        continue
      }
      lastFig = null
      // Front matter on the first page: the title renders as a document
      // heading; the journal banner and the author/affiliation block render
      // as muted metadata so the abstract and the first body paragraph are
      // visually unmistakable.
      if (l.isTitle) {
        flushPara()
        blocks.push({ type: 'title', html: l.html, plain: l.plain })
        i++
        continue
      }
      if (l.inMasthead || l.inAuthors) {
        flushPara()
        blocks.push({ type: 'meta', html: l.html, plain: l.plain })
        i++
        continue
      }
      // Papers without an "ABSTRACT" label: the gap-marked line starts the
      // abstract paragraph.
      if (l.startAbstract && !pendingAbstract && abstractText === null) pendingAbstract = true
      // Equations render as crops below; a display equation's big symbols
      // must not make it a heading by size.
      let level = (l.eqGroup || isMathLine(l)) ? 0 : l.forceHeading ? 3 : l.hbody >= body * 1.55 ? 1 : l.hbody >= body * 1.32 ? 2 : l.hbody >= body * 1.2 ? 3 : 0
      // Single-word lines are headings only when they look like words:
      // annotations, page numbers, and watermarks (e.g. "28", "Jul") stay text.
      if (level > 0 && l.words.length === 1 && !l.forceHeading) {
        const t = l.plain
        if (t.length < 4 || !/[A-Za-z\u00C0-\u024F]{2,}/.test(t)) level = 0
      }
      // Caps-only and numbered section titles are headings even at body size
      // (bold ink does not change the glyph boxes). A caps heading stands
      // apart from the surrounding text (section spacing), unlike caps table
      // captions or fragments inside a paragraph.
      if (level === 0) {
        const caps = isCapsLine(l) && (() => {
          const prevL = i > 0 ? lines[i - 1] : null
          const nextL = i + 1 < lines.length ? lines[i + 1] : null
          const gp = prevL ? l.cy - prevL.cy : Infinity
          const gn = nextL ? nextL.cy - l.cy : Infinity
          return gp > pagePitch * 1.3 || gn > pagePitch * 1.3
        })()
        if (caps || isNumberedHeading(l)) level = 3
      }
      if (level > 0) {
        flushPara()
        if (firstHeading === null) firstHeading = l.plain
        if (/^abstract$/i.test(l.plain.trim()) && !l.skipAbstract) pendingAbstract = true
        blocks.push({ type: 'h', level, html: l.html, plain: l.plain })
        i++
        continue
      }
      const dotIdx = (l.segments || []).findIndex((s) => s.dots && s.t.length >= 6)
      const afterDots = dotIdx >= 0 ? l.segments.slice(dotIdx + 1) : []
      const pageText = afterDots.map((s) => s.t).join('').trim()
      if (dotIdx >= 0 && /^\d+$/.test(pageText) && afterDots.length >= 1) {
        flushPara()
        blocks.push({
          type: 'toc',
          entry: renderSegments(l.segments.slice(0, dotIdx + 1)),
          page: renderSegments(afterDots),
          entryPlain: plainSegments(l.segments.slice(0, dotIdx + 1)),
          pagePlain: plainSegments(afterDots),
        })
        i++
        continue
      }
      // Display equations render as cropped images (fractions, cases, and
      // alignment stay visually intact).
      if (l.eqGroup) {
        flushPara()
        const grp = l.eqGroup
        if (grp.file) {
          blocks.push({ type: 'eqimg', file: grp.file, w: grp.right - grp.left, h: grp.bottom - grp.top, plain: grp.plain })
        } else {
          blocks.push({ type: 'math', html: grp.lines.map((x) => x.html).join('<br/>'), plain: grp.plain })
        }
        i += grp.lines.length
        continue
      }
      if (isMathLine(l)) {
        const mathHtml = []
        const mathPlain = []
        let j = i
        while (j < lines.length && isMathLine(lines[j])) {
          mathHtml.push(lines[j].html)
          mathPlain.push(lines[j].plain)
          j++
        }
        flushPara()
        blocks.push({ type: 'math', html: mathHtml.join('<br/>'), plain: mathPlain.join(' ') })
        i = j
        continue
      }
      let j = i
      if (isTableRowLine(l)) {
        while (j < lines.length && isTableRowLine(lines[j])) j++
        const run = lines.slice(i, j)
        if (run.length >= 2) {
          let cols = detectColumns(run)
          if (cols.length >= 3) {
            // Absorb wrapped continuation lines: a line whose words all land
            // in the established columns (none at the first column's start)
            // belongs to the cell above it.
            let extended = false
            const rows = run.map((rl) => rowCells(rl, cols))
            let k = j
            while (k < lines.length) {
              const nxt = lines[k]
              const wordsInCols = nxt.words.filter((w) => cols.some((c) => Math.abs(w.x - c) <= 6)).length
              const atFirstCol = nxt.words.some((w) => Math.abs(w.x - cols[0]) <= 6)
              if (wordsInCols >= Math.max(1, Math.ceil(nxt.words.length * 0.6)) && !atFirstCol && k - j < 8) {
                const cells = rowCells(nxt, cols)
                rows[rows.length - 1] = rows[rows.length - 1].map((cell, ci) => (cell && cells[ci]) ? cell + ' ' + cells[ci] : cell)
                j = k + 1
                extended = true
                k++
                continue
              }
              break
            }
            flushPara()
            blocks.push({ type: 'table', rows })
            i = j
            continue
          }
        }
      }
      const prev = lines[i - 1]
      const gap = prev ? l.cy - prev.cy - (prev.h + l.h) / 2 : 0
      // A column switch whose y restarts near the top of the page starts a new
      // paragraph: the left column's open paragraph must not absorb the right
      // column's first lines (their cy jumps backwards, so the gap test alone
      // never fires).
      const colRestart = prev && para && l.col !== prev.col && l.col !== '' && prev.col !== '' && l.cy < prev.cy - body
      if (para && (gap > body * 0.9 || colRestart)) flushPara()
      para = para || []
      para.push(l)
      i++
    }
    flushPara()

    let imgIdx = 0
    images.filter((im) => im.page === pi + 1).forEach((im) => {
      if (im.file) {
        imgIdx++
        blocks.push({ type: 'figure', file: im.file, n: imgIdx, page: pi + 1, w: im.w, h: im.h })
      }
    })

    for (const b of blocks) {
      parts.push(renderBlock(b))
      mdParts.push(renderMdBlock(b))
    }
    if (pi < pages.length - 1) {
      parts.push('<div class="pp-pagebreak">\u2014 Page ' + (pi + 2) + ' \u2014</div>')
      mdParts.push('\n---\n')
    }
  })
  // Title: the tagged title lines win (they were adopted only when no usable
  // heading preceded them); otherwise the first detected heading serves.
  let title = titleLines.length > 0 ? titleLines.map((l) => l.plain.trim()).join(' ') : (firstHeading || null)
  if (title !== null) {
    const t0 = stripSectionNo(title.trim())
    if (/^(abstract|introduction|contents)$/i.test(t0) || t0.length < 15 || /:$/.test(t0)) title = firstHeading || null
  }
  return {
    fallback: false,
    pages: pages.length,
    html: parts.join('\n'),
    md: mdParts.join('\n\n'),
    title,
    abstract: abstractText,
  }
}

export const name = 'paper-review'
export const inject = ['webServer']

// Exported for the evaluation harness (scripts/eval.mjs) and future tooling.
export { convertPdf }

const CONVERT_VERSION = 35

function makeStore(dir, opts = {}) {
  return {
    dir,
    pdfName: opts.pdfName || 'current.pdf',
    metaName: opts.metaName || 'current.json',
    htmlName: opts.htmlName || 'current.html',
    mdName: opts.mdName || 'current.md',
    bytes: null,
    meta: { name: '', size: 0 },
    html: null,
    md: '',
    title: null,
    abstract: null,
    conv: { converting: false, ready: false, fallback: false, pages: 0, error: null },
    seq: 0,
  }
}

export function apply(ctx) {
  const globalDir = paperDir()
  mkdirSync(globalDir, { recursive: true })
  const global = makeStore(globalDir)
  const linksPath = join(globalDir, 'links.json')
  let links = {}
  try { links = JSON.parse(readFileSync(linksPath, 'utf8')) } catch (error) { links = {} }
  const linkedStores = new Map()

  function saveLinks() {
    try { writeFileSync(linksPath, JSON.stringify(links)) } catch (error) {}
  }

  function pdfPath(st) { return join(st.dir, st.pdfName) }
  function metaPath(st) { return join(st.dir, st.metaName) }
  function htmlPath(st) { return join(st.dir, st.htmlName) }
  function mdPath(st) { return join(st.dir, st.mdName) }

  function startConvert(st) {
    const v = ++st.seq
    st.conv = { converting: true, ready: false, fallback: false, pages: 0, error: null }
    convertPdf(pdfPath(st), st.dir).then((result) => {
      if (v !== st.seq) return
      st.html = result.html
      st.md = result.md
      st.title = result.title
      st.abstract = result.abstract
      st.conv = { converting: false, ready: true, fallback: result.fallback, pages: result.pages, error: null }
      try {
        writeFileSync(htmlPath(st), st.html)
        writeFileSync(mdPath(st), st.md)
        writeFileSync(metaPath(st), JSON.stringify({ ...st.meta, pages: result.pages, fallback: result.fallback, convertVersion: CONVERT_VERSION }))
      } catch (error) {}
    }).catch((error) => {
      if (v !== st.seq) return
      st.html = null
      st.md = ''
      st.conv = { converting: false, ready: false, fallback: false, pages: 0, error: String((error && error.message) || error) }
    })
  }

  function initStore(st) {
    try {
      if (existsSync(pdfPath(st))) {
        st.bytes = readFileSync(pdfPath(st))
        const saved = existsSync(metaPath(st)) ? JSON.parse(readFileSync(metaPath(st), 'utf8')) : null
        st.meta = { name: (saved && saved.name) || basename(pdfPath(st)), size: st.bytes.length }
        if (existsSync(htmlPath(st)) && saved && saved.convertVersion === CONVERT_VERSION) {
          st.html = readFileSync(htmlPath(st), 'utf8')
          if (existsSync(mdPath(st))) st.md = readFileSync(mdPath(st), 'utf8')
          const titleMatch = st.html.match(/<h[123]>([^<]*)<\/h[123]>/)
          st.title = titleMatch ? titleMatch[1] : null
          st.conv = { converting: false, ready: true, fallback: !!saved.fallback, pages: saved.pages || 0, error: null }
        } else {
          startConvert(st)
        }
      }
    } catch (error) {
      st.bytes = null
      st.meta = { name: '', size: 0 }
    }
  }

  initStore(global)

  function storeFor(url) {
    try {
      const sid = new URL(url, 'http://localhost').searchParams.get('sessionId')
      if (sid && links[sid]) {
        let st = linkedStores.get(sid)
        if (!st) {
          st = makeStore(links[sid], { pdfName: 'paper.pdf', metaName: 'meta.json', htmlName: 'paper.html', mdName: 'paper.md' })
          linkedStores.set(sid, st)
          initStore(st)
        }
        return st
      }
    } catch (error) {}
    return global
  }

  function sendJson(res, code, obj) {
    res.writeHead(code, { 'Content-Type': 'application/json', 'Cache-Control': 'no-store' })
    res.end(JSON.stringify(obj))
  }

  function serveImage(req, res, prefix, subdir) {
    const st = storeFor(req.url)
    const pathname = new URL(req.url, 'http://localhost').pathname
    const name = decodeURIComponent(pathname.slice(prefix.length))
    if (!/^[A-Za-z0-9._-]+$/.test(name)) { res.writeHead(400); res.end('bad name'); return }
    let data = null
    try {
      data = readFileSync(join(st.dir, subdir, name))
    } catch (error) {
      // linked stores keep images in a figs/ subfolder
      if (subdir === '') {
        try { data = readFileSync(join(st.dir, 'figs', name)) } catch (error2) {}
      }
    }
    if (data === null) { res.writeHead(404, { 'Content-Type': 'text/plain' }); res.end('not found'); return }
    res.writeHead(200, { 'Content-Type': 'image/png', 'Content-Length': data.length, 'Cache-Control': 'no-store' })
    res.end(data)
  }

  async function createProject() {
    if (global.bytes === null || global.html === null) throw new Error('No converted paper available.')
    let base = null
    let workspaceId = null
    const wsReg = ctx.get('workspaceRegistry')
    if (wsReg) {
      let paperWs = wsReg.list().find((w) => w.title === 'Paper' || /\/Paper\/?$/.test(w.path))
      if (!paperWs) {
        const existing = wsReg.list().find((w) => w.path && /\/Downloads\/?$/.test(w.path))
        const root = existing ? existing.path : join(os.homedir(), 'Downloads')
        const paperPath = join(root, 'Paper')
        mkdirSync(paperPath, { recursive: true })
        try {
          paperWs = await wsReg.create(paperPath, 'Paper')
        } catch (error) {
          base = paperPath
        }
      }
      if (paperWs) {
        base = paperWs.path
        workspaceId = paperWs.id
      }
    }
    if (base === null) base = join(os.homedir(), 'Downloads', 'Paper')
    const rawName = global.title && String(global.title).trim() ? String(global.title).trim() : String(global.meta.name || 'paper').replace(/\.pdf$/i, '')
    const safe = rawName
      .replace(/[^\w.-]+/g, '-')
      .replace(/^-+|-+$/g, '')
      .slice(0, 60) || 'paper'
    const projectDir = join(base, safe)
    mkdirSync(projectDir, { recursive: true })
    writeFileSync(join(projectDir, 'paper.pdf'), global.bytes)
    writeFileSync(join(projectDir, 'paper.md'), global.md || '')
    if (global.html) {
      const html = global.html.replace(/\/paper-review\/fig\//g, 'figs/').replace(/\/paper-review\/pages\//g, 'pages/')
      writeFileSync(join(projectDir, 'paper.html'), html)
    }
    try {
      const figs = readdirSync(globalDir).filter((f) => (f.startsWith('fig-') || f.startsWith('crop-')) && f.endsWith('.png'))
      if (figs.length > 0) {
        mkdirSync(join(projectDir, 'figs'), { recursive: true })
        for (const f of figs) writeFileSync(join(projectDir, 'figs', f), readFileSync(join(globalDir, f)))
      }
      const pageDir = join(globalDir, 'pages')
      if (existsSync(pageDir)) {
        mkdirSync(join(projectDir, 'pages'), { recursive: true })
        for (const f of readdirSync(pageDir)) writeFileSync(join(projectDir, 'pages', f), readFileSync(join(pageDir, f)))
      }
    } catch (error) {}
    const title = global.title || safe
    const readme = [
      '# ' + title,
      '',
      'Source: `' + global.meta.name + '` (' + formatSize(global.meta.size) + ', ' + (global.conv.pages || 0) + ' pages)',
      '',
      global.abstract ? '## Abstract\n\n' + global.abstract : '',
      '',
      '## Files',
      '',
      '- `paper.pdf` — the original PDF',
      '- `paper.md` — the converted text (headings, tables, sub/superscripts)',
      '- `paper.html` — the converted document (open in a browser)',
      '',
      'Use this folder as the workspace context when asking questions about the paper.',
    ].join('\n')
    writeFileSync(join(projectDir, 'README.md'), readme)
    writeFileSync(join(projectDir, 'meta.json'), JSON.stringify({
      name: global.meta.name,
      size: global.meta.size,
      pages: global.conv.pages,
      fallback: global.conv.fallback,
      title: global.title,
      convertVersion: CONVERT_VERSION,
    }))
    return { path: projectDir, workspaceId }
  }

  ctx.effect(() => {
    const routes = [
      ctx.webServer.register({
        kind: 'exact',
        path: '/paper-review/paper.pdf',
        handler(req, res) {
          const st = storeFor(req.url)
          if (st.bytes === null) { res.writeHead(404, { 'Content-Type': 'text/plain' }); res.end('no paper'); return }
          res.writeHead(200, {
            'Content-Type': 'application/pdf',
            'Content-Length': st.bytes.length,
            'Cache-Control': 'no-store',
          })
          res.end(st.bytes)
        },
      }),
      ctx.webServer.register({
        kind: 'exact',
        path: '/paper-review/state',
        handler(req, res) {
          const st = storeFor(req.url)
          sendJson(res, 200, {
            present: st.bytes !== null,
            name: st.meta.name,
            size: st.bytes ? st.bytes.length : 0,
            converting: st.conv.converting,
            ready: st.conv.ready,
            fallback: st.conv.fallback,
            pages: st.conv.pages,
            title: st.title,
            error: st.conv.error,
          })
        },
      }),
      ctx.webServer.register({
        kind: 'exact',
        path: '/paper-review/document.html',
        handler(req, res) {
          const st = storeFor(req.url)
          if (st.html === null) { res.writeHead(404, { 'Content-Type': 'text/plain' }); res.end('no document'); return }
          let html = st.html
          // For linked sessions, figure URLs carry the session so images
          // resolve against that project's store (project files may also use
          // relative figs/ paths from the exported standalone copy).
          try {
            const sid = new URL(req.url, 'http://localhost').searchParams.get('sessionId')
            if (sid && links[sid]) {
              html = html.replace(/\/paper-review\/fig\/([A-Za-z0-9._-]+)/g, '/paper-review/fig/$1?sessionId=' + encodeURIComponent(sid))
              html = html.replace(/\/paper-review\/pages\/([A-Za-z0-9._-]+)/g, '/paper-review/pages/$1?sessionId=' + encodeURIComponent(sid))
              html = html.replace(/src="figs\/([A-Za-z0-9._-]+)"/g, 'src="/paper-review/fig/$1?sessionId=' + encodeURIComponent(sid) + '"')
              html = html.replace(/src="pages\/([A-Za-z0-9._-]+)"/g, 'src="/paper-review/pages/$1?sessionId=' + encodeURIComponent(sid) + '"')
            }
          } catch (error) {}
          res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-store' })
          res.end(html)
        },
      }),
      ctx.webServer.register({
        kind: 'exact',
        path: '/paper-review/document.md',
        handler(req, res) {
          const st = storeFor(req.url)
          if (st.bytes === null) { res.writeHead(404, { 'Content-Type': 'text/plain' }); res.end('no document'); return }
          res.writeHead(200, { 'Content-Type': 'text/markdown; charset=utf-8', 'Cache-Control': 'no-store' })
          res.end(st.md)
        },
      }),
      ctx.webServer.register({
        kind: 'prefixes',
        path: '/paper-review/fig',
        handler(req, res) { serveImage(req, res, '/paper-review/fig/', '') },
      }),
      ctx.webServer.register({
        kind: 'prefixes',
        path: '/paper-review/pages',
        handler(req, res) { serveImage(req, res, '/paper-review/pages/', 'pages') },
      }),
      ctx.webServer.register({
        kind: 'exact',
        path: '/paper-review/project',
        handler(req, res) {
          if (req.method !== 'POST') { sendJson(res, 405, { ok: false, error: 'POST only' }); return }
          createProject().then((result) => {
            sendJson(res, 200, { ok: true, path: result.path, workspaceId: result.workspaceId })
          }).catch((error) => {
            sendJson(res, 500, { ok: false, error: String((error && error.message) || error) })
          })
        },
      }),
      ctx.webServer.register({
        kind: 'exact',
        path: '/paper-review/link',
        handler(req, res) {
          if (req.method !== 'POST') { sendJson(res, 405, { ok: false, error: 'POST only' }); return }
          const chunks = []
          req.on('data', (c) => chunks.push(c))
          req.on('end', () => {
            try {
              const body = JSON.parse(Buffer.concat(chunks).toString('utf8') || '{}')
              if (typeof body.sessionId !== 'string' || typeof body.path !== 'string') {
                sendJson(res, 400, { ok: false, error: 'sessionId and path are required.' })
                return
              }
              if (!existsSync(join(body.path, 'paper.pdf'))) {
                sendJson(res, 400, { ok: false, error: 'project folder not found.' })
                return
              }
              links[body.sessionId] = body.path
              saveLinks()
              sendJson(res, 200, { ok: true })
            } catch (error) {
              sendJson(res, 400, { ok: false, error: String((error && error.message) || error) })
            }
          })
        },
      }),
      ctx.webServer.register({
        kind: 'exact',
        path: '/paper-review/session-title',
        handler(req, res) {
          if (req.method !== 'POST') { sendJson(res, 405, { ok: false, error: 'POST only' }); return }
          const chunks = []
          req.on('data', (c) => chunks.push(c))
          req.on('end', () => {
            try {
              const body = JSON.parse(Buffer.concat(chunks).toString('utf8') || '{}')
              const titleSvc = ctx.get('sessionTitle')
              const sessionsSvc = ctx.get('sessions')
              const session = sessionsSvc && typeof body.sessionId === 'string' ? sessionsSvc.get(body.sessionId) : undefined
              if (!session || !titleSvc) { sendJson(res, 200, { ok: false, error: 'session unavailable' }); return }
              titleSvc.rename(session, String(body.title || 'Paper').slice(0, 80))
              sendJson(res, 200, { ok: true })
            } catch (error) {
              sendJson(res, 400, { ok: false, error: String((error && error.message) || error) })
            }
          })
        },
      }),
      ctx.webServer.register({
        kind: 'exact',
        path: '/paper-review/upload',
        handler(req, res) {
          if (req.method !== 'POST') { sendJson(res, 405, { ok: false, error: 'POST only' }); return }
          const name = decodeName(req.headers['x-paper-name'])
          const chunks = []
          let size = 0
          let overflow = false
          req.on('data', (chunk) => {
            size += chunk.length
            if (size > MAX_BYTES) { overflow = true; return }
            chunks.push(chunk)
          })
          req.on('end', () => {
            if (overflow) { sendJson(res, 413, { ok: false, error: 'This PDF is larger than the 30 MB limit.' }); return }
            const buf = Buffer.concat(chunks)
            if (buf.length < 4) { sendJson(res, 400, { ok: false, error: 'Empty upload.' }); return }
            global.bytes = buf
            global.meta = { name: name || 'paper.pdf', size: buf.length }
            global.html = null
            global.md = ''
            global.title = null
            global.abstract = null
            try { writeFileSync(pdfPath(global), buf) } catch (error) {}
            try { writeFileSync(metaPath(global), JSON.stringify(global.meta)) } catch (error) {}
            try { unlinkSync(htmlPath(global)) } catch (error) {}
            try { unlinkSync(mdPath(global)) } catch (error) {}
            sendJson(res, 200, { ok: true, name: global.meta.name, size: global.meta.size })
            startConvert(global)
          })
          req.on('error', () => {
            try { sendJson(res, 400, { ok: false, error: 'Upload interrupted.' }) } catch (error) {}
          })
        },
      }),
      ctx.webServer.register({
        kind: 'exact',
        path: '/paper-review/delete',
        handler(req, res) {
          global.seq++
          global.bytes = null
          global.meta = { name: '', size: 0 }
          global.html = null
          global.md = ''
          global.title = null
          global.abstract = null
          global.conv = { converting: false, ready: false, fallback: false, pages: 0, error: null }
          try { unlinkSync(pdfPath(global)) } catch (error) {}
          try { unlinkSync(metaPath(global)) } catch (error) {}
          try { unlinkSync(htmlPath(global)) } catch (error) {}
          try { unlinkSync(mdPath(global)) } catch (error) {}
          try { unlinkSync(join(globalDir, 'bbox.xml')) } catch (error) {}
          try { rmSync(join(globalDir, 'pages'), { recursive: true, force: true }) } catch (error) {}
          try {
            for (const f of readdirSync(globalDir)) {
              if ((f.startsWith('fig-') || f.startsWith('crop-')) && f.endsWith('.png')) unlinkSync(join(globalDir, f))
            }
          } catch (error) {}
          sendJson(res, 200, { ok: true })
        },
      }),
    ]
    return () => {
      for (const dispose of routes) dispose()
    }
  })
}
