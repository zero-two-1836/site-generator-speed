// A fast drop-in for makefun-site 1.0.0 (site-generator-speed-01): run(input) returns the reference build's output
// tree for one case's site, byte for byte, with less CPU time. The semantics are makefun-site's own (its README and
// code are the spec); this module re-implements them with the slow shapes removed: bulk HTML escaping instead of a
// regex replace per character, first-character dispatch in the Markdown lexer instead of a battery of anchored
// regexes per line, a scanner front-matter parse that never splits the body, per-build slug and link caches, and a
// word counter that allocates nothing. Dependency-free ES module; main.ts is the driver the harness runs.

'use strict';

// ---------------------------------------------------------------- text

const ESCAPES = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };
const ESCAPE_ANY = /[&<>"']/;
const ESCAPE_ALL = /[&<>"']/g;

/** `text` with & < > " and ' escaped; the common no-special-character string is returned as it stands. */
function escapeHtml(text) {
  if (!ESCAPE_ANY.test(text)) return text;
  return text.replace(ESCAPE_ALL, (c) => ESCAPES[c]);
}

const SLUG_MAX = 64;

/** The reference slug algorithm, whole: NFKD, combining marks dropped, A-Z lowered, runs of other characters one "-". */
function slugifySlow(text) {
  const plain = text.normalize('NFKD').replace(/\p{M}/gu, '');
  let out = '';
  let gap = false;
  for (const ch of plain) {
    let keep = null;
    if (ch >= 'A' && ch <= 'Z') keep = ch.toLowerCase();
    else if ((ch >= 'a' && ch <= 'z') || (ch >= '0' && ch <= '9')) keep = ch;
    if (keep === null) {
      gap = out.length > 0;
      continue;
    }
    if (gap) out += '-';
    gap = false;
    out += keep;
  }
  out = out.slice(0, SLUG_MAX).replace(/-+$/, '');
  return out === '' ? 'untitled' : out;
}

/**
 * The slug of `text`. Pure ASCII takes a direct loop: ASCII has no NFKD decomposition and no combining marks, so the
 * slow path's answer for it is exactly this loop's. Anything else takes the reference algorithm unchanged.
 */
function slugifyCompute(text) {
  for (let i = 0; i < text.length; i++) {
    if (text.charCodeAt(i) > 0x7f) return slugifySlow(text);
  }
  let out = '';
  let gap = false;
  for (let i = 0; i < text.length; i++) {
    const c = text.charCodeAt(i);
    let keep = -1;
    if (c >= 0x41 && c <= 0x5a) keep = c + 0x20;
    else if ((c >= 0x61 && c <= 0x7a) || (c >= 0x30 && c <= 0x39)) keep = c;
    if (keep === -1) {
      gap = out.length > 0;
      continue;
    }
    if (gap) out += '-';
    gap = false;
    out += String.fromCharCode(keep);
  }
  out = out.slice(0, SLUG_MAX).replace(/-+$/, '');
  return out === '' ? 'untitled' : out;
}

/** `slug` made unique against `taken` (and added to it): the first of slug, slug-2, slug-3 ... not taken. */
function uniqueSlug(slug, taken) {
  let out = slug;
  for (let n = 2; taken.has(out); n++) out = `${slug}-${n}`;
  taken.add(out);
  return out;
}

const MONTHS = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];

/** A YYYY-MM-DD date in words, from the string alone. */
function longDate(date) {
  const [y, m, d] = date.split('-');
  return `${Number(d)} ${MONTHS[Number(m) - 1]} ${y}`;
}

/** Whether a UTF-16 code unit is JavaScript whitespace (the \s set), for the word counter and list continuations. */
function isWsCode(c) {
  return (
    c === 0x20 ||
    (c >= 0x09 && c <= 0x0d) ||
    c === 0xa0 ||
    c === 0x1680 ||
    (c >= 0x2000 && c <= 0x200a) ||
    c === 0x2028 ||
    c === 0x2029 ||
    c === 0x202f ||
    c === 0x205f ||
    c === 0x3000 ||
    c === 0xfeff
  );
}

/** The words of a body: its runs of characters other than whitespace, counted without allocating the runs. */
function wordsOf(text) {
  let n = 0;
  let inWord = false;
  for (let i = 0; i < text.length; i++) {
    const c = text.charCodeAt(i);
    if (c < 0x80) {
      // ASCII whitespace is exactly the \s set's ASCII part: tab..carriage return and the space.
      if (c === 0x20 || (c >= 0x09 && c <= 0x0d)) inWord = false;
      else if (!inWord) {
        n++;
        inWord = true;
      }
    } else if (isWsCode(c)) inWord = false;
    else if (!inWord) {
      n++;
      inWord = true;
    }
  }
  return n;
}

// ---------------------------------------------------------------- front matter

const FM_KEYS = new Set(['title', 'date', 'tags', 'draft', 'layout', 'slug', 'summary']);
const FM_LINE = /^([a-z_]+):(?: (.*))?$/;
const FM_DATE = /^(\d{4})-(\d{2})-(\d{2})$/;
const FM_NAME = /^[a-z0-9-]+$/;
const FM_SLUG = /^[a-z0-9]+(?:-[a-z0-9]+)*$/;
const FM_TAG = /^[^"[\]]+$/;

/** The days of month `m` (1-12) of year `y`, by the Gregorian rule. */
function daysIn(y, m) {
  if (m === 2) return (y % 4 === 0 && y % 100 !== 0) || y % 400 === 0 ? 29 : 28;
  return m === 4 || m === 6 || m === 9 || m === 11 ? 30 : 31;
}

/** A string value: "..." with \" and \\ its only escapes, or bare, the rest of the line (never opening on " or [). */
function stringOf(raw) {
  if (raw.startsWith('"')) {
    if (raw.length < 2 || !raw.endsWith('"')) return { error: 'a quoted string is not closed' };
    let out = '';
    for (let i = 1; i < raw.length - 1; i++) {
      const c = raw[i];
      if (c === '\\') {
        const n = raw[i + 1];
        if ((n !== '"' && n !== '\\') || i + 1 === raw.length - 1) return { error: 'a quoted string holds an escape other than \\" or \\\\' };
        out += n;
        i++;
      } else if (c === '"') return { error: 'a quoted string holds a stray quote' };
      else out += c;
    }
    return { value: out };
  }
  if (raw.startsWith('[')) return { error: 'a bare string opens on [' };
  return { value: raw };
}

/** One key's value, or why it is refused. */
function valueOf(key, raw) {
  switch (key) {
    case 'title':
    case 'summary': {
      const s = stringOf(raw);
      return 'error' in s ? { error: `key "${key}": ${s.error}` } : s;
    }
    case 'date': {
      const m = FM_DATE.exec(raw);
      const y = m ? Number(m[1]) : 0;
      const mo = m ? Number(m[2]) : 0;
      const d = m ? Number(m[3]) : 0;
      if (!m || y < 1970 || y > 2099 || mo < 1 || mo > 12 || d < 1 || d > daysIn(y, mo)) return { error: 'key "date": not a date from 1970-01-01 to 2099-12-31 (YYYY-MM-DD)' };
      return { value: raw };
    }
    case 'tags': {
      if (!raw.startsWith('[') || !raw.endsWith(']')) return { error: 'key "tags": not a list [a, b]' };
      const inner = raw.slice(1, -1);
      if (inner.trim() === '') return { value: [] };
      const tags = inner.split(',').map((t) => t.trim());
      if (tags.some((t) => t === '' || !FM_TAG.test(t))) return { error: 'key "tags": an empty tag, or one holding " [ or ]' };
      return { value: tags };
    }
    case 'draft':
      return raw === 'true' ? { value: true } : raw === 'false' ? { value: false } : { error: 'key "draft": true or false' };
    case 'layout':
      return FM_NAME.test(raw) ? { value: raw } : { error: 'key "layout": not a template name' };
    case 'slug':
      return FM_SLUG.test(raw) && raw.length <= 64 ? { value: raw } : { error: 'key "slug": not a slug' };
    default:
      return { error: `unknown key "${key}"` };
  }
}

/**
 * A source's front matter and body: { data, body }, or { error } with the first reason it is refused. `text` has "\n"
 * line ends. The reference splits the whole text into lines and joins the tail back for the body; this scans line
 * bounds instead and slices the body out whole — the same lines, the same first "---" close (found before any line is
 * validated, as the reference finds it), the same reasons in the same order.
 */
function parseFrontMatter(text) {
  const firstNl = text.indexOf('\n');
  const firstLine = firstNl === -1 ? text : text.slice(0, firstNl);
  if (firstLine !== '---') return { error: 'no front matter' };
  // Collect the front-matter lines while looking for the closing "---", exactly as the reference's scan does.
  const lines = [];
  let pos = firstNl === -1 ? text.length : firstNl + 1;
  let bodyStart = -1;
  if (firstNl !== -1) {
    for (;;) {
      const nl = text.indexOf('\n', pos);
      const line = nl === -1 ? text.slice(pos) : text.slice(pos, nl);
      if (line === '---') {
        bodyStart = nl === -1 ? text.length : nl + 1;
        break;
      }
      lines.push(line);
      if (nl === -1) break;
      pos = nl + 1;
    }
  }
  if (bodyStart === -1) return { error: 'the front matter is not closed' };
  const data = {};
  for (let j = 0; j < lines.length; j++) {
    const line = lines[j];
    if (/^[ \t]*$/.test(line) || line.startsWith('#')) continue;
    const m = FM_LINE.exec(line);
    if (!m) return { error: `line ${j + 2} is not "key: value"` };
    const key = m[1];
    const raw = (m[2] ?? '').replace(/[ \t]+$/, '');
    if (!FM_KEYS.has(key)) return { error: `unknown key "${key}"` };
    if (Object.hasOwn(data, key)) return { error: `key "${key}" is given twice` };
    if (raw === '') return { error: `key "${key}" has no value` };
    const v = valueOf(key, raw);
    if ('error' in v) return v;
    data[key] = v.value;
  }
  if (!Object.hasOwn(data, 'title')) return { error: 'no title' };
  return { data, body: text.slice(bodyStart) };
}

// ---------------------------------------------------------------- markdown

/** Whether `line` is blank: spaces and tabs only. */
function isBlank(line) {
  for (let i = 0; i < line.length; i++) {
    const c = line.charCodeAt(i);
    if (c !== 0x20 && c !== 0x09) return false;
  }
  return true;
}

/** A fence line's language, or null when `line` is not a fence opening: ``` then language characters then blanks. */
function fenceLang(line) {
  if (line.charCodeAt(0) !== 0x60 || line.charCodeAt(1) !== 0x60 || line.charCodeAt(2) !== 0x60) return null;
  let i = 3;
  while (i < line.length) {
    const c = line.charCodeAt(i);
    const ok = (c >= 0x41 && c <= 0x5a) || (c >= 0x61 && c <= 0x7a) || (c >= 0x30 && c <= 0x39) || c === 0x5f || c === 0x2b || c === 0x2d;
    if (!ok) break;
    i++;
  }
  const lang = line.slice(3, i);
  while (i < line.length) {
    const c = line.charCodeAt(i);
    if (c !== 0x20 && c !== 0x09) return null;
    i++;
  }
  return lang;
}

/** Whether `line` closes a fence: three backticks then blanks only. */
function isFenceClose(line) {
  if (line.charCodeAt(0) !== 0x60 || line.charCodeAt(1) !== 0x60 || line.charCodeAt(2) !== 0x60) return false;
  for (let i = 3; i < line.length; i++) {
    const c = line.charCodeAt(i);
    if (c !== 0x20 && c !== 0x09) return false;
  }
  return true;
}

/** A heading line's level and text, or null: 1 to 6 #, at least one blank, text with trailing blanks dropped. */
function headingOf(line) {
  let depth = 0;
  while (line.charCodeAt(depth) === 0x23) depth++;
  if (depth === 0 || depth > 6) return null;
  let i = depth;
  const c = line.charCodeAt(i);
  if (c !== 0x20 && c !== 0x09) return null;
  while (i < line.length) {
    const cc = line.charCodeAt(i);
    if (cc !== 0x20 && cc !== 0x09) break;
    i++;
  }
  let end = line.length;
  while (end > i) {
    const cc = line.charCodeAt(end - 1);
    if (cc !== 0x20 && cc !== 0x09) break;
    end--;
  }
  if (end === i) return null;
  return { depth, text: line.slice(i, end) };
}

/** Whether `line` is a thematic break: --- or ***, then blanks only. */
function isHR(line) {
  const c = line.charCodeAt(0);
  if (c !== 0x2d && c !== 0x2a) return false;
  if (line.charCodeAt(1) !== c || line.charCodeAt(2) !== c) return false;
  for (let i = 3; i < line.length; i++) {
    const x = line.charCodeAt(i);
    if (x !== 0x20 && x !== 0x09) return false;
  }
  return true;
}

/** A bullet item's text, or null: "- " or "* " then the item. */
function bulletOf(line) {
  const c = line.charCodeAt(0);
  if (c !== 0x2d && c !== 0x2a) return null;
  if (line.charCodeAt(1) !== 0x20) return null;
  return line.slice(2);
}

/** An ordered item's number and text, or null: 1 to 9 digits, ". ", then the item. */
function orderedOf(line) {
  let i = 0;
  while (i < line.length) {
    const c = line.charCodeAt(i);
    if (c < 0x30 || c > 0x39) break;
    i++;
  }
  if (i === 0 || i > 9) return null;
  if (line.charCodeAt(i) !== 0x2e || line.charCodeAt(i + 1) !== 0x20) return null;
  return { num: Number(line.slice(0, i)), text: line.slice(i + 2) };
}

/** Whether `line` continues a list item: two or more spaces then a non-whitespace character. */
function isContinued(line) {
  let i = 0;
  while (line.charCodeAt(i) === 0x20) i++;
  if (i < 2 || i >= line.length) return false;
  return !isWsCode(line.charCodeAt(i));
}

/** Whether `line` ends a paragraph: a blank line, a fence, a heading or a thematic break. */
function endsParagraph(line) {
  return isBlank(line) || fenceLang(line) !== null || headingOf(line) !== null || isHR(line);
}

/** A paragraph or item line as it is rendered: spaces and tabs at either end dropped. */
function trimLine(line) {
  let a = 0;
  let b = line.length;
  while (a < b) {
    const c = line.charCodeAt(a);
    if (c !== 0x20 && c !== 0x09) break;
    a++;
  }
  while (b > a) {
    const c = line.charCodeAt(b - 1);
    if (c !== 0x20 && c !== 0x09) break;
    b--;
  }
  return a === 0 && b === line.length ? line : line.slice(a, b);
}

/** `src`'s block tokens, in order — the reference lexer, dispatched on each line's first character. */
function lex(src) {
  const lines = src.split('\n');
  const tokens = [];
  let i = 0;
  while (i < lines.length) {
    const line = lines[i];
    if (isBlank(line)) {
      i++;
      continue;
    }
    const c0 = line.charCodeAt(0);
    if (c0 === 0x60) {
      const lang = fenceLang(line);
      if (lang !== null) {
        const body = [];
        i++;
        while (i < lines.length && !isFenceClose(lines[i])) body.push(lines[i++]);
        i++;
        tokens.push({ type: 'code', lang, lines: body });
        continue;
      }
    }
    if (c0 === 0x23) {
      const heading = headingOf(line);
      if (heading !== null) {
        tokens.push({ type: 'heading', depth: heading.depth, text: heading.text });
        i++;
        continue;
      }
    }
    if ((c0 === 0x2d || c0 === 0x2a) && isHR(line)) {
      tokens.push({ type: 'hr' });
      i++;
      continue;
    }
    if (c0 === 0x3e) {
      const body = [];
      while (i < lines.length && lines[i].charCodeAt(0) === 0x3e) {
        const l = lines[i++];
        body.push(l.charCodeAt(1) === 0x20 ? l.slice(2) : l.slice(1));
      }
      tokens.push({ type: 'blockquote', lines: body.map(trimLine).filter((l) => l !== '') });
      continue;
    }
    const bullet = c0 === 0x2d || c0 === 0x2a ? bulletOf(line) : null;
    const ordered = bullet === null && c0 >= 0x30 && c0 <= 0x39 ? orderedOf(line) : null;
    if (bullet !== null || ordered !== null) {
      const isOrdered = ordered !== null;
      const items = [];
      let cur = line;
      for (;;) {
        const m = isOrdered ? orderedOf(cur) : bulletOf(cur);
        if (m !== null) {
          items.push([trimLine(isOrdered ? m.text : m)]);
          i++;
        } else if (isContinued(cur)) {
          items[items.length - 1].push(trimLine(cur));
          i++;
        } else break;
        if (i >= lines.length) break;
        cur = lines[i];
      }
      tokens.push({ type: 'list', ordered: isOrdered, start: isOrdered ? ordered.num : 1, items: items.map((parts) => parts.join('\n')) });
      continue;
    }
    const body = [trimLine(line)];
    i++;
    while (i < lines.length && !endsParagraph(lines[i])) body.push(trimLine(lines[i++]));
    tokens.push({ type: 'paragraph', text: body.join('\n') });
  }
  return tokens;
}

/** The characters a backslash escapes, by code unit. */
const ESCAPABLE = new Set([0x5c, 0x60, 0x2a, 0x5f, 0x5b, 0x5d, 0x28, 0x29, 0x23, 0x2b, 0x2d, 0x2e, 0x21, 0x3e]);

/** The first index from `from` where `s` holds `what` (one or two code units) outside a backslash escape, or -1. */
function findUnescaped(s, what, from) {
  const w0 = what.charCodeAt(0);
  const w1 = what.length > 1 ? what.charCodeAt(1) : -1;
  for (let j = from; j <= s.length - what.length; j++) {
    const c = s.charCodeAt(j);
    if (c === 0x5c && j + 1 < s.length && ESCAPABLE.has(s.charCodeAt(j + 1))) {
      j++;
      continue;
    }
    if (c === w0 && (w1 === -1 || s.charCodeAt(j + 1) === w1)) return j;
  }
  return -1;
}

/** The first single * from `from` (one whose run is not **), outside an escape, or -1. */
function findSingleStar(s, from) {
  for (let j = from; j < s.length; j++) {
    const c = s.charCodeAt(j);
    if (c === 0x5c && j + 1 < s.length && ESCAPABLE.has(s.charCodeAt(j + 1))) {
      j++;
      continue;
    }
    if (c !== 0x2a) continue;
    if (s.charCodeAt(j + 1) === 0x2a) {
      j++;
      continue;
    }
    return j;
  }
  return -1;
}

const INTERESTING = /[\\`*\["&<>']/g;
const TARGET_WS = /\s/;

/**
 * `s` rendered inline; `env.link(target)` is a link's href. One scan finds every character that is either
 * structural (\ ` * [) or escaped in the output (& < > " '); the runs between them hold neither, so they are
 * written as they stand, and the structural handling itself is the reference's, decision for decision.
 */
function inline(s, env) {
  let out = '';
  let i = 0;
  const n = s.length;
  while (i < n) {
    INTERESTING.lastIndex = i;
    const m = INTERESTING.exec(s);
    const j = m === null ? n : m.index;
    if (j > i) {
      out += s.slice(i, j);
      i = j;
    }
    if (m === null) break;
    const c = s[i];
    if (c === '&') {
      out += '&amp;';
      i++;
      continue;
    }
    if (c === '<') {
      out += '&lt;';
      i++;
      continue;
    }
    if (c === '>') {
      out += '&gt;';
      i++;
      continue;
    }
    if (c === '"') {
      out += '&quot;';
      i++;
      continue;
    }
    if (c === "'") {
      out += '&#39;';
      i++;
      continue;
    }
    if (c === '\\') {
      // The escaped character as escapeHtml writes it: of the escapable characters only ">" has an entity.
      if (i + 1 < n && ESCAPABLE.has(s.charCodeAt(i + 1))) {
        const nx = s[i + 1];
        out += nx === '>' ? '&gt;' : nx;
        i += 2;
      } else {
        out += '\\';
        i++;
      }
      continue;
    }
    if (c === '`') {
      const k = s.indexOf('`', i + 1);
      if (k > i + 1) {
        out += `<code>${escapeHtml(s.slice(i + 1, k))}</code>`;
        i = k + 1;
      } else {
        out += '`';
        i++;
      }
      continue;
    }
    if (c === '*') {
      if (s[i + 1] === '*') {
        const k = findUnescaped(s, '**', i + 2);
        if (k > i + 2) {
          out += `<strong>${inline(s.slice(i + 2, k), env)}</strong>`;
          i = k + 2;
        } else {
          out += '**';
          i += 2;
        }
        continue;
      }
      const k = findSingleStar(s, i + 1);
      if (k > i + 1) {
        out += `<em>${inline(s.slice(i + 1, k), env)}</em>`;
        i = k + 1;
      } else {
        out += '*';
        i++;
      }
      continue;
    }
    // c === '['
    const k = findUnescaped(s, ']', i + 1);
    const mm = k !== -1 && s[k + 1] === '(' ? s.indexOf(')', k + 2) : -1;
    const target = mm === -1 ? '' : s.slice(k + 2, mm);
    if (target !== '' && !TARGET_WS.test(target)) {
      out += `<a href="${escapeHtml(env.link(target))}">${inline(s.slice(i + 1, k), env)}</a>`;
      i = mm + 1;
      continue;
    }
    out += '[';
    i++;
  }
  return out;
}

/**
 * `src` rendered: its HTML (each block on its own lines, a "\n" after the last), its table of contents (every level 2
 * and 3 heading) and its excerpt (the first paragraph's inline HTML, or ""). `env.slug` is the build's cached slugify.
 */
function renderMarkdown(src, env) {
  const ids = new Set();
  const blocks = [];
  const toc = [];
  let excerpt = null;
  for (const t of lex(src)) {
    switch (t.type) {
      case 'heading': {
        const id = uniqueSlug(env.slug(t.text), ids);
        const html = inline(t.text, env);
        blocks.push(`<h${t.depth} id="${id}">${html}</h${t.depth}>`);
        if (t.depth === 2 || t.depth === 3) toc.push({ level: t.depth, id, html });
        break;
      }
      case 'code': {
        const cls = t.lang === '' ? '' : ` class="language-${escapeHtml(t.lang)}"`;
        blocks.push(`<pre><code${cls}>${t.lines.map((l) => `${escapeHtml(l)}\n`).join('')}</code></pre>`);
        break;
      }
      case 'hr':
        blocks.push('<hr>');
        break;
      case 'blockquote':
        blocks.push(t.lines.length === 0 ? '<blockquote>\n</blockquote>' : `<blockquote>\n<p>${inline(t.lines.join('\n'), env)}</p>\n</blockquote>`);
        break;
      case 'list': {
        const tag = t.ordered ? 'ol' : 'ul';
        const open = t.ordered && t.start !== 1 ? `<ol start="${t.start}">` : `<${tag}>`;
        blocks.push(`${open}\n${t.items.map((item) => `<li>${inline(item, env)}</li>\n`).join('')}</${tag}>`);
        break;
      }
      case 'paragraph': {
        const html = inline(t.text, env);
        if (excerpt === null) excerpt = html;
        blocks.push(`<p>${html}</p>`);
        break;
      }
    }
  }
  return { html: blocks.map((b) => `${b}\n`).join(''), toc, excerpt: excerpt ?? '' };
}

// ---------------------------------------------------------------- templates

const INCLUDE_DEPTH = 8;

const TPL_PATH = /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/;
const TPL_FOR = /^for ([A-Za-z_][A-Za-z0-9_]*) in (\S+)$/;
const TPL_IF = /^if (not )?(\S+)$/;
const TPL_INCLUDE = /^include "([a-z0-9-]+)"$/;

/** A template that does not parse: its name and why. */
class TemplateError extends Error {}

/** The path `text` names, split at its dots, or a TemplateError. */
function pathOf(name, text) {
  if (!TPL_PATH.test(text)) throw new TemplateError(`template "${name}": ${JSON.stringify(text)} is not a path`);
  return text.split('.');
}

/** Whether src[a..b) is spaces and tabs only. */
function blanksOnly(src, a, b) {
  for (let k = a; k < b; k++) {
    const c = src.charCodeAt(k);
    if (c !== 0x20 && c !== 0x09) return false;
  }
  return true;
}

/** `src`'s tokens: text, {{ }}, {{{ }}} and {% %}, a standalone tag's line taken with it. */
function tokenize(name, src) {
  const tokens = [];
  let text = '';
  let i = 0;
  while (i < src.length) {
    const open = src.indexOf('{', i);
    if (open === -1 || open === src.length - 1) {
      text += src.slice(i);
      break;
    }
    const next = src[open + 1];
    if (next !== '{' && next !== '%') {
      text += src.slice(i, open + 1);
      i = open + 1;
      continue;
    }
    text += src.slice(i, open);
    if (next === '{') {
      const raw = src[open + 2] === '{';
      const close = src.indexOf(raw ? '}}}' : '}}', open + (raw ? 3 : 2));
      if (close === -1) throw new TemplateError(`template "${name}": a ${raw ? '{{{' : '{{'} is not closed`);
      if (text !== '') tokens.push({ t: 'text', text });
      text = '';
      tokens.push({ t: raw ? 'raw' : 'var', path: pathOf(name, src.slice(open + (raw ? 3 : 2), close).trim()) });
      i = close + (raw ? 3 : 2);
      continue;
    }
    const close = src.indexOf('%}', open + 2);
    if (close === -1) throw new TemplateError(`template "${name}": a {% is not closed`);
    const end = close + 2;
    const lineStart = src.lastIndexOf('\n', open - 1) + 1;
    const nl = src.indexOf('\n', end);
    const lineEnd = nl === -1 ? src.length : nl;
    const standalone = blanksOnly(src, lineStart, open) && blanksOnly(src, end, lineEnd);
    if (standalone) text = text.slice(0, text.length - (open - lineStart));
    if (text !== '') tokens.push({ t: 'text', text });
    text = '';
    tokens.push({ t: 'tag', tag: src.slice(open + 2, close).trim() });
    i = standalone ? (nl === -1 ? src.length : nl + 1) : end;
  }
  if (text !== '') tokens.push({ t: 'text', text });
  return tokens;
}

/** The body a parse stack frame currently appends to. */
function frameBody(node) {
  return node.kind === 'if' ? node.else ?? node.then : node.body;
}

/** `src` parsed into its tree of nodes (a TemplateError when it does not parse). */
function parseTemplate(name, src) {
  const root = { kind: 'root', body: [] };
  const stack = [root];
  let body = root.body;
  for (const tok of tokenize(name, src)) {
    if (tok.t === 'text') body.push({ kind: 'text', text: tok.text });
    else if (tok.t === 'var' || tok.t === 'raw') body.push({ kind: tok.t, path: tok.path });
    else {
      const tag = tok.tag;
      const top = stack[stack.length - 1];
      let m;
      if ((m = TPL_FOR.exec(tag)) !== null) {
        const node = { kind: 'for', name: m[1], path: pathOf(name, m[2]), body: [] };
        body.push(node);
        stack.push(node);
        body = node.body;
      } else if ((m = TPL_IF.exec(tag)) !== null) {
        const node = { kind: 'if', not: m[1] !== undefined, path: pathOf(name, m[2]), then: [], else: null };
        body.push(node);
        stack.push(node);
        body = node.then;
      } else if (tag === 'else') {
        if (top.kind !== 'if' || top.else !== null) throw new TemplateError(`template "${name}": an else outside an if`);
        top.else = [];
        body = top.else;
      } else if (tag === 'endfor' || tag === 'endif') {
        if (top.kind !== (tag === 'endfor' ? 'for' : 'if')) throw new TemplateError(`template "${name}": an ${tag} with no open ${tag.slice(3)}`);
        stack.pop();
        body = frameBody(stack[stack.length - 1]);
      } else if ((m = TPL_INCLUDE.exec(tag)) !== null) body.push({ kind: 'include', name: m[1] });
      else throw new TemplateError(`template "${name}": {% ${tag} %} is not a tag`);
    }
  }
  if (stack.length > 1) throw new TemplateError(`template "${name}": a ${stack[stack.length - 1].kind} is not closed`);
  return root.body;
}

/** The value at `path` in the scope chain: its first name from the nearest scope holding it, then own properties. */
function lookup(scope, path) {
  let s = scope;
  const first = path[0];
  while (s !== null && !Object.hasOwn(s.vars, first)) s = s.parent;
  if (s === null) return undefined;
  let v = s.vars[first];
  for (let k = 1; k < path.length; k++) {
    if (v === null || typeof v !== 'object' || !Object.hasOwn(v, path[k])) return undefined;
    v = v[path[k]];
  }
  return v;
}

/** A value as text: a string itself, a number in JavaScript's digits, true or false, an array's items joined by ", ", else "". */
function textOf(v) {
  if (typeof v === 'string') return v;
  if (typeof v === 'number') return String(v);
  if (typeof v === 'boolean') return v ? 'true' : 'false';
  if (Array.isArray(v)) return v.map(textOf).join(', ');
  return '';
}

/** Whether a value counts as true in an if: not undefined, null, false, "", 0 or an empty array. */
function truthy(v) {
  if (Array.isArray(v)) return v.length > 0;
  return v !== undefined && v !== null && v !== false && v !== '' && v !== 0;
}

/**
 * `nodes` rendered in `scope` ({ vars, parent }). `ctx` holds the parsed templates (a Map of name to nodes, a
 * template that did not parse absent) and the include depth.
 */
function renderNodes(nodes, scope, ctx, depth) {
  let out = '';
  for (let idx = 0; idx < nodes.length; idx++) {
    const n = nodes[idx];
    switch (n.kind) {
      case 'text':
        out += n.text;
        break;
      case 'var':
        out += escapeHtml(textOf(lookup(scope, n.path)));
        break;
      case 'raw':
        out += textOf(lookup(scope, n.path));
        break;
      case 'if': {
        const v = truthy(lookup(scope, n.path));
        const branch = v !== n.not ? n.then : n.else;
        if (branch !== null) out += renderNodes(branch, scope, ctx, depth);
        break;
      }
      case 'for': {
        const xs = lookup(scope, n.path);
        if (!Array.isArray(xs)) break;
        for (let k = 0; k < xs.length; k++) {
          const vars = { [n.name]: xs[k], loop: { index: k + 1, first: k === 0, last: k === xs.length - 1, length: xs.length } };
          out += renderNodes(n.body, { vars, parent: scope }, ctx, depth);
        }
        break;
      }
      case 'include': {
        const t = ctx.templates.get(n.name);
        if (t !== undefined && depth < INCLUDE_DEPTH) out += renderNodes(t, scope, ctx, depth + 1);
        break;
      }
    }
  }
  return out;
}

// ---------------------------------------------------------------- the build

const REPORT_FILE = 'build-report.txt';
const RESERVED = ['posts', 'tags', 'page'];

/** Code-unit order (never the locale's). */
const byCodeUnits = (a, b) => (a < b ? -1 : a > b ? 1 : 0);

/** `rel` (a link's path, "/"-separated) from the directory `dir` of a source, or null when it climbs out of the root. */
function resolvePath(dir, rel) {
  const parts = dir === '' ? [] : dir.split('/');
  for (const seg of rel.split('/')) {
    if (seg === '' || seg === '.') continue;
    if (seg === '..') {
      if (parts.length === 0) return null;
      parts.pop();
    } else parts.push(seg);
  }
  return parts.join('/');
}

const dirOf = (path) => (path.includes('/') ? path.slice(0, path.lastIndexOf('/')) : '');

const SCHEME = /^[A-Za-z][A-Za-z0-9+.-]*:/;

/** One site's output tree: path -> text. The reference build's pipeline, stage for stage. */
function build(input) {
  const templates = new Map();
  const report = [];
  for (const name of Object.keys(input.templates).sort(byCodeUnits)) {
    try {
      templates.set(name, parseTemplate(name, input.templates[name]));
    } catch (err) {
      if (!(err instanceof TemplateError)) throw err;
      report.push(err.message);
    }
  }
  const base = input.site.base_url.replace(/\/+$/, '');
  const slugCache = new Map();
  const slug = (text) => {
    let v = slugCache.get(text);
    if (v === undefined) {
      v = slugifyCompute(text);
      slugCache.set(text, v);
    }
    return v;
  };
  const dateCache = new Map();
  const dateLong = (date) => {
    let v = dateCache.get(date);
    if (v === undefined) {
      v = longDate(date);
      dateCache.set(date, v);
    }
    return v;
  };

  // 1. The sources, in code-unit order of their paths, line ends made "\n"; a source that is not .md is static.
  const sources = [];
  const statics = [];
  const files = [...input.files].sort((x, y) => byCodeUnits(x.path, y.path));
  for (const f of files) {
    if (f.path.endsWith('.md')) {
      sources.push({ path: f.path, text: f.content.includes('\r') ? f.content.replace(/\r\n?/g, '\n') : f.content });
    } else statics.push({ path: f.path, content: f.content });
  }

  // 2. Each source's front matter: a refused source is reported and dropped, and so is a draft. The checks run in
  // the reference's order and the first one that fails is the one reported.
  const kept = [];
  for (const s of sources) {
    const fm = parseFrontMatter(s.text);
    if ('error' in fm) {
      report.push(`refused ${s.path}: ${fm.error}`);
      continue;
    }
    s.data = fm.data;
    s.body = fm.body;
    s.post = s.path.startsWith('posts/');
    const own = RESERVED.find((d) => d !== 'posts' && s.path.startsWith(`${d}/`));
    if (own !== undefined) {
      report.push(`refused ${s.path}: ${own}/ is the generator's own`);
      continue;
    }
    if (s.post && !Object.hasOwn(s.data, 'date')) {
      report.push(`refused ${s.path}: a post needs a date`);
      continue;
    }
    const layout = s.data.layout ?? (s.post ? 'post' : 'page');
    if (!templates.has(layout)) {
      report.push(`refused ${s.path}: layout "${layout}" is no template that parses`);
      continue;
    }
    s.layout = layout;
    if (s.data.draft === true) {
      report.push(`draft ${s.path}`);
      continue;
    }
    kept.push(s);
  }

  // 3. Each page's output directory and url: its slug made unique in its directory, in source order.
  const bySource = new Map();
  {
    const taken = new Map();
    const takenIn = (dir) => {
      if (!taken.has(dir)) taken.set(dir, new Set(dir === '' ? RESERVED : []));
      return taken.get(dir);
    };
    for (const s of kept) {
      const dir = s.post ? 'posts' : dirOf(s.path);
      const sl = uniqueSlug(s.data.slug ?? slug(s.data.title), takenIn(dir));
      s.slug = sl;
      s.outDir = dir === '' ? sl : `${dir}/${sl}`;
      s.url = `${base}/${s.outDir}/`;
      bySource.set(s.path, s);
    }
  }

  // 4. Each body's Markdown, its links resolved to the pages and static files they name. A link's answer depends
  // only on its source's directory and its target, so resolutions are cached per build; the broken-link report
  // still fires per source, as the reference's does.
  const broken = new Set();
  {
    const staticPaths = new Set(statics.map((f) => f.path));
    const linkCaches = new Map(); // source directory -> Map of target -> { href, broken }
    const resolveLink = (cache, dir, target) => {
      let r = cache.get(target);
      if (r !== undefined) return r;
      if (SCHEME.test(target) || target.startsWith('/') || target.startsWith('#')) {
        r = { href: target, broken: false };
      } else {
        const hash = target.indexOf('#');
        const rel = hash === -1 ? target : target.slice(0, hash);
        const frag = hash === -1 ? '' : target.slice(hash);
        const path = rel === '' ? null : resolvePath(dir, rel);
        if (path !== null && bySource.has(path)) r = { href: `${bySource.get(path).url}${frag}`, broken: false };
        else if (path !== null && staticPaths.has(path)) r = { href: `${base}/${path}${frag}`, broken: false };
        else r = { href: target, broken: true };
      }
      cache.set(target, r);
      return r;
    };
    for (const s of kept) {
      const dir = dirOf(s.path);
      let cache = linkCaches.get(dir);
      if (cache === undefined) {
        cache = new Map();
        linkCaches.set(dir, cache);
      }
      const env = {
        slug,
        link: (target) => {
          const r = resolveLink(cache, dir, target);
          if (r.broken) broken.add(`broken-link ${s.path} -> ${target}`);
          return r.href;
        },
      };
      const md = renderMarkdown(s.body, env);
      s.html = md.html;
      s.toc = md.toc;
      s.excerpt = md.excerpt;
    }
  }

  // 5. The posts, newest first and then by slug; each post's newer and older neighbours.
  const posts = kept.filter((s) => s.post);
  posts.sort((x, y) => byCodeUnits(y.data.date, x.data.date) || byCodeUnits(x.slug, y.slug));
  posts.forEach((p, k) => {
    p.newer = k === 0 ? null : posts[k - 1];
    p.older = k === posts.length - 1 ? null : posts[k + 1];
  });

  // 6. The tags: grouped by their slug, each named as first met in the posts' order, ordered by count then slug.
  const bySlug = new Map();
  const ownTags = (s) => {
    const seen = new Set();
    const out = [];
    for (const name of s.data.tags ?? []) {
      const sl = slug(name);
      if (!seen.has(sl)) {
        seen.add(sl);
        out.push(name);
      }
    }
    return out;
  };
  for (const p of posts) {
    p.tagRefs = [];
    for (const name of ownTags(p)) {
      const sl = slug(name);
      if (!bySlug.has(sl)) bySlug.set(sl, { name, slug: sl, url: `${base}/tags/${sl}/`, posts: [] });
      const tag = bySlug.get(sl);
      tag.posts.push(p);
      p.tagRefs.push(tag);
    }
  }
  for (const s of kept) if (!s.post) s.tagRefs = ownTags(s).map((name) => bySlug.get(slug(name)) ?? { name, slug: slug(name), url: '', posts: [] });
  const tags = [...bySlug.values()].sort((x, y) => y.posts.length - x.posts.length || byCodeUnits(x.slug, y.slug));

  const linkOf = (s) => (s === null ? null : { title: s.data.title, url: s.url, date: s.data.date ?? '', date_long: s.data.date === undefined ? '' : dateLong(s.data.date) });
  const cardOf = (s) => ({
    title: s.data.title,
    url: s.url,
    date: s.data.date ?? '',
    date_long: s.data.date === undefined ? '' : dateLong(s.data.date),
    summary: s.data.summary ?? '',
    excerpt: s.excerpt,
    reading_minutes: Math.max(1, Math.ceil(wordsOf(s.body) / 200)),
    tags: s.tagRefs.map((t) => ({ name: t.name, slug: t.slug, url: t.url })),
  });
  const pageOf = (s, card) => ({
    ...(card ?? cardOf(s)),
    slug: s.slug,
    content: s.html,
    toc: s.toc.map((h) => ({ level: h.level, id: h.id, html: h.html })),
    newer: linkOf(s.newer ?? null),
    older: linkOf(s.older ?? null),
    is_post: s.post,
  });

  // 7. Every page through its layout, the index pages and the tag pages through theirs, then the static files.
  const output = {};
  {
    const cards = new Map(posts.map((p) => [p, cardOf(p)]));
    const site = { title: input.site.title, base_url: base };
    const allTags = tags.map((t) => ({ name: t.name, slug: t.slug, url: t.url, count: t.posts.length }));
    const recent = posts.slice(0, input.site.recent).map((p) => cards.get(p));
    const ctx = { templates };
    const render = (name, vars) => {
      const nodes = templates.get(name);
      return nodes === undefined ? null : renderNodes(nodes, { vars: { site, tags: allTags, recent, ...vars }, parent: null }, ctx, 0);
    };
    for (const s of kept) output[`${s.outDir}/index.html`] = render(s.layout, { page: pageOf(s, cards.get(s)) });
    const per = input.site.per_page;
    const pages = Math.max(1, Math.ceil(posts.length / per));
    const indexUrl = (k) => (k === 1 ? `${base}/` : `${base}/page/${k}/`);
    for (let k = 1; k <= pages; k++) {
      const html = render('index', {
        posts: posts.slice((k - 1) * per, k * per).map((p) => cards.get(p)),
        pager: { number: k, total: pages, url: indexUrl(k), newer_url: k === 1 ? '' : indexUrl(k - 1), older_url: k === pages ? '' : indexUrl(k + 1) },
      });
      if (html !== null) output[k === 1 ? 'index.html' : `page/${k}/index.html`] = html;
    }
    for (const t of tags) {
      const html = render('tag', { tag: { name: t.name, slug: t.slug, url: t.url, count: t.posts.length, posts: t.posts.map((p) => cards.get(p)) } });
      if (html !== null) output[`tags/${t.slug}/index.html`] = html;
    }
    const tagsHtml = render('tags', {});
    if (tagsHtml !== null) output['tags/index.html'] = tagsHtml;
    for (const f of statics) {
      if (Object.hasOwn(output, f.path)) report.push(`shadowed ${f.path}: a built page has its path`);
      else output[f.path] = f.content;
    }
  }

  // 8. The report: every refusal, draft, broken link and template that did not parse, sorted, then the counts.
  {
    const lines = [...report, ...broken].sort(byCodeUnits);
    const pages = kept.filter((s) => !s.post).length;
    lines.push(`built ${pages} pages, ${posts.length} posts, ${tags.length} tags and ${statics.length} static files`);
    output[REPORT_FILE] = `${lines.join('\n')}\n`;
  }
  return output;
}

/** makefun-site 1.0.0's answer for one case's input, faster. */
export function run(input) {
  return build(input);
}
