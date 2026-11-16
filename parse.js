// parse.js — Markdown to HTML, byte-for-byte identical to marked 18.1.3
// with its default options (GFM on, breaks off, pedantic off, async off).
// Built from the CommonMark 0.31.2 and GFM 0.29 specs, then adjusted
// wherever marked itself leaves those specs behind.
//
// The work happens in two sweeps. The block sweep reads the input line
// by line: it walks open containers, starts fresh blocks, gathers the
// raw text of leaf blocks, and collects link reference definitions.
// The inline sweep then renders each leaf's text with a delimiter
// stack in the manner of CommonMark appendix A, bent to marked's
// quirks. parse(markdown) is the only public entry point.

// ---------------------------------------------------------------------------
// Character codes and classes
// ---------------------------------------------------------------------------

const SPC = 32;
const TAB = 9;
const LF = 10;
const CR = 13;
const LT = 60;
const GT = 62;
const AMP = 38;
const DQ = 34;
const SQ = 39;
const BSL = 92;
const BT = 96;
const STAR = 42;
const US = 95;
const TILDE = 126;
const LB = 91;
const RB = 93;
const BANG = 33;
const LP = 40;
const RP = 41;
const HASH = 35;
const SL = 47;

// ASCII punctuation, per CommonMark: !"#$%&'()*+,-./:;<=>?@[\]^_`{|}~
// Four ranges cover the set.
function asciiPunct(code) {
  return (code >= 33 && code <= 47) || (code >= 58 && code <= 64) ||
    (code >= 91 && code <= 96) || (code >= 123 && code <= 126);
}

// A character counts as punctuation for marked when it is neither a
// letter, a digit, nor whitespace. ASCII takes the range test above;
// anything else goes through cached Unicode regexes (categories P
// and S).
const PUNCT_RE = /[\p{P}\p{S}]/u;
const ALNUM_RE = /[\p{L}\p{N}]/u;
const PUNCT_WS_RE = /[\s\p{P}\p{S}]/u;

function isPunctChar(chr) { // chr: a one-character string
  const cp = chr.charCodeAt(0);
  return cp < 128 ? asciiPunct(cp) : PUNCT_RE.test(chr);
}

function isPunctOrSpace(chr) {
  const cp = chr.charCodeAt(0);
  if (cp >= 128) return PUNCT_WS_RE.test(chr);
  return asciiPunct(cp) || wsCode(cp);
}

function isAlnumChar(chr) {
  const cp = chr.charCodeAt(0);
  if (cp >= 128) return ALNUM_RE.test(chr);
  return (cp >= 48 && cp <= 57) || (cp >= 65 && cp <= 90) || (cp >= 97 && cp <= 122);
}

const blankCode = (code) => code === 32 || code === 9;
const wsCode = (code) =>
  code === 32 || code === 9 || code === 10 || code === 11 || code === 12 || code === 13;

const hexCode = (code) =>
  (code >= 48 && code <= 57) || (code >= 65 && code <= 70) || (code >= 97 && code <= 102);

// ---------------------------------------------------------------------------
// HTML escaping
// ---------------------------------------------------------------------------
// marked's escape(): with forceAmp every & < > " ' is escaped; without
// it, < > " ' are escaped and & only when it does not open a valid
// reference.
const ESCAPE_MAP = {
  '&': '&amp;',
  '<': '&lt;',
  '>': '&gt;',
  '"': '&quot;',
  "'": '&#39;',
};

function escapeHtml(tx, forceAmp) {
  const n = tx.length;
  const parts = [];
  let cut = 0;
  let changed = false;
  for (let i = 0; i < n; i++) {
    const chr = tx.charCodeAt(i);
    let sub = null;
    if (chr === 38) { // &
      if (forceAmp || !entityAt(tx, i)) sub = '&amp;';
    } else if (chr === 60) sub = '&lt;';
    else if (chr === 62) sub = '&gt;';
    else if (chr === 34) sub = '&quot;';
    else if (chr === 39) sub = '&#39;';
    if (sub === null) continue;
    changed = true;
    if (cut < i) parts.push(tx.slice(cut, i));
    parts.push(sub);
    cut = i + 1;
  }
  if (!changed) return tx;
  if (cut < n) parts.push(tx.slice(cut));
  return parts.join('');
}

// Does the '&' at `at` begin a well-formed character reference? A
// numeric one is &#digits; (1-7 digits) or &#xhex; (1-6 hex digits);
// a named one is &word; with word drawn from [0-9A-Za-z_]+.
function entityAt(tx, at) {
  const n = tx.length;
  let j = at + 1;
  if (j >= n) return false;
  if (tx.charCodeAt(j) === 35) { // #
    j++;
    let hex = false;
    if (j < n && (tx.charCodeAt(j) === 120 || tx.charCodeAt(j) === 88)) {
      hex = true;
      j++;
    }
    const cap = hex ? 6 : 7;
    let digits = 0;
    for (; j < n; j++) {
      const c = tx.charCodeAt(j);
      const ok = hex ? hexCode(c) : (c >= 48 && c <= 57);
      if (!ok) break;
      digits++;
    }
    if (digits === 0 || digits > cap) return false;
    return j < n && tx.charCodeAt(j) === 59; // ;
  }
  let letters = 0;
  for (; j < n; j++) {
    const code = tx.charCodeAt(j);
    const wordish = (code >= 48 && code <= 57) || (code >= 65 && code <= 90) ||
      (code >= 97 && code <= 122) || code === 95;
    if (!wordish) break;
    letters++;
  }
  return letters > 0 && j < n && tx.charCodeAt(j) === 59;
}

// ---------------------------------------------------------------------------
// Numeric character reference decoding
// ---------------------------------------------------------------------------
// This mirrors marked's unescape(). It only runs when the string holds
// at least one well-formed numeric reference. &#123; and &#xAB; decode
// (1-7 decimal digits, 1-6 hex digits, ';' mandatory). A code point of
// 0, above 0x10FFFF, or inside the surrogate range becomes U+FFFD; 38
// becomes '&amp;'. A bare '&' that starts no valid reference becomes
// '&amp;' too. Named references are never decoded here — they pass
// through untouched.
const NUMREF_RE = /&#(?:\d{1,7}|[Xx][A-Fa-f0-9]{1,6});/;

// Reads a numeric reference starting at the '&' in position `i`.
// Returns { value, after } with `after` just past the ';', or null
// when no well-formed numeric reference starts there.
function readNumericRef(tx, i) {
  const n = tx.length;
  let j = i + 1;
  if (j >= n || tx.charCodeAt(j) !== 35) return null;
  j++;
  let hex = false;
  if (j < n && (tx.charCodeAt(j) === 120 || tx.charCodeAt(j) === 88)) {
    hex = true;
    j++;
  }
  const cap = hex ? 6 : 7;
  let digits = 0;
  let v = 0;
  for (; j < n && digits < cap; j++) {
    const code = tx.charCodeAt(j);
    if (hex) {
      if (!hexCode(code)) break;
      v = v * 16 + (code <= 57 ? code - 48 : (code <= 70 ? code - 55 : code - 87));
    } else {
      if (code < 48 || code > 57) break;
      v = v * 10 + (code - 48);
    }
    digits++;
  }
  if (digits < 1 || digits > cap) return null;
  if (j >= n || tx.charCodeAt(j) !== 59) return null;
  return { value: v, after: j + 1 };
}

function decodeNumRefs(tx) {
  if (!NUMREF_RE.test(tx)) return tx;
  const n = tx.length;
  const parts = [];
  let cut = 0;
  let i = 0;
  while (i < n) {
    if (tx.charCodeAt(i) !== 38) { i++; continue; } // not &
    const ref = readNumericRef(tx, i);
    if (ref) {
      if (cut < i) parts.push(tx.slice(cut, i));
      const val = ref.value;
      if (val === 0 || val > 0x10FFFF || (val >= 0xD800 && val <= 0xDFFF)) parts.push('\uFFFD');
      else if (val === 38) parts.push('&amp;');
      else parts.push(String.fromCodePoint(val));
      i = ref.after;
      cut = i;
      continue;
    }
    // No numeric reference here: a bare '&' is escaped unless it
    // opens some other valid reference.
    if (!entityAt(tx, i)) {
      if (cut < i) parts.push(tx.slice(cut, i));
      parts.push('&amp;');
      i++;
      cut = i;
      continue;
    }
    i++;
  }
  if (cut === 0) return tx;
  if (cut < n) parts.push(tx.slice(cut));
  return parts.join('');
}

// ---------------------------------------------------------------------------
// URL cleaning and label folding
// ---------------------------------------------------------------------------
// marked's clean: encodeURI, then turn %25 back into %. encodeURI
// throws on lone surrogates, so null comes back then and the caller
// renders the link as plain text.
function cleanUrl(r) {
  try {
    return encodeURI(r).replace(/%25/g, '%');
  } catch (err) {
    return null;
  }
}

// Fold a link label for reference lookup: trim, collapse each
// whitespace run to one space, then case-fold the way marked does —
// toLowerCase().toUpperCase().toLowerCase(), which folds ẞ, ß and SS
// together.
function foldLabel(lbl) {
  return lbl.trim().replace(/\s+/g, ' ').toLowerCase().toUpperCase().toLowerCase();
}

// ---------------------------------------------------------------------------
// The block tree
// ---------------------------------------------------------------------------
// CommonMark's phase 1/2 container algorithm, plus GFM tables. A block
// node carries its kind, its text, its children, and the bookkeeping
// each kind needs (fence details, list markers, table rows).

const BLOCK_TAGS = new Set([
  'address', 'article', 'aside', 'base', 'basefont', 'blockquote', 'body',
  'caption', 'center', 'col', 'colgroup', 'dd', 'details', 'dialog', 'dir',
  'div', 'dl', 'dt', 'fieldset', 'figcaption', 'figure', 'footer', 'form',
  'frame', 'frameset', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'head', 'hdr',
  'hr', 'out', 'iframe', 'legend', 'li', 'link', 'main', 'menu', 'menuitem',
  'meta', 'nav', 'noframes', 'ol', 'optgroup', 'option', 'p', 'param',
  'search', 'section', 'summary', 'table', 'tbody', 'td', 'tfoot', 'th',
  'thead', 'title', 'tr', 'track', 'ul',
]);
// Tag names that open an HTML block of type 1.
const TYPE1_TAGS = new Set(['script', 'pre', 'style', 'textarea']);

function newBlock(kind) {
  return {
    kind, parent: null, children: [], open: true, text: '',
    startLine: 0, endLine: 0, level: 0, info: '',
    fenceChar: '', fenceLen: 0, fenceIndent: 0, fenced: false,
    htmlType: 0, listType: '', bullet: '', delim: '',
    start: 1, tight: true, markerOffset: 0, contentPad: 0,
    checked: -1, lastNonBlank: null,
    header: null, align: null, rows: null, delimLine: -1,
  };
}

// The container's last child, but only while that child is still open.
function lastOpenChild(ctn) {
  const list = ctn.children;
  if (list.length === 0) return null;
  const rest = list[list.length - 1];
  return rest.open ? rest : null;
}

// Leaf blocks collect lines verbatim instead of opening children.
function leafKind(kind) {
  return kind === 'code_block' || kind === 'html_block' ||
    kind === 'paragraph' || kind === 'table';
}

// Which child kinds may sit under a given parent kind.
function mayNest(parentKind, childKind) {
  if (parentKind === 'document') return childKind !== 'item';
  if (parentKind === 'list') return childKind === 'item';
  if (parentKind === 'blockquote' || parentKind === 'item') return childKind !== 'item';
  return false;
}

// --- line cursor -----------------------------------------------------------
// A cursor follows one line: idx is the string index, col the visual
// column, and halfTab records that a tab was only partly eaten, so its
// remaining width still counts as spaces while the index still points
// at the tab itself.
function newCursor() {
  return {
    idx: 0, col: 0, halfTab: false, tabUsed: 0,
    tabCut: false,
    nextNonSpace: 0, nextNonSpaceCol: 0, indent: 0,
    indented: false, blank: false,
  };
}

function charAtIdx(ln, idx) {
  return idx < ln.length ? ln.charCodeAt(idx) : -1;
}

function measureIndent(ln, cur) {
  let idx = cur.idx;
  let col = cur.col;
  while (idx < ln.length) {
    const chr = ln.charCodeAt(idx);
    if (chr === 32) { idx++; col++; }
    else if (chr === 9) { idx++; col += 4 - (col % 4); }
    else break;
  }
  cur.blank = idx >= ln.length;
  cur.nextNonSpace = idx;
  cur.nextNonSpaceCol = col;
  cur.indent = col - cur.col;
  cur.indented = cur.indent >= 4;
}

function advanceCursor(ln, cur, n, byCol) {
  while (n > 0 && cur.idx < ln.length) {
    const chr = ln.charCodeAt(cur.idx);
    if (chr !== 9) {
      cur.halfTab = false;
      cur.tabUsed = 0;
      cur.tabCut = false;
      cur.idx += 1;
      cur.col += 1;
      n -= 1;
      continue;
    }
    const tabW = 4 - (cur.col % 4);
    if (!byCol) {
      cur.halfTab = false;
      cur.tabUsed = 0;
      cur.tabCut = false;
      cur.col += tabW;
      cur.idx += 1;
      n -= 1;
      continue;
    }
    const partial = tabW > n;
    cur.halfTab = partial;
    const take = partial ? n : tabW;
    cur.tabUsed = partial ? cur.tabUsed + take : 0;
    if (!partial) cur.tabCut = false;
    cur.col += take;
    cur.idx += partial ? 0 : 1;
    n -= take;
  }
}

function jumpToContent(cur) {
  cur.idx = cur.nextNonSpace;
  cur.col = cur.nextNonSpaceCol;
  cur.halfTab = false;
  cur.tabUsed = 0;
  cur.tabCut = false;
}

// Spaces left in a partly eaten tab.
function tabRemainder(cur) {
  return 4 - (cur.col % 4);
}

// The line's text from the cursor, expanding a partly eaten tab.
function tailText(ln, cur) {
  if (!cur.halfTab) return ln.slice(cur.idx);
  return ' '.repeat(tabRemainder(cur)) + ln.slice(cur.idx + 1);
}

// --- block continuation (phase 1) ------------------------------------------
// Each matcher returns 0 when its container accepts the line, 1 when it
// does not, and 2 when a fenced code block was closed by this line.
const CLOSE_FENCE_RE = /^(?:`{3,}|~{3,})(?=[ \t]*$)/;

function matchBlockquote(st, ctn) {
  const src = st.line;
  const cur = st.cursor;
  if (cur.indented || charAtIdx(src, cur.nextNonSpace) !== 62) return 1; // >
  jumpToContent(cur);
  advanceCursor(src, cur, 1, false);
  st.quoteConsumed = true;
  const nx = charAtIdx(src, cur.idx);
  if (nx === 32 || nx === 9) {
    advanceCursor(src, cur, 1, true);
    // A tab cut here sits at the start of the quote content, so its
    // width is measured from the quote's content column (2), not the
    // raw column — feedLine needs to know this cut came from the `>`.
    if (cur.halfTab) cur.tabCut = true;
  }
  return 0;
}

function matchListItem(st, ctn) {
  const src = st.line;
  const cur = st.cursor;
  if (cur.indent >= ctn.markerOffset + ctn.contentPad) {
    advanceCursor(src, cur, ctn.markerOffset + ctn.contentPad, true);
    return 0;
  }
  if (cur.blank && ctn.children.length > 0) {
    jumpToContent(cur);
    return 0;
  }
  // Marked quirk: a fenced code block inside a list item swallows even
  // unindented lines (its list tokenizer takes the whole fence), but
  // only once the fence already holds content. An empty fence lets an
  // unindented line end the item (and the fence); the next fence
  // marker then opens a fresh block at the outer level. The exception
  // is a fence inside a blockquote: a blockquote that does not match
  // this line (no `>`) stops the fence from taking it, so the item
  // must fail and the line can start a sibling item in the parent list.
  let tip = ctn;
  let sawQuote = false;
  for (let kid = lastOpenChild(tip); kid; kid = lastOpenChild(tip)) {
    tip = kid;
    if (tip.kind === 'blockquote') sawQuote = true;
  }
  if (tip.kind === 'code_block' && tip.fenced && !cur.blank && !sawQuote) {
    // The opener line (the info string) is the first line of `text`;
    // a newline before the end of `text` means a content line was fed.
    const nl = tip.text.indexOf('\n');
    if (nl >= 0 && nl < tip.text.length - 1) return 0;
  }
  return 1;
}

function matchCodeBlock(st, ctn) {
  const src = st.line;
  const cur = st.cursor;
  if (!ctn.fenced) {
    // Indented code: four columns keep the line, a blank line keeps it
    // too, anything else ends the block.
    if (cur.indent >= 4) {
      advanceCursor(src, cur, 4, true);
      return 0;
    }
    if (cur.blank) jumpToContent(cur);
    else return 1;
    return 0;
  }
  const fenceCh = ctn.fenceChar.charCodeAt(0);
  if (cur.indent <= 3 && charAtIdx(src, cur.nextNonSpace) === fenceCh) {
    const rest = src.slice(cur.nextNonSpace);
    const closer = CLOSE_FENCE_RE.exec(rest);
    if (closer && closer[0].length >= ctn.fenceLen) {
      ctn.endLine = st.lineNumber;
      closeBlock(st, ctn, st.lineNumber);
      return 2;
    }
  }
  // Up to fenceIndent spaces are stripped from content lines, but only
  // for backtick fences — marked does NOT strip the indent for tilde
  // fences. When the strip itself cuts into a tab, marked drops the
  // whole tab instead of leaving the remainder as spaces. (A tab
  // already partly eaten by a container marker, e.g. `>`, keeps its
  // remainder.)
  let toStrip = ctn.fenceChar === '`' ? ctn.fenceIndent : 0;
  const hadPartial = cur.halfTab;
  while (toStrip > 0) {
    const c = charAtIdx(src, cur.idx);
    if (c !== 32 && c !== 9) break;
    advanceCursor(src, cur, 1, true);
    toStrip--;
  }
  if (cur.halfTab && !hadPartial) {
    cur.col += tabRemainder(cur);
    cur.idx++;
    cur.halfTab = false;
    cur.tabUsed = 0;
    cur.tabCut = false;
  }
  return 0;
}

function matchHtmlBlock(st, ctn) {
  const cur = st.cursor;
  if (!cur.blank) return 0;
  return (ctn.htmlType === 6 || ctn.htmlType === 7) ? 1 : 0;
}

function matchParagraph(st, ctn) {
  const src = st.line;
  const cur = st.cursor;
  // A `>` line that leaves only spaces still contributes those spaces
  // as paragraph content (marked keeps `>  ` as a ` ` line); a bare
  // `>` or `> ` line (nothing left) is blank and ends the paragraph.
  if (cur.blank && st.quoteConsumed && cur.idx < src.length) return 0;
  return cur.blank ? 1 : 0;
}

function matchTableBlock(st, ctn) {
  if (st.lineNumber === ctn.delimLine) return 0;
  return lineEndsTable(st) ? 1 : 0;
}

const CONTAINER_MATCH = {
  blockquote: matchBlockquote,
  item: matchListItem,
  code_block: matchCodeBlock,
  html_block: matchHtmlBlock,
  paragraph: matchParagraph,
  table: matchTableBlock,
};

function matchContainer(st, ctn) {
  const kind = ctn.kind;
  if (kind === 'document' || kind === 'list') return 0;
  const fn = CONTAINER_MATCH[kind];
  return fn ? fn(st, ctn) : 1; // heading, thematic_break
}

// Does the current line (at the cursor) start a block that would end a
// table row run? (blank, indented code, ATX, hr, blockquote, fence,
// list, or an HTML block of type 1-6)
function lineEndsTable(st) {
  const src = st.line;
  const cur = st.cursor;
  const rest = src.slice(cur.idx);
  // Marked's table row regex ends the table on a "blank" line of
  // spaces only (` *\n`), or an indented-code line
  // (`(?: {4}| {0,3}\t)[^\n]`). A lone tab (or space+tab) is NOT
  // blank: it becomes an empty row.
  if (/^ *$/.test(rest)) return true;
  if (/^(?: {4}| {0,3}\t)[^\n]/.test(rest)) return true;
  const stripped = src.slice(cur.nextNonSpace);
  if (stripped === '') return false;
  const fst = stripped.charCodeAt(0);
  if (fst === 62) return true; // >
  if (ATX_RE.test(stripped)) return true;
  if (HR_RE.test(stripped)) return true;
  if (FENCE_RE.test(stripped)) return true;
  if (isHtmlStart(stripped)) return true;
  return startsListMarker(stripped);
}

// True when `stripped` starts a list marker: a bullet followed by a
// space/tab, or an ordered `1.` / `1)` followed by a space/tab.
function startsListMarker(stripped) {
  const fst = stripped.charCodeAt(0);
  if (fst === 42 || fst === 43 || fst === 45) { // * + -
    const after = stripped.length > 1 ? stripped.charCodeAt(1) : -1;
    return after === 32 || after === 9;
  }
  if (fst !== 49) return false; // 1.
  const ord = /^1[.)]/.exec(stripped);
  if (!ord) return false;
  const after = stripped.length > ord[0].length ? stripped.charCodeAt(ord[0].length) : -1;
  return after === 32 || after === 9;
}

// --- closing blocks -----------------------------------------------------------
// Tight/loose for a list: the list is loose when two of its items, or
// two blocks inside one item, are separated by a blank line — that is,
// the later block starts more than one line after the earlier one ends.
// True when block `b` starts more than one line after block `a`
// ends — a blank line separates them.
function gapBetween(a, b) {
  return b.startLine > a.endLine + 1;
}

function finishListBlock(st, blk) {
  const list = blk.children;
  let tight = true;
  for (let i = 0; i < list.length && tight; i++) {
    const it = list[i];
    if (i + 1 < list.length && gapBetween(it, list[i + 1])) {
      tight = false;
      break;
    }
    const inner = it.children;
    for (let k = 0; k + 1 < inner.length; k++) {
      if (gapBetween(inner[k], inner[k + 1])) {
        tight = false;
        break;
      }
    }
  }
  blk.tight = tight;
  blk.endLine = list.length ? list[list.length - 1].endLine : blk.startLine;
}

function finishCodeBlock(st, blk, lineNumber) {
  if (!blk.fenced) {
    // Indented code: drop trailing blank lines.
    const out = blk.text.split('\n');
    while (out.length && /^[ \t]*$/.test(out[out.length - 1])) out.pop();
    blk.text = out.join('\n') + '\n';
    blk.endLine = blk.lastNonBlank != null ? blk.lastNonBlank : blk.startLine;
    return;
  }
  const body = blk.text;
  const firstNl = body.indexOf('\n');
  const opener = firstNl < 0 ? body : body.slice(0, firstNl);
  blk.info = unescapeBackslash(opener).trim();
  blk.text = firstNl < 0 ? '' : body.slice(firstNl + 1);
  // Marked's fenced content has no trailing \n: the \n before the
  // closing fence is the separator, not content.
  if (blk.text.endsWith('\n')) blk.text = blk.text.slice(0, -1);
  if (blk.endLine < blk.startLine) blk.endLine = lineNumber;
}

function finishHtmlBlock(st, blk) {
  if (blk.text.endsWith('\n')) blk.text = blk.text.slice(0, -1);
  // Marked renders an HTML block with a trailing \n unless the line
  // after the block is blank — and, when the block is the last thing
  // in the document, unless the source ended without \n. For types
  // 1-5 (closed by a pattern) only a truly empty line swallows the
  // trailing \n; a whitespace-only line does not. For types 6-7
  // (ended by a blank line) any whitespace-only line swallows it.
  const following = st.lines[blk.endLine + 1];
  const followingBlank = following !== undefined &&
    (blk.htmlType <= 5 ? following === '' : /^[ \t]*$/.test(following));
  const eofNoNl = blk.endLine >= st.lines.length - 1 && !st.endsWithNewline;
  blk.noTrailNewline = followingBlank || eofNoNl;
}

function finishContainerBlock(st, blk) {
  const list = blk.children;
  // Keep the furthest line the container reached: an empty `>` line
  // extends it even though it adds no child content.
  const lastEnd = list.length ? list[list.length - 1].endLine : blk.startLine;
  blk.endLine = Math.max(lastEnd, blk.endLine);
}

function closeBlock(st, blk, lineNumber) {
  const up = blk.parent;
  blk.open = false;
  if (blk.kind === 'list') finishListBlock(st, blk);
  else if (blk.kind === 'code_block') finishCodeBlock(st, blk, lineNumber);
  else if (blk.kind === 'html_block') finishHtmlBlock(st, blk);
  else if (blk.kind === 'blockquote' || blk.kind === 'item' || blk.kind === 'document') finishContainerBlock(st, blk);
  st.tip = up;
}

// --- adding children / closing unmatched containers ---------------------------
function addChild(st, kind, off) {
  while (!mayNest(st.tip.kind, kind)) {
    closeBlock(st, st.tip, st.lineNumber - 1);
  }
  const blk = newBlock(kind);
  blk.startLine = st.lineNumber;
  blk.endLine = st.lineNumber;
  blk.parent = st.tip;
  st.tip.children.push(blk);
  st.tip = blk;
  return blk;
}

function closeUnmatched(st) {
  if (st.allClosed) return;
  while (st.oldTip !== st.lastMatched) {
    const up = st.oldTip.parent;
    closeBlock(st, st.oldTip, st.lineNumber - 1);
    st.oldTip = up;
  }
  st.allClosed = true;
}

// --- feeding a line to the current leaf ---------------------------------------
function feedLine(st) {
  const lf = st.tip;
  if (lf.kind === 'table') {
    // Header and delimiter lines are not rows.
    if (st.lineNumber <= lf.delimLine) return;
    lf.rows.push(tailText(st.line, st.cursor));
    lf.endLine = st.lineNumber;
    return;
  }
  if (st.cursor.halfTab) {
    st.cursor.idx++;
    if (st.cursor.tabCut) {
      // The tab was partly eaten by a `>` marker, so its width is
      // measured from where it started in the local column system, not
      // from the raw column: the tab began `tabUsed` columns before
      // the current content column.
      const base = tabOrigin(st, lf);
      const origin = base - st.cursor.tabUsed;
      const width = 4 - (((origin % 4) + 4) % 4);
      lf.text += ' '.repeat(Math.max(0, width - st.cursor.tabUsed));
    } else {
      // Cut by a list item indent (or similar): the remainder is
      // measured from the raw column.
      lf.text += ' '.repeat(tabRemainder(st.cursor));
    }
  } else if (st.cursor.col > 0 && insideContainer(lf)) {
    // When a list item or blockquote removed an indent from the line,
    // marked expands leading tabs to spaces (its text extraction
    // expands the leading whitespace before slicing the indent). At
    // the top level, with no such ancestor, a leading tab is kept.
    // Every tab in the leading whitespace run expands to the next
    // multiple of 4; spaces stay as they are.
    let col = tabOrigin(st, lf);
    let off = st.cursor.idx;
    let prefix = '';
    let expanded = false;
    for (; off < st.line.length; off++) {
      const c = st.line.charCodeAt(off);
      if (c === 32) { prefix += ' '; col++; continue; }
      if (c !== 9) break;
      const width = 4 - (col % 4);
      prefix += ' '.repeat(width);
      col += width;
      expanded = true;
    }
    if (expanded) {
      lf.text += prefix;
      st.cursor.idx = off;
      st.cursor.col = col;
    }
  }
  lf.text += st.line.slice(st.cursor.idx) + '\n';
  lf.endLine = st.lineNumber;
  if (!st.cursor.blank && lf.kind === 'code_block' && !lf.fenced) lf.lastNonBlank = st.lineNumber;
}

// True when the block sits inside a list item or a blockquote — a
// container whose text extraction expands leading tabs.
function insideContainer(nd) {
  let up = nd.parent;
  while (up) {
    if (up.kind === 'item' || up.kind === 'blockquote') return true;
    up = up.parent;
  }
  return false;
}

// The column a tab expands from in a fenced code block's content line.
// Marked re-lexes blockquote content, so when the innermost container
// is a blockquote nested inside another blockquote or a list item, the
// tab expands from column 2 (the `> ` marker) whatever the outer
// indents are; a lone top-level blockquote keeps its full column (its
// leading spaces count), and a list item innermost keeps the full
// column.
function tabOrigin(st, nd) {
  let up = nd.parent, quotes = 0, inItem = false;
  while (up) {
    if (up.kind === 'blockquote') quotes++;
    if (up.kind === 'item') inItem = true;
    up = up.parent;
  }
  // The innermost container decides.
  up = nd.parent;
  while (up) {
    if (up.kind === 'blockquote') return (quotes > 1 || inItem) ? 2 : st.cursor.col;
    if (up.kind === 'item') return st.cursor.col;
    up = up.parent;
  }
  return st.cursor.col;
}

// --- block start helpers ------------------------------------------------------
function isBlockStarter(src, at) {
  if (at >= src.length) return false;
  const chr = src.charCodeAt(at);
  return chr === 35 || chr === 96 || chr === 126 || chr === 42 || chr === 43 || chr === 95 ||
    chr === 61 || chr === 60 || chr === 62 || chr === 48 || chr === 49 || chr === 50 ||
    chr === 51 || chr === 52 || chr === 53 || chr === 54 || chr === 55 || chr === 56 ||
    chr === 57 || chr === 45;
}

const ATX_RE = /^#{1,6}(?:[ \t]+|$)/;
const FENCE_RE = /^`{3,}(?!.*`)|^~{3,}/;
const SETEXT_RE = /^(?:=+|-+)[ \t]*$/;
const HR_RE = /^(?:\*[ \t]*){3,}$|^(?:_[ \t]*){3,}$|^(?:-[ \t]*){3,}$/;
const BULLET_RE = /^[*+-]/;
const ORDERED_RE = /^(\d{1,9})([.)])/;

// Which HTML block type a line opens (1-7), or 0 when it opens none.
// The rules follow marked's block-start test, except type 7: any tag
// name counts here, without the inline-tag exclusion.
function htmlBlockType(tx) {
  // tx starts at '<'
  if (tx.length < 2) return 0;
  const ch2 = tx.charCodeAt(1);
  if (/^<(script|pre|style|textarea)(?:[\s>]|$)/i.test(tx)) return 1; // type 1
  if (tx.startsWith('<!--')) return 2; // type 2
  if (ch2 === 63) return 3; // type 3: <?
  if (ch2 === 33 && tx.length > 2) {
    // type 4: <! followed by a letter
    const ch3 = tx.charCodeAt(2);
    const isLetter = (ch3 >= 65 && ch3 <= 90) || (ch3 >= 97 && ch3 <= 122);
    if (isLetter) return 4;
  }
  if (tx.startsWith('<![CDATA[')) return 5; // type 5
  // type 6: a block-level tag, open or close
  const openTag = /^<\/?([A-Za-z][A-Za-z0-9-]*)/.exec(tx);
  if (openTag) {
    const name = openTag[1].toLowerCase();
    const isBlock = BLOCK_TAGS.has(name) || /^h[1-6]$/.test(name);
    if (isBlock) {
      const rest = tx.slice(openTag[0].length);
      const first = rest === '' ? -1 : rest.charCodeAt(0);
      const endsHere = first === -1 || first === 32 || first === 9 ||
        first === 10 || first === 47 || first === 62;
      if (endsHere) return 6;
    }
  }
  // type 7: any other tag, alone on the line. A close tag cannot carry
  // attributes — `</a href="foo">` is not a tag, it is a paragraph.
  const closeRe = /^<\/([A-Za-z][A-Za-z0-9-]*)[ \t]*>/;
  const openRe = /^<([A-Za-z][A-Za-z0-9-]*)((?: +[A-Za-z_:][\w.:-]*(?: *= *"[^"\n]*"| *= *'[^'\n]*'| *= *[^\s"'=<>`]+)?)*) *\/?>/;
  const anyTag = tx.startsWith('</') ? closeRe.exec(tx) : openRe.exec(tx);
  if (anyTag) {
    const name = anyTag[1].toLowerCase();
    // script/pre/style/textarea belong to type 1
    if (TYPE1_TAGS.has(name)) return 0;
    const rest = tx.slice(anyTag[0].length);
    if (/^[ \t]*$/.test(rest)) return 7;
  }
  return 0;
}

// What closes each HTML block type (1-5); types 6-7 end at a blank line.
const HTML_CLOSE_RE = [
  null,
  /<\/(?:script|pre|style|textarea)>/i,
  /-->/,
  /\?>/,
  />/,
  /\]\]>/,
];

function isHtmlStart(tx) {
  // The type 1-6 start condition, used for paragraph interruption and
  // for ending table row runs.
  if (tx.length < 1 || tx.charCodeAt(0) !== 60) return false;
  const kind = htmlBlockType(tx);
  return kind >= 1 && kind <= 6;
}

// --- list markers --------------------------------------------------------------
// True when the block sits inside a list item, at any depth. Marked
// lets a nested ordered list interrupt a paragraph inside a list item
// no matter what number it starts with (its list tokenizer ends the
// item text at the nested marker); at the top level only a list
// starting with 1 may interrupt.
function insideItem(nd) {
  let up = nd.parent;
  while (up) {
    if (up.kind === 'item') return true;
    up = up.parent;
  }
  return false;
}

function scanMarker(st, ctn) {
  const src = st.line;
  const cur = st.cursor;
  if (cur.indent >= 4) return null;
  const rest = src.slice(cur.nextNonSpace);
  let marker = BULLET_RE.exec(rest);
  let data = null;
  if (marker) {
    data = { type: 'bullet', bullet: marker[0], delim: null, start: null, markerOffset: cur.indent };
  } else if ((marker = ORDERED_RE.exec(rest)) && (ctn.kind !== 'paragraph' || marker[1] === '1' || insideItem(ctn))) {
    data = { type: 'ordered', bullet: null, delim: marker[2], start: parseInt(marker[1], 10), markerOffset: cur.indent };
  } else {
    return null;
  }
  const after = charAtIdx(src, cur.nextNonSpace + marker[0].length);
  if (!(after === -1 || after === 9 || after === 32)) return null;
  // An empty list item cannot interrupt a paragraph.
  if (ctn.kind === 'paragraph') {
    let hasText = false;
    for (let idx = cur.nextNonSpace + marker[0].length; idx < src.length; idx++) {
      const chr = src.charCodeAt(idx);
      if (chr !== 32 && chr !== 9) { hasText = true; break; }
    }
    if (!hasText) return null;
  }
  jumpToContent(cur);
  advanceCursor(src, cur, marker[0].length, false);
  const col0 = cur.col;
  const off0 = cur.idx;
  let chr = charAtIdx(src, cur.idx);
  while (cur.col - col0 < 5 && (chr === 32 || chr === 9)) {
    advanceCursor(src, cur, 1, true);
    chr = charAtIdx(src, cur.idx);
  }
  const isBlank = cur.idx >= src.length;
  const gapW = cur.col - col0;
  if (gapW >= 5 || gapW < 1 || isBlank) {
    data.contentPad = marker[0].length + 1;
    cur.col = col0;
    cur.idx = off0;
    cur.halfTab = false;
    const ch2 = charAtIdx(src, cur.idx);
    if (ch2 === 32 || ch2 === 9) advanceCursor(src, cur, 1, true);
  } else {
    data.contentPad = marker[0].length + gapW;
  }
  return data;
}

function sameListType(listData, itemData) {
  return listData.type === itemData.type &&
    listData.delim === itemData.delim &&
    listData.bullet === itemData.bullet;
}

// --- tables -------------------------------------------------------------------
// Counts the run of backslashes ending just before position `i`.
function countBackslashes(tx, i) {
  let n = 0;
  for (let j = i - 1; j >= 0 && tx.charCodeAt(j) === 92; j--) n++;
  return n;
}

// Split a table row into cells: an unescaped pipe splits, empty cells
// at the ends are dropped, cells are trimmed, and \| becomes |.
function splitTableRow(tx, want) {
  // Tag unescaped pipes with a leading space so split(' |') does the job.
  const parts = [];
  for (let i = 0; i < tx.length; i++) {
    if (tx.charCodeAt(i) !== 124) { // |
      parts.push(tx[i]);
      continue;
    }
    parts.push(countBackslashes(tx, i) % 2 === 1 ? '|' : ' |');
  }
  const out = parts.join('').split(' |');
  if (out.length && out[0].trim() === '') out.shift();
  if (out.length && out[out.length - 1].trim() === '') out.pop();
  if (want != null) {
    if (out.length > want) out.length = want;
    else while (out.length < want) out.push('');
  }
  return out.map((cell) => cell.trim().replace(/\\\|/g, '|'));
}

const DELIM_CELL_RE = /^:?-+:?$/;
function parseDelimiterRow(r) {
  // r is the delimiter row with containers stripped. Returns
  // {align, count}, or null when the row is not a delimiter row.
  if (!/[:|]/.test(r)) return null;
  let body = r.trim();
  if (body.startsWith('|')) body = body.slice(1);
  if (body.endsWith('|')) body = body.slice(0, -1);
  const chunks = body.split('|');
  const align = [];
  for (const chunk of chunks) {
    const trimmed = chunk.trim();
    if (!DELIM_CELL_RE.test(trimmed)) return null;
    if (/^:-+:$/.test(trimmed)) align.push('center');
    else if (/^-+:$/.test(trimmed)) align.push('right');
    else if (/^:-+$/.test(trimmed)) align.push('left');
    else align.push(null);
  }
  return { align, count: chunks.length };
}

// Dry-run container matching on a line, used for the table lookahead:
// returns the cursor left after matching the containers, or null when
// a container fails to match.
function probeContainers(st, src, stopAt) {
  const cur = newCursor();
  // Walk the ancestor chain from the document down to `stopAt`,
  // stripping each container's prefix from the delimiter line. Never
  // descend below `stopAt`: its children are the blocks phase 1
  // already rejected for the header line, so the delimiter belongs to
  // `stopAt` itself.
  const path = [];
  for (let up = stopAt || st.doc; up && up.kind !== 'document'; up = up.parent) {
    path.unshift(up);
  }
  let current = st.doc;
  for (const step of path) {
    current = step;
    measureIndent(src, cur);
    if (step.kind === 'document' || step.kind === 'list') continue;
    if (step.kind === 'blockquote') {
      if (cur.indented || charAtIdx(src, cur.nextNonSpace) !== 62) return null;
      jumpToContent(cur);
      advanceCursor(src, cur, 1, false);
      const c = charAtIdx(src, cur.idx);
      if (c === 32 || c === 9) advanceCursor(src, cur, 1, true);
      continue;
    }
    if (step.kind !== 'item') continue;
    const needed = step.markerOffset + step.contentPad;
    if (cur.indent >= needed) {
      advanceCursor(src, cur, needed, true);
      continue;
    }
    if (cur.blank && step.children.length > 0) {
      jumpToContent(cur);
      continue;
    }
    return null;
  }
  return { ctn: current, cur };
}

// Drop backslash escapes: \ followed by ASCII punctuation becomes the
// punctuation itself.
function unescapeBackslash(tx) {
  if (!tx.includes('\\')) return tx;
  const parts = [];
  let start = 0;
  for (let i = 0; i < tx.length; i++) {
    if (tx.charCodeAt(i) === 92 && i + 1 < tx.length && asciiPunct(tx.charCodeAt(i + 1))) {
      if (start < i) parts.push(tx.slice(start, i));
      parts.push(tx[i + 1]);
      i++;
      start = i + 1;
    }
  }
  if (start === 0) return tx;
  if (start < tx.length) parts.push(tx.slice(start));
  return parts.join('');
}

// --- block starts -----------------------------------------------------------
// Each opener returns 0 (no match), 1 (a container opened, keep trying
// openers), or 2 (a leaf opened, stop).

function openBlockquote(st, ctn) {
  const src = st.line;
  const cur = st.cursor;
  if (cur.indented || charAtIdx(src, cur.nextNonSpace) !== 62) return 0;
  jumpToContent(cur);
  advanceCursor(src, cur, 1, false);
  const nx = charAtIdx(src, cur.idx);
  if (nx === 32 || nx === 9) advanceCursor(src, cur, 1, true);
  closeUnmatched(st);
  addChild(st, 'blockquote', cur.nextNonSpace);
  return 1;
}

function openAtx(st, ctn) {
  const src = st.line;
  const cur = st.cursor;
  if (cur.indented) return 0;
  const m = ATX_RE.exec(src.slice(cur.nextNonSpace));
  if (!m) return 0;
  jumpToContent(cur);
  advanceCursor(src, cur, m[0].length, false);
  closeUnmatched(st);
  const head = addChild(st, 'heading', cur.nextNonSpace);
  head.level = m[0].trim().length;
  // The heading text is the rest of the line with trailing closing
  // hashes removed.
  let tx = src.slice(cur.idx);
  tx = tx.replace(/^[ \t]*#+[ \t]*$/, '').replace(/[ \t]+#+[ \t]*$/, '');
  head.text = tx;
  advanceCursor(src, cur, src.length - cur.idx, false);
  return 2;
}

function openFence(st, ctn) {
  const src = st.line;
  const cur = st.cursor;
  if (cur.indented) return 0;
  const m = FENCE_RE.exec(src.slice(cur.nextNonSpace));
  if (!m) return 0;
  const fLen = m[0].length;
  closeUnmatched(st);
  const blk = addChild(st, 'code_block', cur.nextNonSpace);
  blk.fenced = true;
  blk.fenceLen = fLen;
  blk.fenceChar = m[0][0];
  blk.fenceIndent = cur.indent;
  jumpToContent(cur);
  advanceCursor(src, cur, fLen, false);
  return 2;
}

function openHtml(st, ctn) {
  const src = st.line;
  const cur = st.cursor;
  if (cur.indented || charAtIdx(src, cur.nextNonSpace) !== 60) return 0;
  const tx = src.slice(cur.nextNonSpace);
  const kind = htmlBlockType(tx);
  if (kind < 1 || kind > 7) return 0;
  if (kind === 7) {
    // A type 7 block cannot interrupt a paragraph, and it cannot be a
    // lazy continuation line of one either.
    if (ctn.kind === 'paragraph') return 0;
    if (!st.allClosed && !cur.blank && st.tip.kind === 'paragraph') return 0;
  }
  closeUnmatched(st);
  const blk = addChild(st, 'html_block', cur.idx);
  blk.htmlType = kind;
  return 2;
}

function openSetext(st, ctn) {
  const src = st.line;
  const cur = st.cursor;
  if (cur.indented || ctn.kind !== 'paragraph') return 0;
  const m = SETEXT_RE.exec(src.slice(cur.nextNonSpace));
  if (!m) return 0;
  closeUnmatched(st);
  // When the paragraph starts with link reference definitions, only
  // the part after them becomes the heading.
  let defLen = 0;
  const body = ctn.text;
  while (body.charCodeAt(defLen) === 91) { // [
    const p = scanRefDef(body.slice(defLen), null);
    if (!p) break;
    defLen += p;
  }
  if (body.length <= defLen) return 0;
  const defText = body.slice(0, defLen);
  const head = newBlock('heading');
  head.level = m[0][0] === '=' ? 1 : 2;
  head.text = body.slice(defLen);
  head.startLine = ctn.startLine;
  head.endLine = st.lineNumber;
  head.parent = ctn.parent;
  const at = ctn.parent.children.indexOf(ctn);
  ctn.parent.children.splice(at + 1, 0, head);
  if (defLen > 0) {
    ctn.text = defText;
    ctn.open = false;
    ctn.endLine = ctn.startLine + defText.split('\n').length - 2;
    // The (now closed) paragraph keeps its place; the tip moves to the
    // heading, which is itself closed (a single line).
    st.tip = head;
    head.open = false;
    st.tip = head.parent;
  } else {
    // No definitions: the paragraph disappears entirely.
    ctn.parent.children.splice(at, 1);
    st.tip = head.parent;
    head.open = false;
  }
  advanceCursor(src, cur, src.length - cur.idx, false);
  return 2;
}

function openHr(st, ctn) {
  const src = st.line;
  const cur = st.cursor;
  if (cur.indented) return 0;
  if (!HR_RE.test(src.slice(cur.nextNonSpace))) return 0;
  closeUnmatched(st);
  addChild(st, 'thematic_break', cur.nextNonSpace);
  advanceCursor(src, cur, src.length - cur.idx, false);
  return 2;
}

function openTable(st, ctn) {
  const src = st.line;
  const cur = st.cursor;
  if (cur.blank || cur.indented) return 0;
  const headText = src.slice(cur.nextNonSpace);
  if (headText === '') return 0;
  const delimIdx = st.lineNumber + 1;
  if (delimIdx >= st.lines.length) return 0;
  const probe = probeContainers(st, st.lines[delimIdx], ctn);
  if (!probe) return 0;
  const delimRaw = tailText(st.lines[delimIdx], probe.cur);
  const parsed = parseDelimiterRow(delimRaw);
  if (!parsed) return 0;
  const headCells = splitTableRow(headText, null);
  if (headCells.length !== parsed.count) return 0;
  closeUnmatched(st);
  const tbl = addChild(st, 'table', cur.nextNonSpace);
  tbl.header = headCells;
  tbl.align = parsed.align;
  tbl.rows = [];
  tbl.delimLine = delimIdx;
  tbl.endLine = st.lineNumber;
  return 2;
}

function openList(st, ctn) {
  const src = st.line;
  const cur = st.cursor;
  if (cur.indented && ctn.kind !== 'list') return 0;
  const mark = scanMarker(st, ctn);
  if (!mark) return 0;
  closeUnmatched(st);
  if (st.tip.kind !== 'list' || !sameListType(ctn.listData || {}, mark)) {
    ctn = addChild(st, 'list', cur.nextNonSpace);
    ctn.listType = mark.type;
    ctn.bullet = mark.bullet;
    ctn.delim = mark.delim;
    ctn.start = mark.start;
    ctn.listData = mark;
  }
  ctn = addChild(st, 'item', cur.nextNonSpace);
  ctn.markerOffset = mark.markerOffset;
  ctn.contentPad = mark.contentPad;
  // A task list item: [ ] / [x] / [X] followed by spaces and a
  // non-space character.
  const rest = src.slice(cur.idx);
  const task = /^\[[ xX]\][ \t]+\S/.exec(rest);
  if (task) {
    ctn.checked = (rest[1] === ' ' ? 0 : 1);
    // Eat "[ ]" plus the spaces after it, one column at a time.
    let eat = 3;
    while (eat < rest.length && (rest.charCodeAt(eat) === 32 || rest.charCodeAt(eat) === 9)) eat++;
    advanceCursor(src, cur, eat, true);
  }
  return 1;
}

function openIndentedCode(st, ctn) {
  const src = st.line;
  const cur = st.cursor;
  if (!cur.indented || st.tip.kind === 'paragraph' || cur.blank) return 0;
  advanceCursor(src, cur, 4, true);
  closeUnmatched(st);
  addChild(st, 'code_block', cur.idx);
  return 2;
}

const BLOCK_STARTERS = [
  openBlockquote, openAtx, openFence, openHtml, openSetext, openHr,
  openTable, openList, openIndentedCode,
];

// --- feeding one source line ----------------------------------------------------
// The lazy continuation of a paragraph inside a container: marked
// strips a full 4-column indent (4 spaces, or up to 3 spaces plus a
// tab) from such a line, while 1-3 spaces are kept as they are.
function trimLazyContinuation(st) {
  let anc = st.tip.parent;
  for (; anc; anc = anc.parent) {
    if (anc.kind === 'blockquote' || anc.kind === 'item') break;
  }
  if (!anc || st.cursor.halfTab) return;
  const rest = st.line.slice(st.cursor.idx);
  const m = /^(?: {0,3}\t| {4})/.exec(rest);
  // A leading tab after a consumed `>` expands to spaces (handled in
  // feedLine), so the tab variant is not stripped then; a 4-space
  // indent is always stripped (a lazy continuation of a list-item
  // paragraph inside a blockquote).
  const isTab = m && m[0].indexOf('\t') >= 0;
  if (m && !(isTab && st.quoteConsumed)) {
    st.line = rest.slice(m[0].length);
    st.cursor.idx = 0;
    st.cursor.col = 0;
    st.cursor.halfTab = false;
  }
}

// Marked's blockquote tokenizer replaces a lazy setext underline (an
// `=`/`-` run) with 4 spaces plus the run when it is not the first
// line of its lazy chunk (the previous line was lazy too). That keeps
// it paragraph text instead of a setext heading.
function hideLazySetext(st) {
  if (!st.tip.lastLazy) return;
  const rest = st.line.slice(st.cursor.idx);
  if (!/^ {0,3}(?:=+|-+)[ \t]*$/.test(rest)) return;
  st.line = '    ' + rest.replace(/^ {0,3}/, '');
  st.cursor.idx = 0;
  st.cursor.col = 0;
  st.cursor.halfTab = false;
}

// Phase 1: match the open containers, innermost first. Returns the
// deepest container that matched, or null when a fenced code block
// closed on this line and the line is consumed.
function matchOpenContainers(st) {
  let at = st.doc;
  for (;;) {
    const kid = lastOpenChild(at);
    if (!kid) break;
    at = kid;
    measureIndent(st.line, st.cursor);
    const verdict = matchContainer(st, at);
    if (verdict === 2) return null; // fenced code closed; line consumed
    if (verdict === 1) { at = at.parent; break; }
    // A container matching a non-blank line stretches to it, even when
    // the line adds no leaf content: an empty `>` line keeps its
    // blockquote/item open, so the tight/loose gap is measured from it.
    // A truly blank line does not stretch it — it is what makes a list
    // loose.
    if (!st.cursor.blank) at.endLine = st.lineNumber;
  }
  st.allClosed = at === st.oldTip;
  st.lastMatched = at;
  return at;
}

// Phase 2: try new block starts, unless the matched container is a leaf
// that accepts lines (other than a paragraph). Returns the container
// the line's content goes to.
function openNewBlocks(st, at) {
  let leafOpen = at.kind !== 'paragraph' && leafKind(at.kind);
  while (!leafOpen) {
    measureIndent(st.line, st.cursor);
    if (!st.cursor.indented && !isBlockStarter(st.line, st.cursor.nextNonSpace)) {
      // Only a table header can start with an ordinary character;
      // paragraph content keeps its leading spaces (marked does not
      // strip them), so the index is not advanced here.
      if (openTable(st, at) === 2) { at = st.tip; leafOpen = true; }
      break;
    }
    let si = 0;
    for (; si < BLOCK_STARTERS.length; si++) {
      const started = BLOCK_STARTERS[si](st, at);
      if (started === 1) { at = st.tip; break; }
      if (started === 2) { at = st.tip; leafOpen = true; break; }
    }
    if (si === BLOCK_STARTERS.length) break;
  }
  return at;
}

function processLine(st, r) {
  st.line = r.indexOf('\u0000') === -1 ? r : r.replace(/\0/g, '\uFFFD');
  st.cursor = newCursor();
  st.quoteConsumed = false; // a `>` marker was consumed on this line
  st.oldTip = st.tip;
  st.lineNumber = st.lineIndex;

  // Phase 1: match the open containers, innermost first.
  let at = matchOpenContainers(st);
  if (at === null) return; // a fenced code block closed; line consumed
  // Phase 2: try new block starts, unless the matched container is a
  // leaf that accepts lines (other than a paragraph).
  at = openNewBlocks(st, at);

  // Add the remaining line content.
  if (!st.allClosed && !st.cursor.blank && st.tip.kind === 'paragraph') {
    trimLazyContinuation(st);
    hideLazySetext(st);
    feedLine(st); // lazy paragraph continuation
    st.tip.lastLazy = true;
    return;
  }
  closeUnmatched(st);
  const kind = at.kind;
  if (leafKind(kind)) {
    feedLine(st);
    if (kind === 'paragraph') st.tip.lastLazy = false;
    if (kind === 'html_block' && at.htmlType >= 1 && at.htmlType <= 5 &&
      HTML_CLOSE_RE[at.htmlType].test(st.line.slice(st.cursor.idx))) {
      closeBlock(st, at, st.lineNumber);
    }
    return;
  }
  if (st.cursor.idx < st.line.length && !st.cursor.blank) {
    // A fresh paragraph keeps the line's leading spaces (marked does
    // not strip them from paragraph lines).
    at = addChild(st, 'paragraph', st.cursor.idx);
    feedLine(st);
  }
}

// Scans an optional title at `from`. Returns null when the character
// there does not open a title (" ' or (), { fail: true } when a title
// opens but never closes, and the title plus the index just past its
// closer otherwise. A single-quoted title may run over lines unless a
// blank line starts.
// True when the newline at `at` is followed, after spaces/tabs, by
// another newline — a blank line starts right after it.
function blankLineAfter(tx, at) {
  const tot = tx.length;
  let k = at + 1;
  while (k < tot && (tx.charCodeAt(k) === 32 || tx.charCodeAt(k) === 9)) k++;
  return k < tot && tx.charCodeAt(k) === 10;
}

// Skips trailing spaces/tabs from `p` and the newline that must follow
// them. Returns the index just past that newline, the index itself when
// the string simply ends there, or -1 when other text follows.
function skipToLineEnd(tx, p) {
  const tot = tx.length;
  while (p < tot && (tx.charCodeAt(p) === 32 || tx.charCodeAt(p) === 9)) p++;
  if (p >= tot) return p;
  if (tx.charCodeAt(p) !== 10) return -1;
  return p + 1;
}

function scanRefTitle(tx, from) {
  const tot = tx.length;
  if (from >= tot) return null;
  const quote = tx.charCodeAt(from);
  if (quote !== 34 && quote !== 39 && quote !== 40) return null;
  const closer = quote === 40 ? 41 : quote;
  let inner = '';
  for (let j = from + 1; j < tot; j++) {
    const code = tx.charCodeAt(j);
    if (code === closer) return { title: inner, nx: j + 1 };
    if (code === 92 && j + 1 < tot && isPunctChar(tx[j + 1])) {
      inner += tx[j + 1];
      j++;
      continue;
    }
    if (quote === 39 && code === 10 && blankLineAfter(tx, j)) return { fail: true };
    inner += tx[j];
  }
  return { fail: true };
}

// Scans a reference destination at `from`: either <...> (no newline or
// `<` inside, backslash escapes honoured) or a bare run (no whitespace
// or control character, balanced parens). Returns the destination and
// the index just past it, or null when there is none.
function scanRefDest(tx, from) {
  const tot = tx.length;
  if (from < tot && tx.charCodeAt(from) === 60) { // <
    let dest = '';
    for (let j = from + 1; j < tot; j++) {
      const code = tx.charCodeAt(j);
      if (code === 62) return { dest, nx: j + 1 }; // >
      if (code === 10 || code === 60) return null;
      if (code === 92 && j + 1 < tot && asciiPunct(tx.charCodeAt(j + 1))) {
        dest += tx[j + 1];
        j++;
        continue;
      }
      dest += tx[j];
    }
    return null;
  }
  let dest = '';
  let depth = 0;
  let seen = false;
  let j = from;
  for (; j < tot; j++) {
    const code = tx.charCodeAt(j);
    if (code === 32 || code === 9 || code === 10 || code <= 31) break;
    if (code === 92 && j + 1 < tot && asciiPunct(tx.charCodeAt(j + 1))) {
      dest += tx[j + 1];
      j++;
      seen = true;
      continue;
    }
    if (code === 40) depth++;
    else if (code === 41) {
      if (depth === 0) break;
      depth--;
    }
    dest += tx[j];
    seen = true;
  }
  if (!seen || depth !== 0) return null;
  return { dest, nx: j };
}

// --- link reference definitions ----------------------------------------------
// Scans the `[...]` label of a reference definition starting just after
// the `[`. Returns the label text and the index just past the closing
// `]`, or null when the label is empty, too long, holds an unescaped
// `[`, or never closes. A newline inside the label is allowed unless a
// blank line follows it.
function scanRefLabel(tx, from) {
  const tot = tx.length;
  let lbl = '';
  let j = from;
  let len = 0;
  while (j < tot) {
    const code = tx.charCodeAt(j);
    switch (code) {
      case 92: // backslash escape
        if (j + 1 < tot) {
          lbl += tx[j] + tx[j + 1];
          j += 2;
          len += 2;
        } else {
          lbl += tx[j];
          j++;
          len++;
        }
        continue;
      case 91: // unescaped [ inside the label
        return null;
      case 93: // ] closes the label
        break;
      case 10:
        if (blankLineAfter(tx, j)) return null;
        lbl += '\n';
        j++;
        len++;
        continue;
      default:
        lbl += tx[j];
        j++;
        len++;
        if (len > 999) return null;
        continue;
    }
    break;
  }
  if (j >= tot || len === 0) return null;
  return { lbl, nx: j + 1 };
}

// Read one link reference definition from the start of `tx`. The return
// value is the number of characters consumed, or 0 when there is none.
// When `refs` is a Map the definition is recorded (the first one wins);
// when it is null the text is only measured (for the setext split).
function scanRefDef(tx, refs) {
  const tot = tx.length;
  let pos = 0;
  // Up to 3 leading spaces.
  for (let lead = 0; pos < tot && tx.charCodeAt(pos) === 32 && lead < 3; lead++) pos++;
  if (pos >= tot || tx.charCodeAt(pos) !== 91) return 0; // [
  // The label: no unescaped `[` or `]` may appear inside it
  // (CommonMark forbids unescaped square brackets in a link label).
  // It ends at the first unescaped `]`, so `[ref[bar]]` is never a
  // definition.
  const lab = scanRefLabel(tx, pos + 1);
  if (!lab) return 0;
  const lbl = lab.lbl;
  let cur = lab.nx;
  if (foldLabel(lbl) === '') return 0;
  if (cur >= tot || tx.charCodeAt(cur) !== 58) return 0; // :
  cur++;
  // Optional spaces/tabs/newline before the destination.
  cur = skipSpacesNewline(tx, cur);
  if (cur >= tot) return 0;
  // The destination, in <...> form or bare.
  const dst = scanRefDest(tx, cur);
  if (!dst) return 0;
  const dest = dst.dest;
  cur = dst.nx;
  // The optional title is only attempted when whitespace was consumed
  // between destination and title. If a title parses but the line
  // does not end after it, the title is dropped and the line-end check
  // runs again from just after the destination.
  let title = null;
  const afterDest = cur;
  cur = skipSpacesNewline(tx, cur);
  if (cur !== afterDest) {
    const ttl = scanRefTitle(tx, cur);
    if (ttl && ttl.fail) return 0;
    if (ttl) { title = ttl.title; cur = ttl.nx; }
    else cur = afterDest;
  }
  // Only spaces/tabs may follow, then a newline or the end of the
  // string. If the title parsed but the line does not end, retry
  // without the title.
  let end = skipToLineEnd(tx, cur);
  if (end < 0) {
    if (title === null) return 0;
    title = null;
    end = skipToLineEnd(tx, afterDest);
    if (end < 0) return 0;
  }
  const used = end;
  if (refs) {
    const key = foldLabel(lbl);
    if (key && !refs.has(key)) {
      refs.set(key, { href: dest, title });
    }
  }
  return used;
}

// Skip spaces/tabs, then at most one newline and the spaces/tabs after it.
function skipSpacesNewline(tx, j) {
  const tot = tx.length;
  while (j < tot && (tx.charCodeAt(j) === 32 || tx.charCodeAt(j) === 9)) j++;
  if (j < tot && tx.charCodeAt(j) === 10) {
    j++;
    while (j < tot && (tx.charCodeAt(j) === 32 || tx.charCodeAt(j) === 9)) j++;
  }
  return j;
}

// --- top level ------------------------------------------------------------------
function buildTree(input) {
  const normalized = input.replace(/\r\n?/g, '\n');
  const endsWithNewline = normalized.endsWith('\n');
  const srcLines = normalized.split('\n');
  if (srcLines.length && srcLines[srcLines.length - 1] === '') srcLines.pop();
  const root = newBlock('document');
  const st = {
    doc: root, tip: root, oldTip: root, lastMatched: root,
    line: '', lineIndex: 0, lineNumber: 0, lines: srcLines, endsWithNewline,
    cursor: newCursor(), allClosed: true, refs: new Map(),
  };
  let n = 0;
  while (n < srcLines.length) {
    st.lineIndex = n;
    processLine(st, srcLines[n]);
    n++;
  }
  while (st.tip) closeBlock(st, st.tip, srcLines.length);
  // Link reference definitions are stripped from the starts of paragraphs.
  stripDefinitions(st.doc, st.refs);
  return { doc: st.doc, refs: st.refs };
}

function stripDefinitions(nd, refs) {
  const list = nd.children;
  for (let k = 0; k < list.length; k++) {
    const child = list[k];
    if (child.kind === 'paragraph') {
      const tx = child.text;
      let p = 0;
      let hadDef = false;
      // scanRefDef handles up to 3 leading spaces itself and returns 0
      // when the text is not a definition.
      for (;;) {
        if (p >= tx.length) break;
        const consumed = scanRefDef(tx.slice(p), refs);
        if (!consumed) break;
        p += consumed;
        hadDef = true;
      }
      if (hadDef) {
        child.text = tx.slice(p);
        if (child.text.trim() === '') child.empty = true;
      }
    }
    if (child.children.length) stripDefinitions(child, refs);
  }
}

// ===========================================================================
// The inline parser
// ===========================================================================
// A delimiter-stack algorithm in the style of CommonMark appendix A,
// adapted to marked — no named-entity decoding, GFM strikethrough with
// ~, extended autolinks, and the inRaw / inLink states.

function newInlineNode(kind) {
  return {
    kind, text: '', first: null, last: null, parent: null, next: null, prev: null,
    href: '', title: '', image: false, autolink: false, raw: false,
  };
}

function appendChild(par, nd) {
  nd.parent = par;
  const rest = par.last;
  if (rest) {
    rest.next = nd;
    nd.prev = rest;
    par.last = nd;
  } else {
    par.first = par.last = nd;
  }
  return nd;
}

function removeNode(nd) {
  const up = nd.parent;
  if (!up) return;
  if (nd.prev) nd.prev.next = nd.next;
  else up.first = nd.next;
  if (nd.next) nd.next.prev = nd.prev;
  else up.last = nd.prev;
  nd.parent = null;
  nd.next = null;
  nd.prev = null;
}

function insertAfter(nd, fresh) {
  fresh.parent = nd.parent;
  fresh.prev = nd;
  fresh.next = nd.next;
  if (nd.next) nd.next.prev = fresh;
  else if (nd.parent) nd.parent.last = fresh;
  nd.next = fresh;
}

function textNode(tx) {
  const nd = newInlineNode('tx');
  nd.text = tx;
  return nd;
}

// The character just before `from` and just after `i`, read as whole
// code points (a surrogate pair counts as one character); the start
// and end of the text read as '\n'.
function flankChars(tx, from, i) {
  let before;
  if (from === 0) before = '\n';
  else {
    const prevCode = tx.charCodeAt(from - 1);
    if (prevCode >= 0xDC00 && prevCode <= 0xDFFF && from >= 2) before = tx.slice(from - 2, from);
    else before = tx.charAt(from - 1);
  }
  let after;
  if (i >= tx.length) after = '\n';
  else {
    const nextCode = tx.charCodeAt(i);
    if (nextCode >= 0xD800 && nextCode <= 0xDBFF && i + 1 < tx.length) after = tx.slice(i, i + 2);
    else after = tx.charAt(i);
  }
  return { before, after };
}

// --- delimiter scanning (CommonMark flanking rules) --------------------------
// Scans the run of `cc` at sx.pos and reports its length plus whether
// it can open and/or close, or null when there is no run. The
// characters before and after the run are read as code points, and
// whitespace / punctuation follow Unicode categories.
function measureDelimRun(sx, cc) {
  const tx = sx.src;
  let i = sx.pos;
  let count = 0;
  while (i < tx.length && tx.charCodeAt(i) === cc) { count++; i++; }
  if (count === 0) return null;
  const from = sx.pos;
  const { before, after } = flankChars(tx, from, i);
  const afterWs = unicodeWs(after);
  const afterPunct = isPunctChar(after);
  const afterAlnum = after !== '\n' && ALNUM_RE.test(after);
  const beforeAlnum = before !== '\n' && ALNUM_RE.test(before);
  const beforeWs = unicodeWs(before);
  const beforePunct = isPunctChar(before);
  const leftFlank = !afterWs && (!afterPunct || beforeWs || beforePunct);
  const rightFlank = !beforeWs && (!beforePunct || afterWs || afterPunct);
  let openable;
  let closable;
  if (cc === US) {
    openable = leftFlank && (!rightFlank || beforePunct);
    closable = rightFlank && (!leftFlank || afterPunct);
  } else {
    openable = leftFlank;
    closable = rightFlank;
  }
  // GFM strikethrough: a run of 3+ tildes is never a delimiter
  // (marked's del tokenizer fails at the run start and the text token
  // swallows it), and a run of 3+ can never close.
  if (cc === TILDE && count > 2) {
    openable = false;
    closable = false;
  }
  return {
    numdelims: count,
    canOpen: openable,
    canClose: closable,
    afterIsAlnum: afterAlnum,
    beforeIsAlnum: beforeAlnum,
  };
}

function unicodeWs(chr) {
  const code = chr.charCodeAt(0);
  if (code < 128) return code === 32 || code === 9 || code === 10 || code === 11 || code === 12 || code === 13;
  return /\s/.test(chr);
}

function pushDelimiter(sx, d) {
  d.prev = sx.delims;
  d.next = null;
  if (sx.delims) sx.delims.next = d;
  sx.delims = d;
}

function removeDelimiter(sx, d) {
  if (d.prev !== null) d.prev.next = d.next;
  if (d.next === null) sx.delims = d.prev;
  else d.next.prev = d.prev;
}

function spliceDelimiters(lo, hi) {
  if (lo.next !== hi) {
    lo.next = hi;
    hi.prev = lo;
  }
}

// Take a run of delimiter characters (*, _, ~) at sx.pos.
function handleDelim(sx, cc, blk) {
  const scan = measureDelimRun(sx, cc);
  if (!scan) return false;
  const n = scan.numdelims;
  const from = sx.pos;
  sx.pos += n;
  const txt = textNode(sx.src.slice(from, sx.pos));
  appendChild(blk, txt);
  if (scan.canOpen || scan.canClose) {
    const d = {
      ch: cc, count: n, origCount: n, node: txt,
      prev: null, next: null, canOpen: scan.canOpen, canClose: scan.canClose,
      afterIsAlnum: scan.afterIsAlnum, beforeIsAlnum: scan.beforeIsAlnum,
    };
    // A poisoned link marks the first opener after it: an emphasis
    // span starting there (and anything nested inside it) does not
    // form when it is underscore-delimited or holds inner emphasis.
    if (sx.poison && scan.canOpen && cc !== TILDE) {
      d.poisoned = true;
      sx.poison = false;
    }
    pushDelimiter(sx, d);
  }
  return true;
}

// Decides whether an opener/closer pair may form an emphasis span.
// Marked vetoes a pair in three situations: a one-delimiter asterisk
// outer whose span holds a strong whose closer sits right before an
// alphanumeric while its opener does not sit right after one (an
// intraword `**` does not block), and a split closer (one taking fewer
// delimiters than its opener holds) vetoed by any inner emphasis whose
// closer is followed by an alphanumeric; a span entirely inside a
// failed link label holding a code span with an odd backtick count; and
// a span starting at (or nested under) a poisoned opener, when it is
// underscore-delimited or holds inner emphasis. A vetoed pair is not a
// match: the search moves on to an earlier opener.
function pairVetoed(sx, op, cl, take, cc, stackBottom) {
  if (cc === STAR) {
    const opNode = op.node, clNode = cl.node;
    let cur = opNode.next, innerStrong = false, innerSplit = false;
    while (cur && cur !== clNode) {
      if (cur.isBlocker) innerStrong = true;
      if (cur.splitBlocker) innerSplit = true;
      cur = cur.next;
    }
    // One delimiter of outer emphasis is vetoed by an inner strong.
    if (take === 1 && innerStrong) return true;
    // A split closer is vetoed by inner emphasis whose closer is
    // followed by an alphanumeric.
    if (take < op.count && innerSplit) return true;
  }
  if (op.failedLabel && cl.failedLabel) {
    let cur3 = op.node.next;
    const clNode3 = cl.node;
    while (cur3 && cur3 !== clNode3) {
      if (cur3.kind === 'code') {
        const code3 = cur3.text;
        let n3 = 0;
        for (let i = 0; i < code3.length; i++) if (code3.charCodeAt(i) === 96) n3++;
        if (n3 % 2 === 1) return true;
      }
      cur3 = cur3.next;
    }
  }
  if (cc !== US && cc !== STAR) return false;
  if (op.poisoned) {
    let hasInner = false;
    let cur4 = op.node.next;
    while (cur4 && cur4 !== cl.node) {
      if (cur4.kind === 'em' || cur4.kind === 'strong') { hasInner = true; break; }
      cur4 = cur4.next;
    }
    // A pair vetoed just before leaves its delimiters in the stack
    // between opener and closer.
    if (!hasInner && op.next !== null && op.next !== cl) hasInner = true;
    // Trying this opener spends the poison.
    op.poisoned = false;
    return cc === US || hasInner;
  }
  let prv = op.prev;
  while (prv !== null && prv !== stackBottom) {
    if (prv.poisoned) return true;
    prv = prv.prev;
  }
  return false;
}

// Pairs opener `op` with closer `cl`, taking `take` delimiters from
// each, and returns the delimiter the scan should continue from.
function applyEmphasisPair(sx, op, cl, take, cc) {
  const opNode = op.node;
  const clNode = cl.node;
  op.count -= take;
  cl.count -= take;
  opNode.text = opNode.text.slice(0, opNode.text.length - take);
  clNode.text = clNode.text.slice(0, clNode.text.length - take);
  const tag = cc === TILDE ? 'del' : (take === 1 ? 'em' : 'strong');
  const shell = newInlineNode(tag);
  // A strong counts as a blocker for an outer one-delimiter emphasis
  // when its closer sits right before an alphanumeric and its opener
  // does not sit right after one (an intraword `**` never blocks).
  shell.isBlocker = (take === 2 && !!cl.afterIsAlnum && !op.beforeIsAlnum);
  // Any emphasis whose closer is followed by an alphanumeric while its
  // opener is not preceded by one stops a closer from splitting an
  // opener (taking fewer delimiters than the opener holds): in `**a
  // *b*c* d**` the `*` after `c` must not steal 1 delimiter from the
  // outer `**`; in `**a *b* c* d**` (a space after the inner closer)
  // it does split.
  shell.splitBlocker = (!!cl.afterIsAlnum && !op.beforeIsAlnum);
  // Marked: when the closer run has delimiters left over and the span
  // holds an inner emphasis whose closer is followed by an
  // alphanumeric, those leftover delimiters belong INSIDE the emphasis
  // (marked's closer is the last `take` of the run). So `**a *b*one***`
  // gives `<strong>a <em>b</em>one*</strong>`; with no such inner node
  // (`**a***`, `**a *b* c***`) the leftover stays outside.
  let splitInside = false;
  if (cl.count > 0 && take === 2) {
    let cur0 = opNode.next;
    while (cur0 && cur0 !== clNode) {
      if (cur0.splitBlocker) { splitInside = true; break; }
      cur0 = cur0.next;
    }
  }
  let cur = opNode.next;
  while (cur && cur !== clNode) {
    const nx = cur.next;
    removeNode(cur);
    appendChild(shell, cur);
    cur = nx;
  }
  if (splitInside) {
    // The leftover closer delimiters move inside as trailing text.
    appendChild(shell, textNode(clNode.text));
    clNode.text = '';
    cl.count = 0;
  }
  insertAfter(opNode, shell);
  spliceDelimiters(op, cl);
  if (op.count === 0) {
    removeNode(opNode);
    removeDelimiter(sx, op);
  }
  if (cl.count === 0) {
    removeNode(clNode);
    const afterCl = cl.next;
    removeDelimiter(sx, cl);
    return afterCl;
  }
  return cl;
}

// Walks the delimiter stack above stackBottom (a delimiter object, or
// null) and pairs openers with closers into em / strong / del nodes.
// The search follows CommonMark's emphasis algorithm, with one more
// slot range for '~' (slots 14-19) and the extra rule that a '~'
// opener and closer must carry the same delimiter count.
function resolveEmphasis(sx, stackBottom) {
  const floor = Array.from({ length: 20 }, () => stackBottom);
  // Locate the first closer above stackBottom.
  let cl = sx.delims;
  while (cl !== null && cl.prev !== stackBottom) cl = cl.prev;
  while (cl !== null) {
    const cc = cl.ch;
    if (!cl.canClose) { cl = cl.next; continue; }
    // Scan backwards for the first opener that fits.
    let op = cl.prev;
    let paired = false;
    let slotIx;
    if (cc === US) slotIx = 2 + (cl.canOpen ? 3 : 0) + (cl.origCount % 3);
    else if (cc === STAR) slotIx = 8 + (cl.canOpen ? 3 : 0) + (cl.origCount % 3);
    else slotIx = 14 + (cl.canOpen ? 3 : 0) + (cl.origCount % 3); // ~
    while (op !== null && op !== stackBottom && op !== floor[slotIx]) {
      const odd = (cl.canOpen || op.canClose) &&
        cl.origCount % 3 !== 0 &&
        (op.origCount + cl.origCount) % 3 === 0;
      const tildeMatch = cc !== TILDE || op.count === cl.count;
      if (op.ch === cc && op.canOpen && !odd && tildeMatch) {
        // Marked quirk (the emStrong match-counter): a one-delimiter
        // outer emphasis never forms when its span contains a strong
        // whose closer sits right before an alphanumeric while its
        // opener does not sit right after one — an intraword `**`
        // does not block. So `*a **b**c*` stays literal outside the
        // strong, but `*foo**bar**baz*` (intraword inner) and `*a **b**
        // c*` (closer followed by a space) DO form. Only asterisk
        // outers veto this way: marked's underscore scan behaves
        // differently (`_large **data**not_` DOES form the outer em).
        const take = (cl.count >= 2 && op.count >= 2) ? 2 : 1;
        if (!pairVetoed(sx, op, cl, take, cc, stackBottom)) {
          paired = true;
          break;
        }
      }
      op = op.prev;
    }
    const prevCl = cl;
    if (paired) {
      const take = (cl.count >= 2 && op.count >= 2) ? 2 : 1;
      cl = applyEmphasisPair(sx, op, cl, take, cc);
    } else {
      cl = cl.next;
      // Record the lower bound for later searches.
      floor[slotIx] = prevCl.prev;
      if (!prevCl.canOpen) removeDelimiter(sx, prevCl);
    }
  }
  // Drop every delimiter left above stackBottom.
  for (;;) {
    const top = sx.delims;
    if (top === null || top === stackBottom) break;
    removeDelimiter(sx, top);
  }
}

// Looks for the closing run of `runLen` backticks after `after`
// (stopping at `stopAt`). Returns the code span's inner text and the
// index just past the closer, plus the first backtick run seen (used
// for the loose-closer rule below); inner is null when no run of
// exactly `runLen` backticks turns up.
// The index just past the backtick run starting at `i`.
function backtickRunEnd(tx, i) {
  let j = i;
  while (j < tx.length && tx.charCodeAt(j) === 96) j++;
  return j;
}

// Looks for the closing run of `runLen` backticks after `after`
// (stopping at `stopAt`). Returns the code span's inner text and the
// index just past the closer, plus the first backtick run seen (used
// for the loose-closer rule below); inner is null when no run of
// exactly `runLen` backticks turns up.
function findTickCloser(tx, after, runLen, stopAt) {
  let firstAt = -1, firstTo = -1, firstLen = 0;
  let from = after;
  while (true) {
    const cand = tx.indexOf('`', from);
    if (cand < 0 || cand >= stopAt) break;
    const candEnd = backtickRunEnd(tx, cand);
    if (firstAt < 0) { firstAt = cand; firstTo = candEnd; firstLen = candEnd - cand; }
    if (candEnd - cand === runLen) {
      let inner = tx.slice(after, cand).replace(/\n/g, ' ');
      if (inner.length > 0 && /[^ ]/.test(inner) &&
        inner.charCodeAt(0) === 32 && inner.charCodeAt(inner.length - 1) === 32) {
        inner = inner.slice(1, -1);
      }
      return { inner, end: candEnd, firstAt, firstTo, firstLen };
    }
    from = candEnd;
  }
  return { inner: null, end: -1, firstAt, firstTo, firstLen };
}

// --- backticks (code spans) ---------------------------------------------------
function handleBackticks(sx, blk) {
  const tx = sx.src;
  const i = backtickRunEnd(tx, sx.pos);
  const ticks = tx.slice(sx.pos, i);
  const after = i;
  // A run flagged as a loose closer (below) is literal text, not a
  // code span opener.
  if (sx.tickLiteral === sx.pos) {
    sx.tickLiteral = -1;
    appendChild(blk, textNode(ticks));
    sx.pos = after;
    return true;
  }
  // With a bracket open, a code span must not swallow the `]` that
  // closes it by reaching onto a later line: marked's link tokenizer
  // runs before codespans, so the link forms and an unbalanced
  // `` ``url` `` stays literal. The closer is only searched for on
  // this same line.
  let stopAt = tx.length;
  if (sx.brackets) {
    const nl = tx.indexOf('\n', after);
    if (nl >= 0) stopAt = nl;
  }
  const closer = findTickCloser(tx, after, ticks.length, stopAt);
  if (closer.inner !== null) {
    const nd = newInlineNode('code');
    nd.text = closer.inner;
    appendChild(blk, nd);
    sx.pos = closer.end;
    return true;
  }
  // No strict closer. Inside a link label, a shorter backtick run
  // closes the run loosely (marked's label match is non-greedy and
  // allows a shorter closer): flag it literal so it is not re-read as
  // a code span opener that would eat the label's `]`.
  if (sx.brackets && ticks.length >= 2 && closer.firstAt >= 0 && closer.firstLen < ticks.length) {
    const closeBrk = tx.indexOf(']', after);
    if (closeBrk >= 0 && closer.firstTo <= closeBrk) sx.tickLiteral = closer.firstAt;
  }
  sx.pos = after;
  appendChild(blk, textNode(ticks));
  return true;
}

// --- backslash ------------------------------------------------------------------
function handleBackslash(sx, blk) {
  const tx = sx.src;
  sx.pos += 1;
  if (sx.pos < tx.length && tx.charCodeAt(sx.pos) === 10) {
    sx.pos += 1;
    appendChild(blk, newInlineNode('br'));
    // After a hard break, marked drops the next line's leading spaces/tabs.
    while (sx.pos < tx.length && (tx.charCodeAt(sx.pos) === 32 || tx.charCodeAt(sx.pos) === 9)) sx.pos++;
  } else if (sx.pos < tx.length && asciiPunct(tx.charCodeAt(sx.pos))) {
    appendChild(blk, textNode(tx.charAt(sx.pos)));
    sx.pos += 1;
  } else {
    appendChild(blk, textNode('\\'));
  }
  return true;
}

// --- autolink <...> --------------------------------------------------------------
const EMAIL_ANGLE_RE = /^<([0-9A-Za-z.!#$%&'*+\/=?^_`{|}~-]+@[0-9A-Za-z](?:[0-9A-Za-z-]{0,61}[0-9A-Za-z])?(?:\.[0-9A-Za-z](?:[0-9A-Za-z-]{0,61}[0-9A-Za-z])?)*)>/;
const SCHEME_ANGLE_RE = /^<[A-Za-z][0-9A-Za-z.+-]{1,31}:[^\x00-\x20<>]*>/;

function handleAngleAutolink(sx, blk) {
  const rest = sx.src.slice(sx.pos);
  const m = EMAIL_ANGLE_RE.exec(rest);
  if (m) {
    const url = m[1];
    const link = newInlineNode('link');
    link.href = 'mailto:' + url;
    link.autolink = true;
    appendChild(link, textNode(url));
    appendChild(blk, link);
    sx.pos += m[0].length;
    return true;
  }
  const sch = SCHEME_ANGLE_RE.exec(rest);
  if (sch) {
    const url = sch[0].slice(1, -1);
    const link = newInlineNode('link');
    link.href = url;
    link.autolink = true;
    appendChild(link, textNode(url));
    appendChild(blk, link);
    sx.pos += sch[0].length;
    return true;
  }
  return false;
}

// --- inline HTML tag -------------------------------------------------------------
const HTML_TAG_RE = /^(?:<!--(?:-?>|[\S\s]*?(?:-->|$))|^<\/[A-Za-z][0-9A-Za-z-]*\s*>|^<[A-Za-z][0-9A-Za-z-]*(?:\s+[A-Za-z:_][\w.:-]*(?:\s*=\s*"[^"]*"|\s*=\s*'[^']*'|\s*=\s*[^\s"'=<>`]+)?)*?\s*\/?>|^<\?[\S\s]*?\?>|^<![A-Za-z]+\s[\S\s]*?>|^<!\[CDATA\[[\S\s]*?\]\]>)/;
const OPEN_A_RE = /^<a /i;
const CLOSE_A_RE = /^<\/a>/i;
const OPEN_RAW_RE = /^<(pre|code|kbd|script)(\s|>)/i;
const CLOSE_RAW_RE = /^<\/(pre|code|kbd|script)(\s|>)/i;

function handleHtmlTag(sx, blk) {
  const m = HTML_TAG_RE.exec(sx.src.slice(sx.pos));
  if (!m) return false;
  const r = m[0];
  const out = newInlineNode('out');
  out.text = r;
  appendChild(blk, out);
  sx.pos += r.length;
  if (OPEN_A_RE.test(r)) sx.inLink = true;
  else if (sx.inLink && CLOSE_A_RE.test(r)) sx.inLink = false;
  if (!sx.inRaw && OPEN_RAW_RE.test(r)) sx.inRaw = true;
  else if (sx.inRaw && CLOSE_RAW_RE.test(r)) sx.inRaw = false;
  return true;
}

// --- link destination / title / label ---------------------------------------------
function scanInlineDest(sx) {
  const tx = sx.src, tot = tx.length;
  if (sx.pos < tot && tx.charCodeAt(sx.pos) === 60) { // <
    let i = sx.pos + 1;
    let url = '';
    while (i < tot) {
      const code = tx.charCodeAt(i);
      if (code === 62) { sx.pos = i + 1; return unescapeBackslash(url); }
      if (code === 10 || code === 60) return null;
      if (code === 92 && i + 1 < tot && asciiPunct(tx.charCodeAt(i + 1))) { url += tx[i + 1]; i += 2; continue; }
      url += tx[i];
      i++;
    }
    return null;
  }
  let i = sx.pos;
  let depth = 0;
  const from = i;
  while (i < tot) {
    const code = tx.charCodeAt(i);
    if (code === 92 && i + 1 < tot && asciiPunct(tx.charCodeAt(i + 1))) { i += 2; continue; }
    if (code === 40) depth++;
    else if (code === 41) { if (depth === 0) break; depth--; }
    else if (wsCode(code)) break;
    i++;
  }
  if (i === from && (i >= tot || tx.charCodeAt(i) !== 41)) return null;
  if (depth !== 0) return null;
  const url = tx.slice(from, i);
  sx.pos = i;
  return unescapeBackslash(url);
}

function scanInlineTitle(sx) {
  const tx = sx.src, tot = tx.length;
  if (sx.pos >= tot) return null;
  const qch = tx.charCodeAt(sx.pos);
  if (qch !== 34 && qch !== 39 && qch !== 40) return null;
  const closer = qch === 40 ? 41 : qch;
  let i = sx.pos + 1;
  let body = '';
  while (i < tot) {
    const code = tx.charCodeAt(i);
    if (code === closer) { sx.pos = i + 1; return body; }
    if (code === 92 && i + 1 < tot && isPunctChar(tx[i + 1])) { body += tx[i + 1]; i += 2; continue; }
    if (qch === 40 && (code === 40 || code === 41)) return null;
    body += tx[i];
    i++;
  }
  return null;
}

const LINK_LABEL_RE = /^\[(?:\\.|[^\\\]]){0,1000}\]/s;
function scanInlineLabel(sx) {
  const m = LINK_LABEL_RE.exec(sx.src.slice(sx.pos));
  if (!m || m[0].length > 1001) return 0;
  return m[0].length;
}

// --- brackets ----------------------------------------------------------------------
function pushBracket(sx, txt, at, isImage) {
  if (sx.brackets !== null) sx.brackets.bracketAfter = true;
  sx.brackets = {
    node: txt, prev: sx.brackets, prevDelim: sx.delims,
    index: at, image: isImage, active: true, bracketAfter: false,
  };
}

function popBracket(sx) {
  sx.brackets = sx.brackets.prev;
}

// Mark (or clear) the delimiters added since this bracket opened: they
// sit inside its label. A failed link leaves them marked so
// resolveEmphasis can undo an emphasis span wholly inside the label; a
// link that forms clears marks left by a nested failed bracket.
function markLabelDelims(sx, brk, flag) {
  let cur = sx.delims;
  while (cur !== null && cur !== brk.prevDelim) {
    cur.failedLabel = flag;
    cur = cur.prev;
  }
}

function handleOpenBracket(sx, blk) {
  const at = sx.pos;
  sx.pos += 1;
  const txt = textNode('[');
  appendChild(blk, txt);
  pushBracket(sx, txt, at, false);
  return true;
}

function handleBang(sx, blk) {
  const at = sx.pos;
  sx.pos += 1;
  const followsBracket = sx.pos < sx.src.length && sx.src.charCodeAt(sx.pos) === 91;
  if (!followsBracket) {
    appendChild(blk, textNode('!'));
    return true;
  }
  sx.pos += 1;
  const txt = textNode('![');
  appendChild(blk, txt);
  pushBracket(sx, txt, at + 1, true);
  return true;
}

// Skips a balanced `[...]` starting at `i` (escapes honoured). Returns
// the index just past the closing `]`, or -1 when the brackets never
// balance.
function skipNestedBrackets(tx, i) {
  const tot = tx.length;
  let nest = 1;
  let j = i + 1;
  for (; j < tot && nest > 0; j++) {
    const chr = tx.charCodeAt(j);
    if (chr === 92) {
      j++;
      continue;
    }
    if (chr === 91) nest++;
    else if (chr === 93) nest--;
  }
  return nest === 0 ? j : -1;
}

// Skips a code span starting at a backtick run at `i`: the closing run
// is the first backtick run after the opening (it may be shorter).
// Returns the index just past the closing run, or -1 when the run
// never closes — except that a dangling run of 2+ backticks at the very
// end of the label is allowed, and returns the end.
function skipCodeSpan(tx, i) {
  const tot = tx.length;
  const j = backtickRunEnd(tx, i);
  const openLen = j - i;
  let seek = j;
  while (seek < tot && tx.charCodeAt(seek) !== 96) seek++;
  if (seek >= tot) {
    if (openLen >= 2 && j === tot) return j;
    return -1;
  }
  return backtickRunEnd(tx, seek);
}

// Marked's link label pattern, checked here as a validator over the
// raw label content (the text between `[` and `]`). It walks the label
// piece by piece: a nested `[...]` (balanced, escapes allowed); `\`
// plus any character; a code span whose content is non-greedy and whose
// closing run may be SHORTER than the opening run; a dangling run of
// 2+ backticks right before `]`; or any character except `[`, `]`, `\`,
// backtick. A label with an unmatched backtick run (for example
// `[a `b]`, or `[first `a ` b` of]`) fails the whole label, so the link
// does not form and the URL is autolinked instead. Returns true when
// the entire label matches.
function labelValid(tx) {
  const tot = tx.length;
  for (let i = 0; i < tot;) {
    const code = tx.charCodeAt(i);
    switch (code) {
      case 91: { // [
        const after = skipNestedBrackets(tx, i);
        if (after < 0) return false;
        i = after;
        break;
      }
      case 92: // backslash escape
        if (i + 1 >= tot) return false;
        i += 2;
        break;
      case 96: { // backtick run
        const after = skipCodeSpan(tx, i);
        if (after < 0) return false;
        i = after;
        break;
      }
      case 93: // unescaped ] inside the label
        return false;
      default:
        i++;
        break;
    }
  }
  return true;
}

// A link label is "poisoned" when it holds a backtick run of length 2+
// with no equal-length run to pair with (an unmatched `` ``X` `` run,
// or a lone `` `` `` run). A balanced code span (`` `` a ` b `` ``,
// runs 2,1,2) is not poisoned: the two runs of length 2 pair up.
function labelPoisoned(tx) {
  const tally = Object.create(null);
  for (let i = 0; i < tx.length;) {
    if (tx.charCodeAt(i) !== 96) { i++; continue; }
    const end = backtickRunEnd(tx, i);
    const runLen = end - i;
    tally[runLen] = (tally[runLen] || 0) + 1;
    i = end;
  }
  for (const runLen in tally) {
    const len = +runLen;
    if (len >= 2 && tally[runLen] % 2 === 1) return true;
  }
  return false;
}

// Tries the `(destination "title")` form at the cursor. Returns the
// href and title on success, or null (with the cursor rewound) when the
// form does not parse.
function tryInlineLink(sx) {
  if (sx.pos >= sx.src.length || sx.src.charCodeAt(sx.pos) !== 40) return null;
  const rewind = sx.pos;
  sx.pos++;
  const destStart = sx.pos;
  skipInlineSpaces(sx);
  const dest = scanInlineDest(sx);
  if (dest === null) { sx.pos = rewind; return null; }
  skipInlineSpaces(sx);
  let title = null;
  if (sx.pos > destStart && wsCode(sx.src.charCodeAt(sx.pos - 1))) {
    const ttl = scanInlineTitle(sx);
    if (ttl !== null) title = ttl;
  }
  skipInlineSpaces(sx);
  if (sx.pos < sx.src.length && sx.src.charCodeAt(sx.pos) === 41) {
    sx.pos += 1;
    return { href: dest, title };
  }
  sx.pos = rewind;
  return null;
}

// Tries the `[label]` / `[text][label]` / `[text]` reference forms
// after a `]`. Returns the href and title on success, or null.
function tryReferenceLink(sx, br, closeAt) {
  const rewind = sx.pos;
  const refAt = sx.pos;
  const refLen = scanInlineLabel(sx);
  let second;
  if (refLen > 2) second = sx.src.slice(refAt, refAt + refLen);
  else if (!br.bracketAfter) second = sx.src.slice(br.index, closeAt);
  // scanInlineLabel leaves pos alone: consume the second label when
  // one is there (n>0), else rewind to before the attempt.
  if (refLen === 0) sx.pos = rewind;
  else sx.pos = refAt + refLen;
  if (!second) return null;
  const entry = sx.refs.get(foldLabel(second.slice(1, -1)));
  if (!entry) return null;
  return { href: entry.href, title: entry.title };
}

function handleCloseBracket(sx, blk) {
  sx.pos += 1;
  const closeAt = sx.pos;
  const br = sx.brackets;
  if (br === null) {
    appendChild(blk, textNode(']'));
    return true;
  }
  if (!br.active) {
    appendChild(blk, textNode(']'));
    popBracket(sx);
    return true;
  }
  // A label with an unmatched backtick run fails marked's label regex,
  // so no link forms at all (the `]` stays literal).
  const lbl = sx.src.slice(br.index + 1, closeAt - 1);
  if (lbl.indexOf('`') >= 0 && !labelValid(lbl)) {
    markLabelDelims(sx, br, true);
    appendChild(blk, textNode(']'));
    if (labelPoisoned(lbl)) sx.poison = true;
    popBracket(sx);
    return true;
  }
  const isImg = br.image;
  const inl = tryInlineLink(sx);
  const ref = inl ? null : tryReferenceLink(sx, br, closeAt);
  const got = inl || ref;
  if (got) {
    const nd = newInlineNode(isImg ? 'image' : 'link');
    nd.href = got.href;
    nd.title = got.title || '';
    let kid = br.node.next;
    while (kid) {
      const after = kid.next;
      removeNode(kid);
      if (!isImg && kid.kind === 'link' && kid.extended) {
        // A bare URL or email inside link text stays plain text:
        // marked's url tokenizer only runs when !inLink.
        const head = kid.first;
        const flat = textNode(head ? head.text : '');
        if (head) flat.raw = head.raw;
        appendChild(nd, flat);
      } else {
        appendChild(nd, kid);
      }
      kid = after;
    }
    appendChild(blk, nd);
    if (labelPoisoned(lbl)) sx.poison = true;
    markLabelDelims(sx, br, false);
    resolveEmphasis(sx, br.prevDelim);
    popBracket(sx);
    removeNode(br.node);
    if (!isImg) {
      let up = sx.brackets;
      while (up !== null) {
        if (!up.image) up.active = false;
        up = up.prev;
      }
    }
    return true;
  }
  popBracket(sx);
  sx.pos = closeAt;
  markLabelDelims(sx, br, true);
  appendChild(blk, textNode(']'));
  if (labelPoisoned(lbl)) sx.poison = true;
  return true;
}

// Skip spaces/tabs, then at most one newline and the spaces/tabs after it.
function skipInlineSpaces(sx) {
  const tx = sx.src, tot = tx.length;
  while (sx.pos < tot && (tx.charCodeAt(sx.pos) === 32 || tx.charCodeAt(sx.pos) === 9)) sx.pos++;
  if (sx.pos < tot && tx.charCodeAt(sx.pos) === 10) {
    sx.pos++;
    while (sx.pos < tot && (tx.charCodeAt(sx.pos) === 32 || tx.charCodeAt(sx.pos) === 9)) sx.pos++;
  }
}

// --- extended autolinks (GFM) -------------------------------------------------------
// True when `code` may appear in an email word run: alphanumerics
// plus `-` and `_`, with `.` and `+` allowed when requested.
function mailWordChar(code, allowDot, allowPlus) {
  const alnum = (code >= 48 && code <= 57) || (code >= 65 && code <= 90) ||
    (code >= 97 && code <= 122);
  return alnum || code === 45 || code === 95 ||
    (allowDot && code === 46) || (allowPlus && code === 43);
}

function countCharRun(tx, i, allowDot, allowPlus) {
  const tot = tx.length;
  let n = 0;
  for (; i < tot; i++) {
    if (!mailWordChar(tx.charCodeAt(i), allowDot, allowPlus)) break;
    n++;
  }
  return { end: i, count: n };
}

// The length of a valid email address starting at p, or 0 when there
// is none.
function emailLength(tx, p, delims) {
  const tot = tx.length;
  const local = countCharRun(tx, p, true, true);
  let i = local.end;
  if (local.count === 0 || i >= tot || tx.charCodeAt(i) !== 64) return 0;
  i++;
  const dom = countCharRun(tx, i, false, false);
  i = dom.end;
  if (dom.count === 0) return 0;
  let dots = 0;
  while (i < tot && tx.charCodeAt(i) === 46) {
    // A `.` followed by no valid group is trailing punctuation, not
    // part of the email: stop here and keep the match so far.
    const end = scanDomainPart(tx, i);
    if (end < 0) break;
    i = end;
    dots++;
  }
  if (dots === 0) return 0;
  if (i < tot) {
    const code = tx.charCodeAt(i);
    // A trailing `_` that closes an open `_` emphasis delimiter is not
    // part of the email (marked tokenizes the emphasis first, so the
    // email never sees the closer); any other trailing alnum, `_`, or
    // `-` invalidates the match.
    if (code === 95 && delims && openUnderscoreDelim(delims)) return i - p;
    if (wordChar(code) || code === 45) return 0;
  }
  return i - p;
}

// Scans one dot-separated domain group starting after the dot at
// `i`: alphanumerics extend it, `-` and `_` are skipped over. Returns
// the index just past the group, or -1 when no group follows the dot.
function scanDomainPart(tx, i) {
  const tot = tx.length;
  let lst = -1;
  for (let j = i + 1; j < tot; j++) {
    const code = tx.charCodeAt(j);
    const alnum = (code >= 48 && code <= 57) || (code >= 65 && code <= 90) ||
      (code >= 97 && code <= 122);
    if (alnum) lst = j + 1;
    else if (code === 45 || code === 95) { /* keep scanning */ }
    else break;
  }
  return lst;
}

// True when an open `_` emphasis delimiter sits anywhere in the stack.
function openUnderscoreDelim(delims) {
  for (let del = delims; del; del = del.prev) {
    if (del.ch === 95 && del.canOpen) return true;
  }
  return false;
}

// Is there a protocol:// at p (http/https/ftp, any case)?
function protocolAt(tx, i) {
  const tot = tx.length;
  const c0 = tx.charCodeAt(i) | 32;
  if (c0 === 104) { // http / https
    if (i + 7 > tot) return false;
    const t = tx.charCodeAt(i + 1) | 32;
    const t2 = tx.charCodeAt(i + 2) | 32;
    const p = tx.charCodeAt(i + 3) | 32;
    if (t !== 116 || t2 !== 116 || p !== 112) return false;
    let q = i + 4;
    if ((tx.charCodeAt(q) | 32) === 115) {
      q++;
      if (q + 3 > tot) return false;
    }
    return tx.charCodeAt(q) === 58 &&
      tx.charCodeAt(q + 1) === 47 &&
      tx.charCodeAt(q + 2) === 47;
  }
  if (c0 !== 102) return false; // ftp
  if (i + 6 > tot) return false;
  return (tx.charCodeAt(i + 1) | 32) === 116 &&
    (tx.charCodeAt(i + 2) | 32) === 112 &&
    tx.charCodeAt(i + 3) === 58 &&
    tx.charCodeAt(i + 4) === 47 &&
    tx.charCodeAt(i + 5) === 47;
}

function urlPunct(code) {
  switch (code) {
    case 63: case 33: case 46: case 44: case 58: case 59:
    case 42: case 95: case 39: case 34: case 126: case 40: case 41: case 38:
      return true;
    default:
      return false;
  }
}

// The index of the `)` closing the paren group opened at `i`, or -1
// when the group never closes.
function parenGroupEnd(url, i) {
  const tot = url.length;
  let j = i + 1;
  while (j < tot && url.charCodeAt(j) !== 41) j++;
  return j < tot ? j : -1;
}

// The index just past the `&word` starting at `i`, or -1 when no word
// follows the `&`.
function entityWordEnd(url, i) {
  const tot = url.length;
  let j = i + 1, w = 0;
  while (j < tot && wordChar(url.charCodeAt(j))) { j++; w++; }
  return w > 0 ? j : -1;
}

// The index just past the punctuation run starting at `i`.
function punctRunEnd(url, i) {
  const tot = url.length;
  let j = i;
  while (j < tot && urlPunct(url.charCodeAt(j))) j++;
  return j;
}

// One pass of the URL backpedal: the longest prefix that does not end
// with trailing punctuation (paren groups are kept, and a &word; at
// the very end is excluded).
function trimUrlStep(url) {
  const tot = url.length;
  let i = 0;
  while (i < tot) {
    const code = url.charCodeAt(i);
    if (code === 40) { // (
      const close = parenGroupEnd(url, i);
      if (close >= 0) { i = close + 1; continue; }
      break;
    }
    if (code === 38) { // &
      const end = entityWordEnd(url, i);
      if (end > 0 && end < tot && url.charCodeAt(end) === 59 && end === tot - 1) break;
      i++;
      continue;
    }
    if (urlPunct(code)) {
      const j = punctRunEnd(url, i);
      if (j >= tot) break;
      i = j;
      continue;
    }
    i++;
  }
  return url.slice(0, i);
}

function trimUrlTail(url) {
  let cur = url;
  for (;;) {
    const next = trimUrlStep(cur);
    if (next === cur) return cur;
    cur = next;
  }
}

function wordChar(code) {
  const digit = code >= 48 && code <= 57;
  const upper = code >= 65 && code <= 90;
  const lower = code >= 97 && code <= 122;
  return digit || upper || lower || code === 95;
}

// True when any open bracket is still active (its link may yet form).
function hasActiveBracket(sx) {
  for (let b = sx.brackets; b; b = b.prev) {
    if (b.active) return true;
  }
  return false;
}

// Scans the dot-separated host labels starting at `from`: each label
// is a run of alphanumerics or `-`. Returns the index just past the
// last label and how many labels were found.
function scanHostLabels(tx, from) {
  const tot = tx.length;
  let i = from;
  let count = 0;
  while (i < tot) {
    let j = i;
    for (; j < tot; j++) {
      const code = tx.charCodeAt(j);
      const ok = (code >= 48 && code <= 57) || (code >= 65 && code <= 90) ||
        (code >= 97 && code <= 122) || code === 45;
      if (!ok) break;
    }
    if (j === i) break;
    count++;
    i = j;
    if (i < tot && tx.charCodeAt(i) === 46) {
      i++;
      continue;
    }
    break;
  }
  return { end: i, count };
}

// A protocol:// URL or a www. address at the cursor becomes a link.
function handleSchemeUrl(sx, blk) {
  const tx = sx.src;
  const p = sx.pos;
  const tot = tx.length;
  let schemeLen = 0;
  let www = false;
  if (protocolAt(tx, p)) {
    let i = p;
    while (i < tot && tx.charCodeAt(i) !== 58) i++;
    schemeLen = i + 3 - p;
  } else if (tx.charCodeAt(p) === 119 && p + 4 <= tot &&
    tx.charCodeAt(p + 1) === 119 &&
    tx.charCodeAt(p + 2) === 119 &&
    tx.charCodeAt(p + 3) === 46) {
    if (p === 0) {
      www = true;
    } else {
      const prv = tx.charCodeAt(p - 1);
      const okBefore = prv === 32 || prv === 9 || prv === 10 || prv === 42 ||
        prv === 95 || prv === 126 || prv === 40;
      if (okBefore) www = true;
    }
    if (www) schemeLen = 4;
  }
  if (schemeLen === 0) return false;
  const host = scanHostLabels(tx, p + schemeLen);
  if (host.count === 0) return false;
  let i = host.end;
  for (; i < tot; i++) {
    const code = tx.charCodeAt(i);
    if (code === 32 || code === 9 || code === 10 || code === 60) break;
    // A `]` ends the URL only when it would close an *active* bracket
    // (marked's url tokenizer does not run inside link text); a `]`
    // after deactivated brackets is just another URL character.
    if (code === 93 && hasActiveBracket(sx)) break;
  }
  const href = trimUrlTail(tx.slice(p, i));
  if (href.length === 0) return false;
  const link = newInlineNode('link');
  link.href = www ? 'http://' + href : href;
  link.autolink = true;
  link.extended = true;
  appendChild(link, textNode(href));
  appendChild(blk, link);
  sx.pos = p + href.length;
  return true;
}

// A mailto: or xmpp: address at the cursor becomes a link. The xmpp
// form may carry a /resource part after the address.
// Scans the /resource part of an xmpp: address starting at the slash
// in `from`: alphanumerics, @ and `.`. Returns the index just past it,
// or `from` when there is nothing to take.
function scanXmppResource(tx, from) {
  const tot = tx.length;
  let j = from + 1;
  for (; j < tot; j++) {
    const code = tx.charCodeAt(j);
    const ok = (code >= 48 && code <= 57) || (code >= 65 && code <= 90) ||
      (code >= 97 && code <= 122) || code === 64 || code === 46;
    if (!ok) break;
  }
  return j > from + 1 ? j : from;
}

function handleMailto(sx, blk) {
  const tx = sx.src;
  const p = sx.pos;
  const tot = tx.length;
  const fst = tx.charCodeAt(p);
  if (fst !== 109 && fst !== 120) return false; // m, x
  let scheme = 0;
  let xmpp = false;
  if (p + 7 <= tot && tx.slice(p, p + 7) === 'mailto:') scheme = 7;
  else if (p + 5 <= tot && tx.slice(p, p + 5) === 'xmpp:') { scheme = 5; xmpp = true; }
  if (scheme === 0) return false;
  const addrLen = emailLength(tx, p + scheme, sx.delims);
  if (addrLen <= 0) return false;
  let endAt = p + scheme + addrLen;
  if (xmpp && endAt < tot && tx.charCodeAt(endAt) === 47) {
    endAt = scanXmppResource(tx, endAt);
  }
  const shown = tx.slice(p, endAt);
  const link = newInlineNode('link');
  link.href = shown;
  link.autolink = true;
  link.extended = true;
  appendChild(link, textNode(shown));
  appendChild(blk, link);
  sx.pos = endAt;
  return true;
}

// A bare email address on its own.
function handleBareEmail(sx, blk) {
  const tx = sx.src;
  const p = sx.pos;
  const mLen = emailLength(tx, p, sx.delims);
  if (mLen <= 0) return false;
  const shown = tx.slice(p, p + mLen);
  const link = newInlineNode('link');
  link.href = 'mailto:' + shown;
  link.autolink = true;
  link.extended = true;
  appendChild(link, textNode(shown));
  appendChild(blk, link);
  sx.pos = p + mLen;
  return true;
}

function handleBareAutolink(sx, blk) {
  // Marked's url tokenizer only runs when !inLink: inside a link (or
  // after an unclosed <a> tag, which persists across blocks) a bare
  // URL or email is plain text.
  if (sx.inLink) return false;
  if (handleMailto(sx, blk)) return true;
  if (handleSchemeUrl(sx, blk)) return true;
  return handleBareEmail(sx, blk);
}

// --- text runs -------------------------------------------------------------------
// The characters allowed in an email local part:
// [a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]
function mailChar(code) {
  if ((code >= 48 && code <= 57) || (code >= 65 && code <= 90) || (code >= 97 && code <= 122)) return true;
  switch (code) {
    case 46: case 33: case 35: case 36: case 37: case 38: case 39:
    case 42: case 43: case 47: case 61: case 63: case 94: case 95:
    case 96: case 123: case 124: case 125: case 126: case 45:
      return true;
    default:
      return false;
  }
}

function localPartStart(tx, from, at) {
  let i = at - 1;
  while (i >= from && mailChar(tx.charCodeAt(i))) i--;
  return i + 1 < at ? i + 1 : -1;
}

// True when a www. address starts at `i` (with a valid character
// before it, or at the start of the text).
function wwwStarts(tx, i) {
  if (i + 4 > tx.length) return false;
  if (tx.charCodeAt(i + 1) !== 119 || tx.charCodeAt(i + 2) !== 119 || tx.charCodeAt(i + 3) !== 46) return false;
  if (i === 0) return true;
  const prv = tx.charCodeAt(i - 1);
  return prv === 32 || prv === 9 || prv === 10 || prv === 42 || prv === 95 || prv === 126 || prv === 40;
}

// True when a mailto: or xmpp: address starts at `i` (with a
// non-alphanumeric before it, or at the start of the text).
function mailtoStarts(tx, i) {
  const tot = tx.length;
  const isMailto = i + 7 <= tot && tx.slice(i, i + 7) === 'mailto:';
  const isXmpp = !isMailto && i + 5 <= tot && tx.slice(i, i + 5) === 'xmpp:';
  if (!isMailto && !isXmpp) return false;
  if (i === 0) return true;
  const prv = tx.charCodeAt(i - 1);
  return !((prv >= 48 && prv <= 57) || (prv >= 65 && prv <= 90) || (prv >= 97 && prv <= 122));
}

function handleText(sx, blk) {
  const tx = sx.src, tot = tx.length;
  let i = sx.pos;
  const from = i;
  scan: while (i < tot) {
    const chr = tx.charCodeAt(i);
    switch (chr) {
      case 10: // \n
      case 92: case 96: case 42: case 126: case 91: case 93: case 33: case 60:
        break scan;
      case 95: { // _
        // The run stops so the delimiter is processed — unless this
        // _ is a lone intraword one (word characters on both sides).
        // A _ followed by another _ starts a delimiter run, so it
        // always stops the text.
        if (i + 1 < tot && tx.charCodeAt(i + 1) === 95) break scan;
        const prv = i > 0 ? tx.charCodeAt(i - 1) : 10;
        const nx = i + 1 < tot ? tx.charCodeAt(i + 1) : 10;
        if (wordChar(prv) && wordChar(nx)) { i++; continue; }
        break scan;
      }
      case 104: case 72: case 102: case 70: // h H f F
        if (protocolAt(tx, i)) break scan;
        i++;
        continue;
      case 119: // w
        if (wwwStarts(tx, i)) break scan;
        i++;
        continue;
      case 109: case 120: // m x
        if (mailtoStarts(tx, i)) break scan;
        i++;
        continue;
      case 64: { // @
        const localAt = localPartStart(tx, from, i);
        if (localAt >= 0 && emailLength(tx, localAt, sx.delims) > 0) {
          i = localAt;
          break scan;
        }
        i++;
        continue;
      }
      default:
        i++;
        continue;
    }
  }
  if (i === from) return false;
  const txt = textNode(tx.slice(from, i));
  txt.raw = sx.inRaw;
  appendChild(blk, txt);
  sx.pos = i;
  return true;
}

// --- newline -----------------------------------------------------------------------
function handleNewline(sx, blk) {
  sx.pos += 1;
  const lst = blk.last;
  const endsWithSpace = lst && lst.kind === 'tx' && lst.text.length > 0 &&
    lst.text.charCodeAt(lst.text.length - 1) === 32;
  if (!endsWithSpace) {
    appendChild(blk, newInlineNode('soft'));
    return true;
  }
  const hard = lst.text.length >= 2 && lst.text.charCodeAt(lst.text.length - 2) === 32;
  if (!hard) {
    appendChild(blk, newInlineNode('soft'));
    return true;
  }
  lst.text = lst.text.replace(/ +$/, '');
  appendChild(blk, newInlineNode('br'));
  // After a hard break, marked drops the next line's leading
  // spaces/tabs; after a soft break it keeps them.
  const tx = sx.src;
  while (sx.pos < tx.length && (tx.charCodeAt(sx.pos) === 32 || tx.charCodeAt(sx.pos) === 9)) sx.pos++;
  return true;
}

const INLINE_DISPATCH = {
  10: handleNewline,
  92: handleBackslash,
  96: handleBackticks,
  91: handleOpenBracket,
  33: handleBang,
  93: handleCloseBracket,
};

// --- main inline step ---------------------------------------------------------------
function stepInline(sx, blk) {
  const tx = sx.src, code = tx.charCodeAt(sx.pos);
  let done = false;
  const handler = INLINE_DISPATCH[code];
  if (handler) done = handler(sx, blk);
  else if (code === 42 || code === 95 || code === 126) done = handleDelim(sx, code, blk);
  else if (code === 60) done = handleAngleAutolink(sx, blk) || handleHtmlTag(sx, blk);
  else done = handleBareAutolink(sx, blk) || handleText(sx, blk);
  if (!done) {
    const txt = textNode(tx.charAt(sx.pos));
    txt.raw = sx.inRaw;
    appendChild(blk, txt);
    sx.pos += 1;
  }
  return true;
}

// Render the inline content of one leaf block (a paragraph, a heading,
// or a table cell) to HTML. Marked keeps a paragraph's leading spaces
// (they render as text) and its trailing spaces; only the single
// trailing \n — the last line's terminator — is removed. Headings are
// trimmed at both ends. The inLink state lives at the document level:
// marked's lexer keeps it across blocks (an unclosed <a> suppresses
// extended autolinks in later paragraphs), while inRaw is reset for
// each block. It is cleared in parse().
let docInLink = false;

function renderInlineText(tx, refs, trimLead) {
  let from = 0, to = tx.length;
  if (trimLead) {
    while (from < to) {
      const code = tx.charCodeAt(from);
      if (code === 32 || code === 9 || code === 10 || code === 13) from++;
      else break;
    }
    while (to > from) {
      const code = tx.charCodeAt(to - 1);
      if (code === 32 || code === 9 || code === 10 || code === 13) to--;
      else break;
    }
  } else if (to > from && tx.charCodeAt(to - 1) === 10) {
    to--; // strip exactly one trailing newline
  }
  tx = tx.slice(from, to);
  if (tx === '') return '';
  const tree = newInlineNode('root');
  const sx = {
    src: tx, pos: 0, refs, root: tree, tickLiteral: -1, poison: false,
    delims: null, brackets: null, inLink: docInLink, inRaw: false,
  };
  while (sx.pos < tx.length) stepInline(sx, tree);
  resolveEmphasis(sx, null);
  docInLink = sx.inLink;
  return renderChildren(tree);
}

// --- inline rendering -----------------------------------------------------------------
function renderChildren(tree) {
  let out = '';
  for (let kid = tree.first; kid; kid = kid.next) out += renderInlineNode(kid);
  return out;
}

function renderLink(link) {
  const cln = cleanUrl(link.href);
  if (cln === null) return renderChildren(link);
  let out = '<a href="' + escapeHtml(cln, link.autolink) + '"';
  if (link.title) out += ' title="' + escapeHtml(link.title, false) + '"';
  out += '>';
  if (link.autolink) {
    for (let kid = link.first; kid; kid = kid.next) out += escapeHtml(kid.text, true);
  } else {
    out += renderChildren(link);
  }
  out += '</a>';
  return out;
}

function renderImage(img) {
  const cln = cleanUrl(img.href);
  const altTextOut = escapeHtml(altText(img), false);
  if (cln === null) return altTextOut;
  let out = '<img src="' + escapeHtml(cln, false) + '" alt="' + altTextOut + '"';
  if (img.title) out += ' title="' + escapeHtml(img.title, false) + '"';
  out += '>';
  return out;
}

const INLINE_RENDER = {
  em: (n) => '<em>' + renderChildren(n) + '</em>',
  strong: (n) => '<strong>' + renderChildren(n) + '</strong>',
  del: (n) => '<del>' + renderChildren(n) + '</del>',
  link: renderLink,
  image: renderImage,
  tx: (n) => n.raw ? n.text : escapeHtml(decodeNumRefs(n.text), false),
  code: (n) => '<code>' + escapeHtml(n.text, true) + '</code>',
  br: () => '<br>',
  soft: () => '\n',
  out: (n) => n.text,
};

function renderInlineNode(n) {
  const fn = INLINE_RENDER[n.kind];
  return fn ? fn(n) : '';
}

// The plain-text rendering of a node's children, used for image alt
// text: emphasis and links are flattened, code and raw HTML are kept
// as text, and line breaks contribute nothing.
function altText(img) {
  let out = '';
  for (let kid = img.first; kid; kid = kid.next) {
    if (kid.kind === 'tx') { out += kid.raw ? kid.text : decodeNumRefs(kid.text); continue; }
    if (kid.kind === 'code' || kid.kind === 'out') { out += kid.text; continue; }
    if (kid.kind === 'br' || kid.kind === 'soft') continue;
    out += altText(kid);
  }
  return out;
}

// --- block rendering -------------------------------------------------------------------
function renderItem(item, refs, out) {
  out.push('<li>');
  const isTight = item.parent && item.parent.tight;
  const list = item.children;
  // In a loose list the checkbox is the first inline token of the
  // first paragraph, so it renders inside <p>...</p>.
  if (item.checked >= 0 && !isTight && list.length && list[0].kind === 'paragraph' && !list[0].empty) {
    out.push('<p>', item.checked ? '<input checked="" disabled="" type="checkbox"> ' : '<input disabled="" type="checkbox"> ');
    out.push(renderInlineText(list[0].text, refs));
    out.push('</p>\n');
    for (let k = 1; k < list.length; k++) renderBlockNode(list[k], refs, out);
    if (list.length > 1 && list[list.length - 1].kind === 'html_block' && out[out.length - 1] === '\n') out.pop();
    out.push('</li>\n');
    return;
  }
  if (item.checked >= 0) {
    out.push(item.checked ? '<input checked="" disabled="" type="checkbox"> ' : '<input disabled="" type="checkbox"> ');
  }
  for (const kid of list) {
    if (isTight && kid.kind === 'paragraph') {
      if (!kid.empty) out.push(renderInlineText(kid.text, refs));
    } else {
      renderBlockNode(kid, refs, out);
    }
  }
  // Marked trims the item text, so a trailing HTML block (raw text)
  // loses its trailing \n when it is the last child.
  if (list.length && list[list.length - 1].kind === 'html_block' && out[out.length - 1] === '\n') out.pop();
  out.push('</li>\n');
}

function renderTable(tbl, refs, out) {
  out.push('<table>\n<thead>\n<tr>\n');
  for (let col = 0; col < tbl.header.length; col++) {
    const al = tbl.align[col];
    out.push(al ? '<th align="' + al + '">' : '<th>');
    out.push(renderInlineText(tbl.header[col], refs));
    out.push('</th>\n');
  }
  out.push('</tr>\n</thead>\n');
  if (tbl.rows && tbl.rows.length) {
    out.push('<tbody>');
    for (const ln of tbl.rows) {
      const rowCells = splitTableRow(ln, tbl.header.length);
      out.push('<tr>\n');
      for (let col = 0; col < rowCells.length; col++) {
        const al = tbl.align[col];
        out.push(al ? '<td align="' + al + '">' : '<td>');
        out.push(renderInlineText(rowCells[col], refs));
        out.push('</td>\n');
      }
      out.push('</tr>\n');
    }
    out.push('</tbody>');
  }
  out.push('</table>\n');
}

function renderDocument(blk, refs, out) {
  for (const kid of blk.children) renderBlockNode(kid, refs, out);
}

function renderParagraph(blk, refs, out) {
  if (blk.empty) return;
  out.push('<p>', renderInlineText(blk.text, refs), '</p>\n');
}

function renderHeading(blk, refs, out) {
  out.push('<h', blk.level, '>', renderInlineText(blk.text, refs, true), '</h', blk.level, '>\n');
}

function renderCode(blk, refs, out) {
  const language = blk.info.match(/^\S*/)[0];
  const code = blk.text ? blk.text.replace(/\n$/, '') + '\n' : '';
  if (language) out.push('<pre><code class="language-', escapeHtml(language, false), '">', escapeHtml(code, true), '</code></pre>\n');
  else out.push('<pre><code>', escapeHtml(code, true), '</code></pre>\n');
}

function renderHtml(blk, refs, out) {
  out.push(blk.text);
  if (!blk.noTrailNewline) out.push('\n');
}

function renderBlockquote(blk, refs, out) {
  out.push('<blockquote>\n');
  for (const kid of blk.children) renderBlockNode(kid, refs, out);
  // Marked trims the item/blockquote text, so a trailing HTML block
  // (raw text) loses its trailing \n when it is the last child.
  const list = blk.children;
  if (list.length && list[list.length - 1].kind === 'html_block' && out[out.length - 1] === '\n') out.pop();
  out.push('</blockquote>\n');
}

function renderList(blk, refs, out) {
  const listTag = blk.listType === 'ordered' ? 'ol' : 'ul';
  if (listTag === 'ol' && blk.start !== 1) out.push('<ol start="', blk.start, '">\n');
  else out.push('<', listTag, '>\n');
  for (const kid of blk.children) renderBlockNode(kid, refs, out);
  out.push('</', listTag, '>\n');
}

const BLOCK_RENDER = {
  document: renderDocument,
  paragraph: renderParagraph,
  heading: renderHeading,
  thematic_break: (blk, refs, out) => { out.push('<hr>\n'); },
  code_block: renderCode,
  html_block: renderHtml,
  blockquote: renderBlockquote,
  list: renderList,
  item: renderItem,
  table: renderTable,
};

function renderBlockNode(blk, refs, out) {
  const fn = BLOCK_RENDER[blk.kind];
  if (fn) fn(blk, refs, out);
}

// --- top level ---------------------------------------------------------------------------
export function parse(markdown) {
  const { doc, refs } = buildTree(markdown);
  docInLink = false; // marked's lexer inLink persists across blocks in a document
  const out = [];
  renderBlockNode(doc, refs, out);
  return out.join('');
}
