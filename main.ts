// mend — one patch tool for every AI edit format.
//
// Reads a patch in one of four formats (unified diff, SEARCH/REPLACE
// blocks, V4A, JSON edits), finds the lines each edit names, and writes
// every change or none, printing what it changed or why it failed.
// The contract is SPEC.md; this file implements it from scratch.
//
//   node main.ts [--format=NAME] [--check] [--strict] [PATCH]
//
// Node 22, standard library only. Deterministic: the same patch on the
// same tree always gives the same exit code, stdout and files.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMAT_NAMES = ['auto', 'unified', 'search-replace', 'v4a', 'json'] as const;

/** A fault in the patch text: reported as `error: parse <line>`. */
class ParseFault {
  readonly line: number;
  constructor(line: number) {
    this.line = line;
  }
}

/** One edit failing: reported as `error: <code> <path>`. */
class EditFault {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

type EditFn = (tree: WorkTree) => void;

const isBlank = (s: string): boolean => s.trim() === '';

/** A patch's lines: split at \n, one trailing \r removed from each, and
 * the empty piece after a final \n dropped. */
function patchLines(text: string): string[] {
  if (text === '') return [];
  const parts = text.split('\n');
  if (text.endsWith('\n')) parts.pop();
  return parts.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

/** A path is safe when it is not empty, does not start with /, holds no
 * backslash, and none of its /-separated segments is empty, . or .. */
function isSafePath(p: string): boolean {
  if (p === '' || p.startsWith('/') || p.includes('\\')) return false;
  return p.split('/').every((seg) => seg !== '' && seg !== '.' && seg !== '..');
}

const leadingWhitespace = (line: string): string => {
  const m = /^[ \t]*/.exec(line);
  return m === null ? '' : m[0];
};

/** A file's lines, its line break, and whether it ends with one. */
interface FileModel {
  lines: string[];
  br: string;
  finalBreak: boolean;
}

function splitFile(text: string): FileModel {
  if (text === '') return { lines: [], br: '\n', finalBreak: false };
  const firstNl = text.indexOf('\n');
  const br = firstNl > 0 && text[firstNl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const finalBreak = text.endsWith(br);
  if (finalBreak) parts.pop();
  return { lines: parts, br, finalBreak };
}

function joinFile(model: FileModel): string {
  if (model.lines.length === 0) return '';
  return model.lines.join(model.br) + (model.finalBreak ? model.br : '');
}

/** The tree as the edits leave it: paths the edits touched hold their
 * new text (null: deleted); everything else is read from disk. */
class WorkTree {
  private disk = new Map<string, string | null>();
  private overlay = new Map<string, string | null>();
  readonly moves: Array<{ from: string; to: string }> = [];

  private loadFromDisk(p: string): string | null {
    if (!this.disk.has(p)) {
      let value: string | null = null;
      try {
        if (statSync(p).isFile()) value = readFileSync(p, 'utf8');
      } catch {
        value = null;
      }
      this.disk.set(p, value);
    }
    return this.disk.get(p)!;
  }

  /** The text a path holds now (null: absent). */
  read(p: string): string | null {
    return this.overlay.has(p) ? this.overlay.get(p)! : this.loadFromDisk(p);
  }

  /** The text a path held before the patch (null: absent). */
  original(p: string): string | null {
    return this.loadFromDisk(p);
  }

  write(p: string, value: string | null): void {
    this.overlay.set(p, value);
  }

  touchedPaths(): string[] {
    return [...this.overlay.keys()];
  }

  snapshot(): Map<string, string | null> {
    return new Map(this.overlay);
  }

  restore(snap: Map<string, string | null>): void {
    this.overlay.clear();
    for (const [k, v] of snap) this.overlay.set(k, v);
  }

  noteMove(from: string, to: string): void {
    this.moves.push({ from, to });
  }
}

/** The form a line takes at a matching tier: exact, trailing
 * spaces/tabs removed, or leading and trailing spaces/tabs removed. */
function tierKey(line: string, tier: number): string {
  if (tier === 0) return line;
  if (tier === 1) return line.replace(/[ \t]+$/, '');
  return line.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

/** Every 0-based position at or after `from` where `pattern` matches
 * `lines` at `tier`. Occurrences may overlap. */
function findOccurrences(lines: string[], pattern: string[], tier: number, from: number): number[] {
  const hits: number[] = [];
  if (pattern.length === 0) return hits;
  const want = pattern.map((l) => tierKey(l, tier));
  for (let i = from; i + pattern.length <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < pattern.length; j++) {
      if (tierKey(lines[i + j]!, tier) !== want[j]!) {
        ok = false;
        break;
      }
    }
    if (ok) hits.push(i);
  }
  return hits;
}

/** The first tier (0, then 1, then 2; only 0 when strict) at which
 * `pattern` occurs in `lines` at or after `from`. When `eofOnly`, an
 * occurrence counts only when it ends at the file's last line. */
function firstTierWith(lines: string[], pattern: string[], strict: boolean, from: number, eofOnly: boolean): number | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    const hits = findOccurrences(lines, pattern, tier, from);
    const usable = eofOnly ? hits.filter((pos) => pos + pattern.length === lines.length) : hits;
    if (usable.length > 0) return tier;
  }
  return null;
}

/** One line of the replacement text: either a context line, written as
 * the file's own matched line (at the given position in O), or a new
 * line, written from the patch (re-indented at tier 2). */
interface NewLine {
  ctxPos: number | null;
  text: string;
}

/** Render the replacement lines for a match at `at`: context lines come
 * from the file, other lines are re-indented at tier 2. */
function renderNewLines(items: NewLine[], fileLines: string[], at: number, oldLines: string[], tier: number): string[] {
  const out: string[] = [];
  const f = tier === 2 ? leadingWhitespace(fileLines[at] ?? '') : '';
  const p = tier === 2 ? leadingWhitespace(oldLines[0] ?? '') : '';
  for (const item of items) {
    if (item.ctxPos !== null) {
      out.push(fileLines[at + item.ctxPos]!);
      continue;
    }
    const text = item.text;
    if (tier === 2 && text !== '' && text.trim() !== '' && text.startsWith(p)) {
      out.push(f + text.slice(p.length));
    } else {
      out.push(text);
    }
  }
  return out;
}

/** One body line of a hunk or chunk: context, removed, added, or a
 * backslash marker line. `blank` says the raw patch line was blank
 * (empty or only whitespace). */
interface BodyLine {
  kind: 'ctx' | 'old' | 'new' | 'mark';
  text: string;
  blank: boolean;
}

function parseBodyLine(raw: string): BodyLine {
  if (raw === '') return { kind: 'ctx', text: '', blank: true };
  const c = raw[0]!;
  if (c === ' ') return { kind: 'ctx', text: raw.slice(1), blank: raw.trim() === '' };
  if (c === '-') return { kind: 'old', text: raw.slice(1), blank: false };
  if (c === '+') return { kind: 'new', text: raw.slice(1), blank: false };
  if (c === '\\') return { kind: 'mark', text: raw.slice(1), blank: false };
  return { kind: 'ctx', text: raw, blank: false };
}

function isBodyLine(raw: string): boolean {
  return raw === '' || raw.startsWith(' ') || raw.startsWith('-') || raw.startsWith('+') || raw.startsWith('\\');
}

/** Split a hunk or chunk body into the old lines O and the new lines N. */
function splitBody(body: BodyLine[]): { oldLines: string[]; newItems: NewLine[] } {
  const oldLines: string[] = [];
  const newItems: NewLine[] = [];
  for (const b of body) {
    if (b.kind === 'ctx') {
      newItems.push({ ctxPos: oldLines.length, text: b.text });
      oldLines.push(b.text);
    } else if (b.kind === 'old') {
      oldLines.push(b.text);
    } else if (b.kind === 'new') {
      newItems.push({ ctxPos: null, text: b.text });
    }
  }
  return { oldLines, newItems };
}

/** Whether a backslash line follows the hunk's last context or added
 * line, meaning the result has no final line break when the hunk runs
 * to the end of the file. */
function hunkHasNoNewline(body: BodyLine[]): boolean {
  let last = -1;
  for (let k = 0; k < body.length; k++) {
    if (body[k]!.kind === 'ctx' || body[k]!.kind === 'new') last = k;
  }
  if (last < 0) return false;
  const next = body[last + 1];
  return next !== undefined && next.kind === 'mark';
}

// ---------------------------------------------------------------------------
// Format detection (SPEC.md section 4)
// ---------------------------------------------------------------------------

function detectFormat(lines: string[]): string | null {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (
    lines.some(
      (l, i) =>
        l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')),
    )
  ) {
    return 'unified';
  }
  return null;
}

// ---------------------------------------------------------------------------
// Unified diffs (SPEC.md section 6)
// ---------------------------------------------------------------------------

interface Hunk {
  start: number;
  body: BodyLine[];
}

interface UnifiedSection {
  pairOld: string | null;
  pairNew: string | null;
  renameOld: string | null;
  renameNew: string | null;
  gitOld: string | null;
  gitNew: string | null;
  newFile: boolean;
  deletedFile: boolean;
  hasPair: boolean;
  hunks: Hunk[];
}

function newUnifiedSection(): UnifiedSection {
  return {
    pairOld: null,
    pairNew: null,
    renameOld: null,
    renameNew: null,
    gitOld: null,
    gitNew: null,
    newFile: false,
    deletedFile: false,
    hasPair: false,
    hunks: [],
  };
}

/** A ---/+++ header path: the text after the four characters, up to the
 * first tab, with surrounding spaces removed, and a leading a/ or b/
 * removed. /dev/null means no file. */
function headerPath(line: string): string | null {
  const rest = line.slice(4);
  const tab = rest.indexOf('\t');
  const raw = (tab >= 0 ? rest.slice(0, tab) : rest).trim();
  if (raw === '/dev/null') return null;
  if (raw.startsWith('a/') || raw.startsWith('b/')) return raw.slice(2);
  return raw;
}

function parseUnified(lines: string[], strict: boolean): EditFn[] {
  const sections: UnifiedSection[] = [];
  let cur: UnifiedSection | null = null;
  let i = 0;
  const pairAt = (j: number): boolean =>
    (lines[j] ?? '').startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ');
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(\S+) b\/(\S+)$/.exec(line);
      if (m === null) throw new ParseFault(i + 1);
      cur = newUnifiedSection();
      cur.gitOld = m[1]!;
      cur.gitNew = m[2]!;
      sections.push(cur);
      i++;
      continue;
    }
    if (line.startsWith('--- ') && pairAt(i)) {
      if (cur !== null && cur.hunks.length === 0 && !cur.hasPair) {
        cur.pairOld = headerPath(lines[i]!);
        cur.pairNew = headerPath(lines[i + 1]!);
        cur.hasPair = true;
      } else {
        cur = newUnifiedSection();
        cur.pairOld = headerPath(lines[i]!);
        cur.pairNew = headerPath(lines[i + 1]!);
        cur.hasPair = true;
        sections.push(cur);
      }
      i += 2;
      continue;
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new ParseFault(i + 1);
      const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(line);
      if (m === null) throw new ParseFault(i + 1);
      const hunk: Hunk = { start: Number(m[1]), body: [] };
      i++;
      while (i < lines.length) {
        const b = lines[i]!;
        if (b.startsWith('diff --git ')) break;
        if (b.startsWith('--- ') && pairAt(i)) break;
        if (!isBodyLine(b)) break;
        hunk.body.push(parseBodyLine(b));
        i++;
      }
      while (
        hunk.body.length > 0 &&
        hunk.body[hunk.body.length - 1]!.kind === 'ctx' &&
        hunk.body[hunk.body.length - 1]!.text === ''
      ) {
        hunk.body.pop();
      }
      cur.hunks.push(hunk);
      continue;
    }
    if (line.startsWith('--- ') && cur !== null && cur.hunks.length === 0) {
      throw new ParseFault(i + 2);
    }
    if (cur !== null && cur.hunks.length === 0) {
      if (line.startsWith('rename from ')) cur.renameOld = line.slice('rename from '.length).trim();
      else if (line.startsWith('rename to ')) cur.renameNew = line.slice('rename to '.length).trim();
      else if (line === 'new file mode' || line.startsWith('new file mode ')) cur.newFile = true;
      else if (line === 'deleted file mode' || line.startsWith('deleted file mode ')) cur.deletedFile = true;
    }
    i++;
  }
  return sections.map((s) => unifiedEdit(s, strict));
}

/** Apply a section's hunks in order to a file's text. `drift` tracks
 * the running change in line count between hunks. */
function applyHunks(text: string, hunks: Hunk[], strict: boolean, path: string): string {
  const file = splitFile(text);
  let drift = 0;
  for (const hunk of hunks) {
    const { oldLines, newItems } = splitBody(hunk.body);
    const noNewline = hunkHasNoNewline(hunk.body);
    if (oldLines.length === 0) {
      const at = Math.max(0, Math.min(hunk.start + drift, file.lines.length));
      const atEnd = at === file.lines.length;
      const inserted = newItems.map((item) => item.text);
      file.lines.splice(at, 0, ...inserted);
      if (atEnd) file.finalBreak = !noNewline;
      drift += inserted.length;
      continue;
    }
    const tier = firstTierWith(file.lines, oldLines, strict, 0, false);
    if (tier === null) throw new EditFault('no-match', path);
    const hits = findOccurrences(file.lines, oldLines, tier, 0);
    const target = hunk.start - 1 + drift;
    let at = hits[0]!;
    let best = Math.abs(at - target);
    for (const pos of hits) {
      const dist = Math.abs(pos - target);
      if (dist < best) {
        at = pos;
        best = dist;
      }
    }
    const rendered = renderNewLines(newItems, file.lines, at, oldLines, tier);
    const runsToEnd = at + oldLines.length === file.lines.length;
    file.lines.splice(at, oldLines.length, ...rendered);
    if (runsToEnd) file.finalBreak = !noNewline;
    drift += rendered.length - oldLines.length;
  }
  return joinFile(file);
}

function unifiedEdit(section: UnifiedSection, strict: boolean): EditFn {
  const oldPath = section.pairOld ?? section.renameOld ?? section.gitOld;
  const newPath = section.pairNew ?? section.renameNew ?? section.gitNew;
  return (tree: WorkTree) => {
    const isCreation = oldPath === null || section.newFile;
    const isDeletion = !isCreation && (newPath === null || section.deletedFile);
    if (isCreation) {
      const p = newPath ?? '/dev/null';
      if (!isSafePath(p)) throw new EditFault('unsafe', p);
      if (tree.read(p) !== null) throw new EditFault('exists', p);
      const plus: string[] = [];
      let lastPlus: { hunk: Hunk; index: number } | null = null;
      for (const hunk of section.hunks) {
        hunk.body.forEach((b, k) => {
          if (b.kind === 'new') {
            plus.push(b.text);
            lastPlus = { hunk, index: k };
          }
        });
      }
      let finalBreak = true;
      if (lastPlus !== null) {
        const next = lastPlus.hunk.body[lastPlus.index + 1];
        if (next !== undefined && next.kind === 'mark') finalBreak = false;
      }
      tree.write(p, plus.length === 0 ? '' : plus.join('\n') + (finalBreak ? '\n' : ''));
      return;
    }
    if (isDeletion) {
      const p = oldPath ?? '/dev/null';
      if (!isSafePath(p)) throw new EditFault('unsafe', p);
      if (tree.read(p) === null) throw new EditFault('missing', p);
      tree.write(p, null);
      return;
    }
    if (oldPath !== newPath) {
      const from = oldPath!;
      const to = newPath!;
      if (!isSafePath(from)) throw new EditFault('unsafe', from);
      if (!isSafePath(to)) throw new EditFault('unsafe', to);
      const current = tree.read(from);
      if (current === null) throw new EditFault('missing', from);
      if (tree.read(to) !== null) throw new EditFault('exists', to);
      const changed = applyHunks(current, section.hunks, strict, from);
      tree.write(from, null);
      tree.write(to, changed);
      tree.noteMove(from, to);
      return;
    }
    const p = oldPath!;
    if (!isSafePath(p)) throw new EditFault('unsafe', p);
    const current = tree.read(p);
    if (current === null) throw new EditFault('missing', p);
    tree.write(p, applyHunks(current, section.hunks, strict, p));
  };
}

// ---------------------------------------------------------------------------
// SEARCH/REPLACE blocks (SPEC.md section 7)
// ---------------------------------------------------------------------------

function parseSearchReplace(lines: string[], strict: boolean): EditFn[] {
  const edits: EditFn[] = [];
  let prevEnd = 0;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const searchAt = i;
    let path: string | null = null;
    for (let j = searchAt - 1; j >= prevEnd; j--) {
      const candidate = lines[j]!;
      if (isBlank(candidate)) continue;
      if (candidate.trim().startsWith('```')) continue;
      path = candidate.trim();
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new ParseFault(searchAt + 1);
      path = prevPath;
    }
    let eq = -1;
    for (let j = searchAt + 1; j < lines.length; j++) {
      const t = lines[j]!.trimEnd();
      if (t === '=======') {
        eq = j;
        break;
      }
      if (t === '>>>>>>> REPLACE') break;
    }
    if (eq < 0) throw new ParseFault(searchAt + 1);
    let rep = -1;
    for (let j = eq + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
    }
    if (rep < 0) throw new ParseFault(searchAt + 1);
    const oldLines = lines.slice(searchAt + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    edits.push(searchReplaceEdit(path, oldLines, newLines, strict));
    prevPath = path;
    prevEnd = rep + 1;
    i = rep + 1;
  }
  return edits;
}

function searchReplaceEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): EditFn {
  return (tree: WorkTree) => {
    if (!isSafePath(path)) throw new EditFault('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.read(path) !== null) throw new EditFault('exists', path);
      tree.write(path, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
      return;
    }
    const current = tree.read(path);
    if (current === null) throw new EditFault('missing', path);
    const file = splitFile(current);
    const tier = firstTierWith(file.lines, oldLines, strict, 0, false);
    if (tier === null) throw new EditFault('no-match', path);
    const hits = findOccurrences(file.lines, oldLines, tier, 0);
    if (hits.length > 1) throw new EditFault('ambiguous', path);
    const items: NewLine[] = newLines.map((text) => ({ ctxPos: null, text }));
    const rendered = renderNewLines(items, file.lines, hits[0]!, oldLines, tier);
    file.lines.splice(hits[0]!, oldLines.length, ...rendered);
    tree.write(path, joinFile(file));
  };
}

// ---------------------------------------------------------------------------
// V4A patches (SPEC.md section 8)
// ---------------------------------------------------------------------------

interface V4aChunk {
  anchor: string | null;
  body: BodyLine[];
  eof: boolean;
}

const V4A_HEADERS = ['*** Add File: ', '*** Delete File: ', '*** Update File: '];

function isV4aHeader(line: string): boolean {
  return V4A_HEADERS.some((h) => line.startsWith(h));
}

function parseV4a(lines: string[], strict: boolean): EditFn[] {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) throw new ParseFault(1);
  if (lines[first]!.trim() !== '*** Begin Patch') throw new ParseFault(first + 1);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k--) {
    if (!isBlank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (last < 0 || lines[last]!.trim() !== '*** End Patch') throw new ParseFault(lines.length + 1);
  const edits: EditFn[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (isBlank(line)) {
      i++;
      continue;
    }
    if (line.startsWith('*** Add File: ')) {
      const path = line.slice('*** Add File: '.length).trim();
      const collected: Array<{ text: string; blank: boolean }> = [];
      i++;
      while (i < last) {
        const l = lines[i]!;
        if (isV4aHeader(l)) break;
        if (l.startsWith('+')) {
          collected.push({ text: l.slice(1), blank: false });
          i++;
          continue;
        }
        if (isBlank(l)) {
          collected.push({ text: '', blank: true });
          i++;
          continue;
        }
        throw new ParseFault(i + 1);
      }
      while (collected.length > 0 && collected[collected.length - 1]!.blank) collected.pop();
      edits.push(v4aAddEdit(path, collected.map((c) => c.text)));
      continue;
    }
    if (line.startsWith('*** Delete File: ')) {
      const path = line.slice('*** Delete File: '.length).trim();
      i++;
      while (i < last) {
        const l = lines[i]!;
        if (isV4aHeader(l)) break;
        if (isBlank(l)) {
          i++;
          continue;
        }
        throw new ParseFault(i + 1);
      }
      edits.push(v4aDeleteEdit(path));
      continue;
    }
    if (line.startsWith('*** Update File: ')) {
      const path = line.slice('*** Update File: '.length).trim();
      const updateLine = i + 1;
      i++;
      let moveTo: string | null = null;
      if (i < last && lines[i]!.startsWith('*** Move to: ')) {
        moveTo = lines[i]!.slice('*** Move to: '.length).trim();
        i++;
      }
      const chunks: V4aChunk[] = [];
      let current: V4aChunk | null = null;
      let closedByEof = false;
      while (i < last) {
        const l = lines[i]!;
        if (isV4aHeader(l)) break;
        if (l === '*** End of File') {
          if (current === null) throw new ParseFault(i + 1);
          current.eof = true;
          chunks.push(current);
          current = null;
          closedByEof = true;
          i++;
          continue;
        }
        if (l.startsWith('@@')) {
          if (current !== null) chunks.push(current);
          current = { anchor: l.slice(2).trim(), body: [], eof: false };
          closedByEof = false;
          i++;
          continue;
        }
        if (l.startsWith('*** Move to: ')) throw new ParseFault(i + 1);
        if (isBlank(l) && current === null && (chunks.length > 0 || closedByEof)) {
          // A blank line with no chunk open: at the end of a section it
          // is not part of it, and between chunks it belongs to no chunk.
          i++;
          continue;
        }
        if (isBodyLine(l)) {
          if (current === null) {
            if (chunks.length > 0 || closedByEof) throw new ParseFault(i + 1);
            current = { anchor: null, body: [], eof: false };
          }
          current.body.push(parseBodyLine(l));
          i++;
          continue;
        }
        throw new ParseFault(i + 1);
      }
      if (current !== null) chunks.push(current);
      if (chunks.length > 0) {
        const tail = chunks[chunks.length - 1]!;
        while (tail.body.length > 0 && tail.body[tail.body.length - 1]!.blank) tail.body.pop();
      }
      if (chunks.length === 0 && moveTo === null) throw new ParseFault(updateLine);
      edits.push(v4aUpdateEdit(path, moveTo, chunks, strict));
      continue;
    }
    throw new ParseFault(i + 1);
  }
  return edits;
}

function v4aAddEdit(path: string, fileLines: string[]): EditFn {
  return (tree: WorkTree) => {
    if (!isSafePath(path)) throw new EditFault('unsafe', path);
    if (tree.read(path) !== null) throw new EditFault('exists', path);
    tree.write(path, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
  };
}

function v4aDeleteEdit(path: string): EditFn {
  return (tree: WorkTree) => {
    if (!isSafePath(path)) throw new EditFault('unsafe', path);
    if (tree.read(path) === null) throw new EditFault('missing', path);
    tree.write(path, null);
  };
}

function v4aUpdateEdit(path: string, moveTo: string | null, chunks: V4aChunk[], strict: boolean): EditFn {
  return (tree: WorkTree) => {
    if (!isSafePath(path)) throw new EditFault('unsafe', path);
    if (moveTo !== null && !isSafePath(moveTo)) throw new EditFault('unsafe', moveTo);
    const current = tree.read(path);
    if (current === null) throw new EditFault('missing', path);
    if (moveTo !== null && tree.read(moveTo) !== null) throw new EditFault('exists', moveTo);
    const file = splitFile(current);
    let cursor = 0;
    for (const chunk of chunks) {
      cursor = applyV4aChunk(file, chunk, cursor, path, strict);
    }
    const out = joinFile(file);
    if (moveTo !== null) {
      tree.write(path, null);
      tree.write(moveTo, out);
      tree.noteMove(path, moveTo);
    } else {
      tree.write(path, out);
    }
  };
}

/** Apply one V4A chunk to a file model, returning the cursor for the
 * next chunk: just after the lines this chunk wrote. */
function applyV4aChunk(file: FileModel, chunk: V4aChunk, cursor: number, path: string, strict: boolean): number {
  let at = cursor;
  if (chunk.anchor !== null && chunk.anchor !== '') {
    let found = -1;
    const tiers = strict ? [0] : [0, 1, 2];
    for (const tier of tiers) {
      for (let k = at; k < file.lines.length; k++) {
        if (tierKey(file.lines[k]!, tier) === tierKey(chunk.anchor, tier)) {
          found = k;
          break;
        }
      }
      if (found >= 0) break;
    }
    if (found < 0) throw new EditFault('no-match', path);
    at = found + 1;
  }
  const { oldLines, newItems } = splitBody(chunk.body);
  if (oldLines.length === 0) {
    const insertAt = chunk.eof ? file.lines.length : at;
    const inserted = newItems.map((item) => item.text);
    file.lines.splice(insertAt, 0, ...inserted);
    return insertAt + inserted.length;
  }
  const tier = firstTierWith(file.lines, oldLines, strict, at, chunk.eof);
  if (tier === null) throw new EditFault('no-match', path);
  const hits = findOccurrences(file.lines, oldLines, tier, at).filter(
    (pos) => !chunk.eof || pos + oldLines.length === file.lines.length,
  );
  if (hits.length === 0) throw new EditFault('no-match', path);
  const occ = hits[0]!;
  const rendered = renderNewLines(newItems, file.lines, occ, oldLines, tier);
  file.lines.splice(occ, oldLines.length, ...rendered);
  return occ + rendered.length;
}

// ---------------------------------------------------------------------------
// JSON edits (SPEC.md section 9)
// ---------------------------------------------------------------------------

function jsonEdit(value: unknown): EditFn | null {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return null;
  const obj = value as Record<string, unknown>;
  const p = obj.path;
  if (typeof p !== 'string') return null;
  if (obj.command === 'create') {
    if (typeof obj.file_text !== 'string') return null;
    const text = obj.file_text;
    return (tree: WorkTree) => {
      if (!isSafePath(p)) throw new EditFault('unsafe', p);
      if (tree.read(p) !== null) throw new EditFault('exists', p);
      tree.write(p, text);
    };
  }
  if (obj.command === 'str_replace') {
    if (typeof obj.old_str !== 'string' || obj.old_str === '') return null;
    if (obj.new_str !== undefined && typeof obj.new_str !== 'string') return null;
    const oldStr = obj.old_str;
    const newStr = (obj.new_str as string | undefined) ?? '';
    return (tree: WorkTree) => {
      if (!isSafePath(p)) throw new EditFault('unsafe', p);
      const before = tree.read(p);
      if (before === null) throw new EditFault('missing', p);
      const crlf = splitFile(before).br === '\r\n';
      const toLf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const text = toLf(before);
      const old = toLf(oldStr);
      const replacement = toLf(newStr);
      let count = 0;
      let at = -1;
      for (let k = text.indexOf(old); k >= 0; k = text.indexOf(old, k + 1)) {
        count++;
        if (at < 0) at = k;
      }
      if (count === 0) throw new EditFault('no-match', p);
      if (count > 1) throw new EditFault('ambiguous', p);
      const out = text.slice(0, at) + replacement + text.slice(at + old.length);
      tree.write(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (obj.command === 'insert') {
    if (typeof obj.insert_line !== 'number' || !Number.isInteger(obj.insert_line)) return null;
    if (typeof obj.new_str !== 'string') return null;
    const lineNo = obj.insert_line;
    const added = patchLines(obj.new_str);
    return (tree: WorkTree) => {
      if (!isSafePath(p)) throw new EditFault('unsafe', p);
      const before = tree.read(p);
      if (before === null) throw new EditFault('missing', p);
      const file = splitFile(before);
      if (lineNo < 0 || lineNo > file.lines.length) throw new EditFault('no-match', p);
      file.lines.splice(lineNo, 0, ...added);
      tree.write(p, joinFile(file));
    };
  }
  return null;
}

function parseJson(text: string, lines: string[]): EditFn[] {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) throw new ParseFault(1);
  const edits: EditFn[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let value: unknown;
    try {
      value = JSON.parse(text);
    } catch {
      throw new ParseFault(first + 1);
    }
    if (!Array.isArray(value)) throw new ParseFault(first + 1);
    for (const item of value) {
      const edit = jsonEdit(item);
      if (edit === null) throw new ParseFault(first + 1);
      edits.push(edit);
    }
    return edits;
  }
  lines.forEach((line, index) => {
    if (isBlank(line)) return;
    let edit: EditFn | null = null;
    try {
      edit = jsonEdit(JSON.parse(line));
    } catch {
      edit = null;
    }
    if (edit === null) throw new ParseFault(index + 1);
    edits.push(edit);
  });
  return edits;
}

// ---------------------------------------------------------------------------
// Running the patch (SPEC.md sections 1, 2 and 10)
// ---------------------------------------------------------------------------

function usageResult(): { code: number; out: string[] } {
  return { code: 2, out: ['error: usage'] };
}

function run(argv: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let checkOnly = false;
  let strict = false;
  const positional: string[] = [];
  let afterDashDash = false;
  for (const arg of argv) {
    if (!afterDashDash && arg === '--') {
      afterDashDash = true;
      continue;
    }
    if (!afterDashDash && arg.startsWith('-') && arg !== '-') {
      if (arg.startsWith('--format=')) {
        if (format !== null) return usageResult();
        const value = arg.slice('--format='.length);
        if (!(FORMAT_NAMES as readonly string[]).includes(value)) return usageResult();
        format = value;
      } else if (arg === '--check') {
        if (checkOnly) return usageResult();
        checkOnly = true;
      } else if (arg === '--strict') {
        if (strict) return usageResult();
        strict = true;
      } else {
        return usageResult();
      }
    } else {
      positional.push(arg);
    }
  }
  if (positional.length > 1) return usageResult();
  const patchArg = positional.length === 0 ? null : positional[0]!;
  let patchText = '';
  if (patchArg === null || patchArg === '-') {
    try {
      patchText = readFileSync(0, 'utf8');
    } catch {
      patchText = '';
    }
  } else {
    try {
      patchText = readFileSync(patchArg, 'utf8');
    } catch {
      return { code: 2, out: ['error: no-patch'] };
    }
  }
  const lines = patchLines(patchText);
  const kind = format === null || format === 'auto' ? detectFormat(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: EditFn[];
  try {
    if (kind === 'unified') edits = parseUnified(lines, strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else if (kind === 'v4a') edits = parseV4a(lines, strict);
    else edits = parseJson(patchText, lines);
  } catch (e) {
    if (e instanceof ParseFault) return { code: 2, out: [`error: parse ${e.line}`] };
    throw e;
  }
  if (edits.length === 0) return { code: 2, out: ['error: parse 1'] };
  const tree = new WorkTree();
  const failures: EditFault[] = [];
  for (const edit of edits) {
    const snap = tree.snapshot();
    const movesBefore = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof EditFault)) throw e;
      tree.restore(snap);
      tree.moves.length = movesBefore;
      failures.push(e);
    }
  }
  if (failures.length > 0) {
    return {
      code: 1,
      out: [...failures.map((f) => `error: ${f.code} ${f.path}`), `failed: ${failures.length} of ${edits.length} edits`],
    };
  }
  const rows = describeChanges(tree);
  if (!checkOnly) writeChanges(tree);
  return { code: 0, out: [...rows, `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

/** The output lines for the tree's changes: one per changed path, in
 * byte order, with a move printed as one R line sorted by its new
 * path instead of a D and an A line. */
function describeChanges(tree: WorkTree): string[] {
  const changed = new Map<string, { was: string | null; now: string | null }>();
  for (const p of tree.touchedPaths()) {
    const was = tree.original(p);
    const now = tree.read(p);
    if (was !== now) changed.set(p, { was, now });
  }
  const used = new Set<string>();
  const rows: Array<{ key: string; text: string }> = [];
  for (const move of tree.moves) {
    const from = changed.get(move.from);
    const to = changed.get(move.to);
    if (
      from !== undefined &&
      from.was !== null &&
      from.now === null &&
      to !== undefined &&
      to.was === null &&
      to.now !== null &&
      !used.has(move.from) &&
      !used.has(move.to)
    ) {
      rows.push({ key: move.to, text: `R ${move.from} -> ${move.to}` });
      used.add(move.from);
      used.add(move.to);
    }
  }
  for (const [p, c] of changed) {
    if (used.has(p)) continue;
    const kind = c.was === null ? 'A' : c.now === null ? 'D' : 'M';
    rows.push({ key: p, text: `${kind} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key, 'utf8'), Buffer.from(b.key, 'utf8')));
  return rows.map((r) => r.text);
}

/** Write every change to disk. */
function writeChanges(tree: WorkTree): void {
  for (const p of tree.touchedPaths()) {
    const was = tree.original(p);
    const now = tree.read(p);
    if (was === now) continue;
    if (now === null) {
      rmSync(p, { force: true });
    } else {
      mkdirSync(dirname(p), { recursive: true });
      writeFileSync(p, now);
    }
  }
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this
  // file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const result = run(process.argv.slice(2));
  writeSync(1, result.out.map((line) => `${line}\n`).join(''));
  process.exitCode = result.code;
}
