// node --test .github/scripts/outside-guard.test.mjs
// The plain-file rule of outside-guard.mjs: one fixture per way a proof file could carry code
// that runs while it compiles (or hide it from a reader), and the honest shapes that must pass.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { checkImports, checkOwnNamespace } from './outside-guard.mjs';

const head = 'import Mathlib\nimport PEqualNP.Defs\n\n';
const run = (body) => checkImports(new TextEncoder().encode(head + body), ['PEqualNP.Defs']);
const refused = (name, body, word) => test(`refused: ${name}`, () => {
  assert.throws(() => run(body), (e) => e.message.includes(word), 'not refused, or for another reason');
});
// What passes passes the whole `imports` mode: the plain-file rule and the own-namespace rule.
const passes = (name, body) => test(`passes: ${name}`, () => {
  assert.deepEqual(run(body), ['Mathlib', 'PEqualNP.Defs']);
  checkOwnNamespace(head + body, 'PEqualNP.Outside.L_x_1');
});
const thm = 'theorem PEqualNP.Outside.L_x_1 : True := trivial\n';
const by = (tac) => `theorem PEqualNP.Outside.L_x_1 : True := by\n  ${tac}\n`;

refused('an initialize', `initialize pure ()\n${thm}`, 'initialize');
refused('an indented initialize', `${thm}  initialize pure ()\n`, 'initialize');
refused('run_cmd, indented', `${thm} run_cmd pure ()\n`, 'run_cmd');
refused('#eval', `${thm} #eval 1\n`, '#');
refused('a tactic that runs code', by('run_tac (do return ())'), 'run_tac');
refused('an elaborator, indented', `${thm} elab x : term => pure default\n`, 'elab');
refused('a macro, indented', `${thm} macro x : tactic => y\n`, 'macro');
refused('notation3', `${thm} notation3 x => y\n`, 'notation');
refused('an attribute command', `${thm} attribute [simp] Nat.add_comm\n`, 'attribute');
refused('a generating attribute', `@[to_additive] theorem foo : True := trivial\n${thm}`, '@[');
refused('an option that is not a limit', `set_option debug.skipKernelTC true in\n${thm}`, 'set_option');
refused('an indented option that is not a limit', by('set_option debug.skipKernelTC true in\n  trivial'), 'set_option');
refused('a same-line option that is not a limit', `set_option maxHeartbeats 1 in set_option debug.skipKernelTC true in\n${thm}`, 'set_option');
refused('an axiom', `${thm} axiom a : False\n`, 'axiom');
refused('sorry', by('sorry'), 'sorry');
refused('sorryAx', 'theorem PEqualNP.Outside.L_x_1 : False := sorryAx _\n', 'sorry');
refused('lcProof', 'theorem PEqualNP.Outside.L_x_1 : False := lcProof\n', 'lcProof');
refused('native_decide', by('native_decide'), 'native');
refused('decide +native', by('decide +native'), 'native');
refused('bv_decide', by('bv_decide'), 'bv_decide');
refused('a simproc', `${thm}  simproc foo (x) := y\n`, 'simproc');
refused('open Lean', `open Lean in\n${thm}`, 'Lean');
refused('ofReduceBool', by('exact ofReduceBool x true rfl'), 'ofReduce');
refused('_root_', by('exact _root_.id trivial'), '_root_');
refused('include_str', by('exact include_str x'), 'include_str');
refused('polyrith', by('polyrith'), 'polyrith');
refused('a string literal', `private def s : String := "x"\n${thm}`, '"');
refused('a character-literal trick', `${thm}  -- '"'\n`, '"');
refused('a quoted identifier', `private def «a» : Nat := 1\n${thm}`, '«');
refused('code hidden behind a comment trick', `-- a note /- here\n  initialize pure ()\n-- done -/\n${thm}`, 'initialize');
refused('a command after a comment on one line', `/- note -/ initialize pure ()\n${thm}`, 'initialize');
refused('a syntax quotation', by('exact \x60(tactic| trivial)'), '(tactic|');
refused('#check', `#check Nat\n${thm}`, '#check');
refused('#print axioms, indented', `${thm}  #print axioms Nat.add_comm\n`, '#print');
refused('a direction-changing character', `-- ‮\n${thm}`, 'invisible');
refused('no theorem at all', 'def x : Nat := 1\n', 'no theorem');
// Commands that take an explicit target name could place a declaration outside the file's own
// namespace; refused anywhere until tested in Lean (red team, read of the own-namespace rule).
refused('mk_iff_of_inductive_prop', `mk_iff_of_inductive_prop Foo Bar.baz\n${thm}`, 'mk_iff_of_inductive_prop');
refused('proof_wanted', `proof_wanted foo : True\n${thm}`, 'proof_wanted');
refused('an attribute that takes a target name', `@[to_additive Foo.bar] theorem t : True := trivial\n${thm}`, '@[');

passes('one theorem', thm);
passes('helpers, definitions, namespaces, a docstring', `namespace PEqualNP.Outside.L_x_1\nopen Finset\nvariable {n : ℕ}\n/-- A doc comment. -/\nprivate def f (x : ℕ) : ℕ := x\nprivate lemma l : f 1 = 1 := rfl\nend PEqualNP.Outside.L_x_1\n\n${thm}`);
passes('a block comment with indented prose', `/-\n  The idea of the proof,\n  in two lines.\n-/\n${thm}`);
passes('the simp attributes', `namespace PEqualNP.Outside.L_x_1\n@[simp] private theorem a : True := trivial\n@[local simp] private theorem b : True := trivial\nend PEqualNP.Outside.L_x_1\n${thm}`);
passes('the four limit options', `set_option maxHeartbeats 400000 in\nset_option maxRecDepth 2000 in\n${thm}`);
passes('an indented limit option inside a proof', by('set_option maxRecDepth 2000 in\n  trivial'));
passes('comment prose at column 0 and a heading (form is not judged)', `/-!\n# A heading\n\nProse that starts in column 0,\nover two lines.\n-/\n${thm}`);
passes('a small enumerated type and an instance', `namespace PEqualNP.Outside.L_x_1\nprivate inductive Stack | input | output\n  deriving DecidableEq\n\nprivate instance : Inhabited Stack := ⟨.input⟩\nend PEqualNP.Outside.L_x_1\n${thm}`);
passes('open scoped, and a cardinality written with a hash', `open scoped BigOperators\ntheorem PEqualNP.Outside.L_x_1 (s : Finset ℕ) : #s = #s := rfl\n`);
passes('a pair in backticks inside a doc comment', '/-- The coordinates \x60(a, b, c, d)\x60 of the block. -/\n' + thm);
passes('lemma names that contain add_', by('simp only [Nat.add_comm, add_zero]'));

// The closure rule: which listed modules the base step may build, and which are outside-written
// and built only in the locked step. The base tree is a map here; `read` answers null for a file
// that is not a plain file of the base tree.
import { importClosure, headerImports } from './outside-guard.mjs';
const tree = (files) => (m) => (m in files ? new TextEncoder().encode(files[m]) : null);
const proof = (imports, name = 'PEqualNP.Outside.L_x_2') => `${imports.map((m) => `import ${m}\n`).join('')}\ntheorem ${name} : True := trivial\n`;
const judged = 'PEqualNP.Outside.L_x_1';
const closure = (listed, files) => importClosure(listed, tree(files), judged);
const closureRefused = (name, listed, files, word) => test(`closure refused: ${name}`, () => {
  assert.throws(() => closure(listed, files), (e) => e.message.includes(word), 'not refused, or for another reason');
});

test('closure: base modules only, as before', () => {
  assert.deepEqual(closure(['PEqualNP.Gct.A'], { 'PEqualNP.Gct.A': 'import Mathlib\nimport PEqualNP.Gct.B\n', 'PEqualNP.Gct.B': '-- note\nimport PEqualNP.Defs\n', 'PEqualNP.Defs': 'import Mathlib\n' }),
    { outside: [], base: ['PEqualNP.Defs', 'PEqualNP.Gct.A', 'PEqualNP.Gct.B'] });
});
test('closure: a listed outside module is never handed to the base step; the base modules it imports are', () => {
  const r = closure(['PEqualNP.Outside.L_meta_473'], {
    'PEqualNP.Outside.L_meta_473': proof(['Mathlib', 'PEqualNP.Defs', 'PEqualNP.Outside.L_meta_9'], 'PEqualNP.Outside.L_meta_473'),
    'PEqualNP.Outside.L_meta_9': proof(['Mathlib', 'PEqualNP.Gct.L090'], 'PEqualNP.Outside.L_meta_9'),
    'PEqualNP.Defs': 'import Mathlib\n', 'PEqualNP.Gct.L090': 'import PEqualNP.Defs\n' });
  assert.deepEqual(r, { outside: ['PEqualNP.Outside.L_meta_473', 'PEqualNP.Outside.L_meta_9'], base: ['PEqualNP.Defs', 'PEqualNP.Gct.L090'] });
});
closureRefused('the judged file itself', [judged], {}, 'the file being judged');
closureRefused('an outside module that imports the judged file', ['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': proof([judged]) }, 'the file being judged');
closureRefused('a listed module missing from the base', ['PEqualNP.Outside.L_x_9'], {}, 'not a plain file of the base tree');
closureRefused('a listed base module missing from the base', ['PEqualNP.Gct.Nope'], {}, 'not a plain file of the base tree');
closureRefused('a base module that imports an outside module', ['PEqualNP.Gct.A'], { 'PEqualNP.Gct.A': 'import PEqualNP.Gct.B\n', 'PEqualNP.Gct.B': '/- x -/ import PEqualNP.Outside.L_x_2\n', 'PEqualNP.Outside.L_x_2': proof(['Mathlib']) }, 'imports the outside-written');
closureRefused('a base module behind an outside module that imports another outside module', ['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': proof(['PEqualNP.Gct.B']), 'PEqualNP.Gct.B': 'import PEqualNP.Outside.L_x_3\n', 'PEqualNP.Outside.L_x_3': proof([]) }, 'imports the outside-written');
closureRefused('an outside module that runs code when it compiles', ['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': `import Mathlib\ninitialize pure ()\n${thm}` }, 'initialize');
closureRefused('an outside module with an import below its header', ['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': `import Mathlib\n${thm}/- -/ import PEqualNP.Gct.B\n` }, 'the word "import"');
closureRefused('an outside module importing something not Mathlib and not the project', ['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': proof(['Lean.Elab']) }, 'not allowed');
closureRefused('a module under Outside that is not a proof file name', ['PEqualNP.Outside.Helper'], { 'PEqualNP.Outside.Helper': proof(['Mathlib']) }, 'not the name of an outside proof file');
test('closure: a cycle between outside modules ends', () => {
  assert.deepEqual(closure(['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': proof(['PEqualNP.Outside.L_x_3']), 'PEqualNP.Outside.L_x_3': proof(['PEqualNP.Outside.L_x_2']) }).outside, ['PEqualNP.Outside.L_x_2', 'PEqualNP.Outside.L_x_3']);
});

test('header: comments, module, modifiers, quoted names', () => {
  assert.deepEqual(headerImports('/- a /- nested -/ b -/\n-- c\nmodule\npublic import «PEqualNP».Outside.L_x_2\nmeta import all Mathlib.Tactic\nimport PEqualNP.Defs -- d\n\ntheorem t : True := trivial\n', 'm'),
    ['PEqualNP.Outside.L_x_2', 'Mathlib.Tactic', 'PEqualNP.Defs']);
});
test('header: an import line below the header is refused, never passed over', () => {
  assert.throws(() => headerImports('import Mathlib\ndef x := 1\nimport PEqualNP.Outside.L_x_2\n', 'm'), /below its header/);
});

// Reached base modules are under the PEqualNP root only, and outside modules are capped.
import { MAX_OUTSIDE } from './outside-guard.mjs';
closureRefused('a listed fixture module', ['CheckerSuite.Pass'], { 'CheckerSuite.Pass': 'import Mathlib\n' }, 'not under the PEqualNP root');
closureRefused('a base module that imports a fixture module', ['PEqualNP.Gct.A'], { 'PEqualNP.Gct.A': 'import CheckerSuite.Pass\n', 'CheckerSuite.Pass': 'import Mathlib\n' }, 'not under the PEqualNP root');
closureRefused('an outside module that imports a fixture module', ['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': proof(['CheckerSuite.Pass']), 'CheckerSuite.Pass': 'import Mathlib\n' }, 'not under the PEqualNP root');
const many = (n) => Object.fromEntries(Array.from({ length: n }, (_, k) => [`PEqualNP.Outside.L_x_${k + 10}`, proof(['Mathlib'], `PEqualNP.Outside.L_x_${k + 10}`)]));
test(`closure: ${MAX_OUTSIDE} outside modules pass`, () => {
  assert.equal(MAX_OUTSIDE, 16);
  assert.equal(closure(Object.keys(many(MAX_OUTSIDE)), many(MAX_OUTSIDE)).outside.length, MAX_OUTSIDE);
});
closureRefused(`${MAX_OUTSIDE + 1} outside modules listed`, Object.keys(many(MAX_OUTSIDE + 1)), many(MAX_OUTSIDE + 1), `more than ${MAX_OUTSIDE} outside modules`);
test(`closure refused: ${MAX_OUTSIDE + 1} outside modules, one listed and the rest reached through it`, () => {
  const files = many(MAX_OUTSIDE);
  files['PEqualNP.Outside.L_x_1000'] = proof(Object.keys(many(MAX_OUTSIDE)), 'PEqualNP.Outside.L_x_1000');
  assert.throws(() => closure(['PEqualNP.Outside.L_x_1000'], files), /more than 16 outside modules/);
});

// The own-namespace rule (checkOwnNamespace): every helper inside the file's own namespace block,
// PEqualNP.Outside.L_<x> or PEqualNP.Outside.L_<x>_aux (or below them); at the top level only the
// imports, `open` lines, the four limit options, those blocks and the one theorem, last.
const own = (file, body) => checkOwnNamespace(head + body, file);
const M = 'PEqualNP.Outside.L_meta_9';
const t9 = `theorem ${M} : True := by\n  trivial\n`;
const ownPasses = (name, body, mod = M) => test(`own namespace passes: ${name}`, () => { own(mod, body); });
const ownRefused = (name, body, word, mod = M) => test(`own namespace refused: ${name}`, () => {
  assert.throws(() => own(mod, body), (e) => e.message.includes(word), 'not refused, or for another reason');
});
ownPasses('only the theorem', t9);
ownPasses('helpers inside the own namespace', `namespace ${M}\n\ndef f (n : ℕ) : ℕ := n\nlemma l : f 1 = 1 := rfl\n\nend ${M}\n\nopen ${M} in\n${t9}`);
ownPasses('nested namespace and sections inside it', `namespace ${M}\nnamespace Helpers\nsection\nvariable {n : ℕ}\ntheorem a : n = n := rfl\nend\nnoncomputable section Reals\ndef g : ℕ := 0\nend Reals\nend Helpers\nend ${M}\n${t9}`);
ownPasses('the _aux form, a dotted block below it, and the block opened twice', `namespace ${M}_aux\ntheorem a : True := trivial\nend ${M}_aux\nnamespace ${M}_aux.Helpers\ntheorem b : True := trivial\nend ${M}_aux.Helpers\nnamespace ${M}.More\ntheorem c : True := trivial\nend ${M}.More\n${t9}`);
ownPasses('a where block after the theorem (its helpers carry no command word)', `theorem ${M} : 2 = 2 := by\n  exact aux 2\nwhere\n  aux (n : ℕ) : n = n := by\n    induction n with\n    | zero => rfl\n    | succ k ih => rfl\n  termination_by structural n\n`);
ownPasses('mutual inside the own namespace', `namespace ${M}\nmutual\ndef ev : ℕ → Bool\n  | 0 => true\n  | n + 1 => od n\ndef od : ℕ → Bool\n  | 0 => false\n  | n + 1 => ev n\nend\nend ${M}\n${t9}`);
ownPasses('comments, a doc comment, limit options and open lines at the top level', `/-! notes\ndef not_code : ℕ := 0\n-/\nopen Finset\n-- def nor_this : ℕ := 0\nset_option maxHeartbeats 400000 in\n/-- The step. -/\n${t9}`);
ownPasses('a statement over several lines, some at column 0', `theorem ${M} :\n∀ n : ℕ,\n  n = n := by\n  intro n\n  rfl\n`);
ownPasses('a comment after the proof', `namespace ${M}\ntheorem a : True := trivial\nend ${M}\n${t9}-- trailing note\n`);

ownRefused('a helper at the top level', `def f : ℕ := 1\n${t9}`, 'line 4: a declaration');
ownRefused('a private helper at the top level', `private lemma l : True := trivial\n${t9}`, 'line 4: a declaration');
ownRefused('a helper declared with the own name at the top level', `theorem ${M}.a : True := trivial\n${t9}`, 'line 4: a declaration');
ownRefused('the project namespace at the top level', `namespace PEqualNP.Library.Machines\ndef f : ℕ := 1\nend PEqualNP.Library.Machines\n${t9}`, '`namespace PEqualNP.Library.Machines` at the top level');
ownRefused('namespace PEqualNP.Outside with the short theorem name', `namespace PEqualNP.Outside\ntheorem L_meta_9 : True := trivial\nend PEqualNP.Outside\n`, '`namespace PEqualNP.Outside` at the top level');
ownRefused('a second top-level namespace after the own one closed', `namespace ${M}\ndef f : ℕ := 1\nend ${M}\nnamespace Other\ndef g : ℕ := 1\nend Other\n${t9}`, 'line 7: `namespace Other`');
ownRefused('an indented namespace', `namespace ${M}\n  namespace Inner\n  end Inner\nend ${M}\n${t9}`, 'line 5: `namespace`, `section`, `end`');
ownRefused('an indented end that would close the own block early', `namespace ${M}\ndef f : ℕ := 1\n  end ${M}\ndef PEqualNP.Library.g : ℕ := 1\nend ${M}\n${t9}`, 'line 6: `namespace`, `section`, `end`');
ownRefused('an end in the middle of a line', `namespace ${M}\ndef f : ℕ := 1 end ${M}\ndef g : ℕ := 1\n${t9}`, 'line 5: `namespace`, `section`, `end`');
ownRefused('the own block closed, then a helper', `namespace ${M}\ndef f : ℕ := 1\nend ${M}\ndef g : ℕ := 1\n${t9}`, 'line 7: a declaration');
ownRefused('an end that names a part of the own namespace', `namespace ${M}\nend L_meta_9\ndef g : ℕ := 1\n${t9}`, 'does not name what it closes');
ownRefused('an end with nothing open', `end ${M}\n${t9}`, 'nothing open');
ownRefused('a bare end closing a namespace', `namespace ${M}\nend\n${t9}`, 'does not name what it closes');
ownRefused('the namespace of ANOTHER step that shares a prefix', `namespace PEqualNP.Outside.L_meta_99\ndef f : ℕ := 1\nend PEqualNP.Outside.L_meta_99\n${t9}`, '`namespace PEqualNP.Outside.L_meta_99` at the top level');
ownRefused('the _aux namespace of ANOTHER step that shares a prefix', `namespace PEqualNP.Outside.L_meta_99_aux\nend PEqualNP.Outside.L_meta_99_aux\n${t9}`, 'at the top level');
ownRefused('a name that only starts like the own one', `namespace ${M}x\nend ${M}x\n${t9}`, 'at the top level');
ownRefused('a section at the top level', `section\ndef f : ℕ := 1\nend\n${t9}`, 'a section at the top level');
ownRefused('noncomputable section at the top level', `noncomputable section\ndef f : ℕ := 1\nend\n${t9}`, 'a section at the top level');
ownRefused('mutual at the top level', `mutual\ndef f : ℕ := 1\nend\n${t9}`, '`mutual` at the top level');
ownRefused('a helper after the theorem', `${t9}\ndef PEqualNP.Library.g : ℕ := 1\n`, 'after the theorem');
ownRefused('an indented helper after the theorem, as if in the proof', `${t9}  def g : ℕ := 1\n`, 'after the theorem');
ownRefused('a namespace after the theorem', `${t9}namespace ${M}\nend ${M}\n`, 'nothing but the proof may follow');
ownRefused('a second theorem after the theorem', `${t9}theorem x : True := trivial\n`, 'after the theorem');
ownRefused('a command hidden after a comment on a top-level line', `/- note -/ def f : ℕ := 1\n${t9}`, 'line 4: a declaration');
ownRefused('open ... in with a helper on the same line', `open Finset in def f : ℕ := 1\n${t9}`, 'must end with `in`');
ownRefused('a simp helper at the top level', `@[simp] theorem a : True := trivial\n${t9}`, 'line 4: a declaration');
ownRefused('variable at the top level', `variable {n : ℕ}\n${t9}`, 'line 4: a declaration');
ownRefused('no theorem with the full name', `namespace ${M}\ntheorem x : True := trivial\nend ${M}\n`, 'the theorem must stand at the top level');
ownRefused('a theorem of another step', `theorem PEqualNP.Outside.L_meta_99 : True := trivial\n`, 'line 4: a declaration');
ownRefused('a file name ending in _aux', `theorem PEqualNP.Outside.L_meta_9_aux : True := trivial\n`, 'may not end in _aux', 'PEqualNP.Outside.L_meta_9_aux');

// The add_ rule's sentence names the way round for an honest proof line.
refused('a proof line that begins with a lemma named add_...', `theorem PEqualNP.Outside.L_x_1 : True := by\n  exact\n    add_or_out\n`, 'may not BEGIN with a name that starts with add_');
// A file-wide limit option is refused with the one fix named; anything else set file-wide gets no such hint.
refused('a limit option set for the whole file', `set_option maxHeartbeats 400000\n${thm}`, 'write it as set_option <option> <value> in');
refused('a file-wide option that is not a limit', `set_option autoImplicit true\n${thm}`, 'no options but the four limits');
test('no limit hint for an option that is not a limit', () => {
  assert.throws(() => run(`set_option autoImplicit true\n${thm}`), (e) => !e.message.includes('write it as set_option'));
});
refused('an add_ command still refused', `add_decl_doc Nat.succ\n${thm}`, '"add_decl_doc" is not allowed');
