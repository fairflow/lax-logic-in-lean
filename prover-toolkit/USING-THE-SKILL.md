# Using `prove-lemma-inloop` — the five-minute version

You will not remember this. That is what this file is for. It documents the
**in-loop** route, where Claude is the proposer and the toolkit only supplies
retrieval, goal states and verification. For the hosted-API route
(`prove-lemma`, which spends money per attempt), see `README.md`.

## Install the skill, once per machine

```bash
cp -r prover-toolkit/skill/prove-lemma-inloop ~/.claude/skills/
```

Re-run that after any change to `prover-toolkit/skill/` — the installed copy
does **not** track the repository, and a stale copy is how the wrong port
(8080, a different private corpus) survived for a session.

## Bring it up, once per worktree

```bash
python3 prover-toolkit/leansearch/build_index.py
python3 prover-toolkit/leansearch/server.py &
curl -s localhost:8081/health
```

Three things worth knowing:

- **`build_index.py` is not optional on a fresh worktree.** `index.jsonl` is
  derived data and is git-ignored, so a new worktree has none, and the server
  dies with `FileNotFoundError` rather than building one.
- **The port comes from `prover-toolkit/toolkit.json`** (8081 here). Port 8080
  is a launchd service over a different, private corpus. Do not use it.
- **No environment variable is needed.** The config is found by walking up from
  the working directory. `PROVER_TOOLKIT_CONFIG` only overrides that.

In a Claude worktree you also need the build cache, or every check takes twenty
minutes instead of five seconds:

```bash
/bin/cp -Rc <repo-root>/.lake .lake
```

## When port 8081 is already taken

`toolkit.json` pins one port, and every worktree of the clone shares it, so any
two sessions running the toolkit at once collide. `server.py` then dies with
`EADDRINUSE`, and from the outside a listener is indistinguishable from a live
session mid-query.

**Do not kill it before establishing whose it is.** Two checks settle it:

```bash
lsof -nP -iTCP:8081 -sTCP:LISTEN            # the PID
lsof -a -p <pid> -d cwd -Fn                 # which worktree it serves
curl -s localhost:8081/health               # its entry count
```

A working directory that is not yours, together with an entry count that does
not match your own `index.jsonl`, means the server belongs to another session:
ask that session to stop it rather than killing it. A working directory that
*is* yours makes it a stale server of your own, safe to stop. Kill by **PID**,
never `pkill -f leansearch/server.py` — that pattern matches every session's
server, not only your own.

Count your own index with:

```bash
python3 -c "print(sum(1 for l in open('prover-toolkit/leansearch/index.jsonl') if l.strip()))"
```

Port 8080 is a launchd service over a different, private corpus. Leave it be.

## Use it

Say what you want, and name the file:

> Prove the `sorry` in `LaxLogic/Foo.lean` using the prove-lemma-inloop skill.

or invoke it by name: `/prove-lemma-inloop LaxLogic/Foo.lean`.

## The three commands it runs

You can run all three yourself; nothing here is agent-only.

```bash
python3 prover-toolkit/toolkit_cli.py goals  LaxLogic/Foo.lean
python3 prover-toolkit/toolkit_cli.py search "erasure preserves derivability" -n 8
python3 prover-toolkit/toolkit_cli.py check  LaxLogic/Foo.lean my_theorem
```

`goals` shows the open goal at each `sorry` as Lean reports it. `search`
queries the corpus index. `check` compiles and reports whether `sorryAx`
survives and which axioms the proof rests on — this is the one that matters.

## Verifying a result without trusting `check`

`check` had a bug where it passed files containing `sorry`. It is fixed, and
you should still confirm independently, because the whole point of the toolkit
is that the verification is trustworthy:

```bash
lake env lean LaxLogic/Foo.lean          # expect zero errors, zero warnings
```

Then pin the axioms explicitly. Append to a **copy** of the file (namespaces
are still open at the end of most files here, so close them first):

```lean
end MyNamespace

#print axioms MyNamespace.my_theorem
```

`[propext, Quot.sound]` is the ordinary baseline in this development.
`Classical.choice` appearing where it did not before is worth chasing — though
it is often inherited from a lemma the proof uses rather than needed by the
proof itself, so check the dependencies before concluding anything.

Do **not** certify a file with `grep -c sorry`: `grep` here wraps `ugrep -I`
and silently skips any file containing a NUL byte. Read the bytes, or trust
`#print axioms`, which catches a `sorry` reached through a helper too.

## Writing a good search query

Retrieval is lexical BM25 over `name + signature + docstring + module` — there
is no semantic layer, no stemming, and no type-directed search. Consequences,
all measured (see `docs/toolkit-test-design.md` §3):

- **Use the vocabulary the docstring would use**, not the vocabulary of what
  you want. `soundness` and `sound` are unrelated tokens; the same query with
  one suffix changed moved its target from rank 23 to rank 2.
- **Ask for more than you think.** Short queries are much weaker: with a
  four-word query the right theorem is top-1 only 43% of the time, though
  top-10 87%. Use `-n 15` and read the list.
- **Theorems rank below definitions**, deliberately (`KIND_BOOST` in
  `leansearch/server.py`). If you want a lemma to apply rather than a
  definition to understand, expect it lower than it deserves.
- **43% of theorems in this development have no docstring.** Those are
  reachable only by a query containing their identifiers — which is no help
  when the identifier is the thing you are missing. `grep` beats `search`
  whenever you can guess a name fragment.

## When it fails

An open conjecture may be open because it is false. Before grinding, look for
a countermodel — this repository has the machinery (`PLLSearch`, `#draw`). A
`sorry` you did not close is a failure to report, not a proof; and per the
standing rule in this development, a `sorry` *asserts*, so a relation still to
be determined must not be recorded as a sorried theorem at all.
