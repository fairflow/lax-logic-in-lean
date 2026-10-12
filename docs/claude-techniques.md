# Claude Techniques: keeping long agent work on course

2026-10-12, drafted by the locus overseer session for Matthew, from what
happened in the locus repository on 10 to 12 October and from the record. A
companion to *GitHub with Claude* (`docs/github-with-claude-tutorial.md`):
that document is about repositories; this one is about contexts,
instructions, memory and communication between agents. Dated incidents are
cited so a rule can be traced to its cause. DRAFT.

## 1. Why long work drifts

A long session's context is summarised when it fills, and this can happen
several times in a day. Each summary keeps recent detail and compresses what
came early. The overall direction is usually set early and in conversation, so
it is the first thing to fade. The agent then follows every recent message
faithfully and still moves away from the goal.

Two more causes, in Matthew's words (2026-10-12): instructions that "have been
forgotten", and instructions that are "inconsistent between the rules for the
agents in the different lanes" and the manager. The person experiences this as
having to steer again and again:

> "I feel that I'm constantly trying to steer you in some direction and that
> you're drifting and that the system is drifting all the time."

The cures below share one idea: anything that must survive a summary lives in
a short file with one owner, and is put back into the context by a mechanism,
not by anyone's memory.

## 2. A direction file, re-read by a hook

**The file.** One short document (ours is about 80 lines): the goal, the test
of success, the method, the working rules, the priorities in order, and what
not to do. Conditions for it to be worth having:

- It quotes the person's own words, with dates. A paraphrase drifts each time
  it is rewritten; a quotation does not.
- It has one owner and changes only when the person steers.
- It wins over every other file on direction, and says so.
- It is short. A long one crowds out the work and is skimmed.

**The hook.** Claude Code runs commands at fixed points in a session. Whatever
a `SessionStart` hook prints is added to the agent's context. Its `compact`
matcher fires just after a summarisation, which is the moment the direction is
most likely to have been lost. In the repository's committed
`.claude/settings.json`:

``` code
{
  "hooks": {
    "SessionStart": [
      {
        "matcher": "startup|resume|clear|compact",
        "hooks": [
          { "type": "command", "command": "cat docs/direction.md" }
        ]
      }
    ]
  }
}
```

- Being committed, it reaches every agent and every worktree of the
  repository.
- Settings are read when a session starts, so a running session does not get a
  new hook until it is restarted.
- Not yet observed firing in locus at the time of writing: no session had
  restarted since it was added. Confirm before relying on it.

Also put the file in every brief to a subagent. A subagent starts with nothing
but its brief.

## 3. A chain of instruction files, one job each

When rules are spread over many files they contradict each other without
anyone noticing. Give each file one job and a fixed reading order:



| File | Job | Changes |
|----|----|----|
| `CLAUDE.md` | The reading order, and the few rules that never change | Rarely |
| `docs/direction.md` | Goal, method, priorities, what not to do | When the person steers |
| `docs/protocol.md` | Rules between agents: branches, builds, who owns what | When a rule changes |
| `AGENT-<branch>.md` | One agent's own knowledge: what it owns, its pitfalls, its state now | By that agent, in place |
| Handover logs | History | One entry per finished task |



**Name the agent file after the branch** the agent pushes to (or, where
several agents share `main`, its own branch without the prefix and hash). It
can then be found from the session's branch name, from commit messages, and
from the remote. Keep a table of them in the protocol.

**Logs are not instructions.** On 2026-10-12 three handover logs in locus were
each over 850 lines and were being appended to after almost every message,
while no agent had a short statement of what it owned. A fresh session would
have had to read a thousand lines to find its rules. The audit also found a
rule in force that practice had abandoned, a stale list of pending decisions,
and the current direction written in no instruction file at all.

**Ask each agent for its ten lines.** "What must a fresh session of your lane
know that is in none of the shared files?" The answers contained things that
existed nowhere else: a build wrapper kept in one session's scratch directory,
an output filter that hid parse errors, six statement faults found by
refutation.

## 4. State and memory: rewrite, don't append

- **"State now" is rewritten in place.** A section of at most 30 lines in the
  agent file says what is done, what is running and what is waiting. Appending
  produces a log; rewriting produces a state.
- **One list of what waits on the person**, in one file. Two lists disagree
  within a day.
- **Save to memory only what is durable and changes behaviour**: a correction,
  a standing preference, where something lives. Not completed work, which the
  repository already records.
- **Record the person's words, and label your own readings as yours.** On
  2026-10-12 "we haven't got a backward-looking modality" was turned by the
  manager into "no backward modality" and passed on as a prohibition. It had
  to be withdrawn.
- **Times come from `date`.** Log headings written from memory ran up to three
  hours ahead of the clock.

## 5. Communication between agents

- **One channel to the person.** With several agents each reporting, the
  person reads the same material twice and steers each separately. Since
  2026-10-12 the agents send their findings in full to the manager and say
  only "summary sent to the manager" in their own session; the manager reports
  once.
- **A message between sessions is information, not approval.** It cannot grant
  a permission, and an agent refused an action must not ask another to do it.
- **Messages can be held.** When two sessions run in different permission
  modes a message waits for the person's approval and can expire. Silence is
  not agreement.
- **The first line is what the person sees** in the receiving session, so make
  it a whole sentence saying what the message is.
- **Say what you want back**: the commit, what was tested and with what
  counts, what could not be done as written, the token cost.
- **One owner per file, one writer per log.** Shared configuration has a
  single owner. A change to another agent's file is a request to that agent.

## 6. What to ask the person, and what to decide

"Ask before everything" stops the work; "decide everything" is where drift
comes from. The rule adopted on 2026-10-12:

- The person is consulted before work begins only on **headline** matters:
  what the product or specification will guarantee, a test of the method,
  anything to be claimed outside the repository, a change of direction.
- The manager releases everything else and reports it.
- Before work that another agent will have to pick up, check it against the
  current goals first.

A manager's own check before releasing work: which numbered priority in the
direction file does this serve? If none, it waits.

## 7. Keeping claims straight

- **Four words, never mixed**: PROVED (checked, axioms pinned), REFUTED (a
  checked countermodel), TESTED, OPEN.
- **Verify before relaying.** The manager rebuilds a result and checks its
  pins before reporting it as proved, and presses a page before saying it
  works. Twice on 2026-10-12 it relayed without looking: an "open, not
  attempted" fact that was already a theorem in the repository, and controls
  described as "marked" that were not.
- **Search the record before calling anything new or open.**
- **Hunt a countermodel before proving.** Six statements were found false this
  way in one day, each before anything was built on it.
- **Label what a display computes for itself.** A page showed a formula
  reconstructed by its own code; the proofs were about a different object. It
  was caught and labelled within the hour, then replaced by the proofs' own
  value.
- **State the end-to-end result first.** A day of supporting lemmas had been
  proved before anyone wrote down the theorem they were meant to support. The
  person noticed; the agents had not.

## 8. Showing work to a person

- **One rule or formula at a time**, displayed, then explained.
- **A sample first.** Build one family, let the person look, then build the
  rest. Twice a whole design was built before he had seen one rule of it.
- **Give links he can open.** For a page served on his machine that is a link
  on his private network, not `localhost`; for a file in another repository, a
  permalink.
- **Say what is not there.** A control with nothing behind it is marked where
  it sits. An unmarked one was taken for a fault.
- **Answer the quick question first**, in its own reply; start the long work
  after.

## 9. Cost

- Report the token figure with each result. On 2026-10-12 two lanes and
  thirteen proving subagents used about 3.9 million tokens.
- A subagent costs more than it appears: it knows only its brief and returns
  only a summary. Use one for independent work, not for a lookup.
- Do not pause asked-for work on cost grounds. An overnight build that the
  manager had hesitated over used 3% of the weekly allowance.
- The largest waste is not tokens but re-derivation and unrequested
  generality. Both are prevented by sections 2 and 7.

## 10. Incidents, with dates



| Date | What happened | Rule it gave |
|----|----|----|
| 10-11 | Two designs were built in full before a rule was shown | Sample first (§8) |
| 10-12 | A fact reported "open, not attempted" was already proved | Search the record; verify before relaying (§7) |
| 10-12 | The method's central theorem had never been stated | State the end-to-end result first (§7) |
| 10-12 | A page's formula was not the object of the proofs | Label what a display computes (§7) |
| 10-12 | A remark became a prohibition in the manager's relay | Quote; label your own readings (§4) |
| 10-12 | Direction existed in no instruction file | Direction file and hook (§2) |
| 10-12 | Logs of over 850 lines, no short file per agent | Agent files; logs are history (§3) |
| 10-12 | An output filter hid a build error for three builds | Record pitfalls in the agent file (§3) |
