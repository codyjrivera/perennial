# Perennial

Perennial is a system implemented in Rocq for proving Go code correct. It builds on the Iris separation logic framework and uses stdpp (a Rocq standard library for Iris).

Most of the implementation is in `new/`, with program proofs in `new/proof/`.

There is a tutorial on writing program proofs: @new/proof/PERENNIAL_PROOF_TUTORIAL.md.

The `new/code` and `new/generatedproof` directories are auto-generated: do not edit anything there, and do not use these for proof style.

## Tools

There are some tools in `etc/` that we use for development and CI.

## Specific instructions for this branch.

This is an experimental branch where I want to not only have AI automate the work, but I also
want a good idea of what it has tried, where it got stuck, etc.

`agentlogs/` is a local directory I created to store this information. Log every session by date
(though I may give more clarification on what you need to do directly).

By default, if I do not give you other instructions, run my queries through a subagent. The
default agent's responsibility is to try to see what the agent is trying, and log it. You
should also monitor anywhere the agent seems to get stuck, and record it.

For each subagent invocation, record the following in the session log:
- Wall-clock time (duration)
- Token spend (approximate)
- Number of tool calls
- Model used

**Important limitation**: The orchestrating (main) agent cannot observe subagent intermediate
steps — only the final result, or nothing if interrupted. To mitigate this:
- After a subagent completes or is interrupted, the main agent should **check the actual file
  state** (read modified files, check build artifacts) to understand what the subagent did.
- The main agent should record this observed state in the session log, not just rely on the
  subagent's self-report.
- If subagents prove unreliable for logging, consider having the main agent do the work
  directly and log as it goes.

**Subagent logging requirements**: Subagents must write detailed progress notes to their
assigned log file (using Edit to append, NEVER overwrite with Write). The goal is not just to
record *that* the agent is stuck, but *what precisely it is trying and why*.

**CRITICAL**: Logging is a hard requirement, not optional. The orchestrator CANNOT see
subagent intermediate steps. If the subagent is interrupted or fails, the log is the ONLY
record of what happened. A subagent that does work without logging is useless — the work
cannot be understood, debugged, or continued.

Subagent logging protocol:
1. **First action**: Create/open the log file and write the plan (BEFORE doing any proof work).
2. **Before each compile attempt**: Append to the log what tactics/approach will be tried and why.
3. **After each compile attempt**: Append the result — success, or the error message and
   relevant proof state. Include the exact tactic sequence that was attempted.
4. **Every 3 tool calls maximum**: Append a progress checkpoint to the log, regardless of
   whether anything notable happened. This ensures progress is captured even if interrupted.
5. **When stuck**: Record what approaches were considered, what was tried, and why each failed.
   Distinguish between: (a) not knowing what tactic to use, (b) knowing the tactic but it
   produces an unexpected proof state, (c) a conceptual misunderstanding of the goal.
6. **When something works**: Record why it worked (so the pattern can be reused).
7. **Final action**: Append a summary with the final proof state (Qed/Admitted/stuck).

The log file path will be specified by the orchestrator. Use Edit (not Write) to append.
Format each entry with a markdown heading (## or ###) and timestamp-like ordering.
