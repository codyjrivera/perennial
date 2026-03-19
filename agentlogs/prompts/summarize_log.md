# Summarizing Claude Code Logs

## Summarizing proof sessions.

When asked to summarize a proof, report only on the specific proof(s) named in the request.
If a session contained multiple proofs, do not summarize proofs that were not asked about —
only mention them briefly (e.g., in a note on session stats) to give context for time/token
attribution. If multiple proofs are requested, they will be named explicitly.

Please report time, token spend, and model used during the proof session, both for the whole
session (the scope of what you were asked to report on) and for any subsections of the proof
you would like to point out.

Please describe and divide the effort taken with respect to the following aspects of the proof:
- Research (looking at other proofs, looking at the 'tutorials').
- Planning (doing the logical reasoning for the proof).
- Implementing (writing proof code, debugging it).

Also, throughout the proof, try to notice where the tool got stuck, report statistics about where it got stuck,
and describe these places in detail, chronologically.

Finally, summarize what progress was made, what obstacles were encountered, how those that were overcome
were overcome, and what remains to be solved next.
