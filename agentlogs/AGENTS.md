# Perennial Agent Logs

Please follow the section labeled "Initial instructions" upon reading
this file. Please refer to the other sections as reference on how
to do things by default.

## Initial instructions

This is where I will store agent logs/progress. Sessions
are stored in the `sessions/` subdirectory, and are stored in the following
format: `YYYY-MM-DD-sN` (capitals are digits): date and session sequence.

Record the session ID (UUID) of the current session in the directory. I may want to
refer back to the comprehensive .jsonl log Claude records, indexed by
this ID (e.g., for a summary).

The created `sessions/[date+seq]` directory is the best place to store
any logging information related to a particular session.

*IMPORTANT*: DO NOT REFER TO ANY PAST SESSION DATA IN THIS
DIRECTORY UNLESS I HAVE EXPLICITLY GIVEN YOU PERMISSION TO DO SO.


## Summarizing logs

Please follow the structure in `prompts/summarize_log.md` by default
when you are asked to summarize a log.

## Proof style

When you are writing proofs, please follow `prompts/proof_prompt.md` closely.
