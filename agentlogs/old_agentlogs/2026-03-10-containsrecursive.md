# ContainsRecursive Proof Log

## Plan
1. Read existing proof file and generated code
2. Write proof using iInduction on the nat index of is_list_aux
3. Base case: head = null, S = empty, null check returns false
4. Inductive case: destruct, null check fails, check val == v, recurse
5. Build and iterate until Qed

## Attempt 1
Writing initial proof. Strategy: wp_start, destruct is_list, revert, iInduction on n.
