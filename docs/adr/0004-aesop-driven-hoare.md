## Aesop-Driven Hoare Logic with a Total, Fuel-Indexed `loopM`

We rebuilt the `bitlib` Hoare layer around two interlocking decisions: making `loopM` total via a `fuel : Nat` parameter (with `UBKind.timeout` on exhaustion), and replacing the bespoke `hoare` macro tactic with Aesop driving a dedicated `BitcHoare` rule set of WLP-style structural lemmas.

The previous design used a `partial` `loopM` and two TCB axioms (`loopM_EffectStack_unfold` for the fixpoint equation, `loopM_terminates_on_invariant` for well-foundedness). Those axioms encoded partial-correctness assumptions that the Lean kernel could not verify. Total fuel-indexed recursion eliminates them: `loopM_hoare` is now proved by structural induction on `fuel` with no axioms beyond Lean's built-ins, and non-terminating user code is observable as `timeout` UB rather than wedging the proof.

The bespoke `hoare` macro paired well with a bespoke `wp` engine (ADR-0002), but Aesop has matured into the de facto Lean automation framework and already understands forward chaining, branch splitting, and rule prioritisation. By stating each structural lemma in WLP shape — `seq_hoare` passes the post-state of the first leg directly into the second, with no existential intermediate predicate to invent — and tagging it `@[aesop safe apply (rule_sets := [BitcHoare])]`, a single `aesop (rule_sets := [BitcHoare])` call discharges straight-line Hoare goals. `loopM_hoare` is intentionally **not** tagged: Aesop cannot guess a loop invariant, so the user always opens loops with `apply loopM_hoare (I := ...)` before calling Aesop.

Supersedes ADR-0002. See `VERIFICATION.md` for the standard proof workflows.
