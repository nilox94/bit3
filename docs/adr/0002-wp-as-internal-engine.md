# Weakest Precondition as Internal Tactic Engine

We decided to keep weakest precondition (`wp`) computation strictly internal to the `hoare` tactic implementation, rather than exposing it as a first-class user-facing definition.

While `wp` is the theoretical foundation of the verification process and allows for fully automatic straight-line code proofs, exposing it directly often results in large, unreadable proof goals for the user. By hiding `wp` inside a bidirectional `hoare` tactic, users interact exclusively with the human-readable `HoareM` proposition. This provides the automation benefits of `wp` for straight-line code while maintaining the explicit, understandable structure of forward Hoare logic for complex control flow and loops.
