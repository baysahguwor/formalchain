## FormalChain Coq Formalisation

Machine-checkable chain-of-custody with **formally verified state transitions** and **provable unlinkability guarantees**.

**Coq version:** 8.20.1  
**Compile with:** `coqc formalchain.v`

**This file contains:**  
(1) **Type definitions** - states, actors, permissions, and actions;  
(2) **Core structures** - evidence record and system state;  
(3) **Transition model** - `ValidTransition`, implementing a **7-rule transition predicate**;  
(4) **Verified invariants** - seven mechanically proven properties: evidence integrity, custody continuity, state monotonicity, authorization enforcement, no state skipping, non-empty custody, and timestamp monotonicity;  
(5) **Executable verifier** - `transitionMatrix`, a decision procedure extracted for **on-chain verification**.
