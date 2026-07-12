/-
Copyright (c) 2026 Iris-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode
public import Iris.HeapLang.Lib.SpinLock

@[expose] public section
namespace Iris.Examples.HeapLang

open Iris.HeapLang BI Iris ProgramLogic List

/-!
# A per-node-locked doubly linked list (hand-over-hand locking)

Every node carries its own `SpinLock`.  A node is a heap location `l` whose cell
stores four physical components

```
l ↦ (lock, (value, (prev, next)))
```

where the three *logical* fields are `value`, `prev`, `next` (this is the
"`l` points to 3 elements" shape; the lock is an extra, immutable, component used
only for hand-over-hand locking).  `prev` and `next` are **head-values**:

* `none()`       — no neighbour on that side, so
                   `next = none()` ⇒ `l` is the last node,
                   `prev = none()` ⇒ `l` is the first node;
* `some(#l')`    — the neighbour is the node at location `l'`.

The *handle* of a node is its bare location value `#l` (not wrapped in `some`).
When a `some(#l')` head-value is pattern-matched, the bound variable is exactly
that bare handle `#l'`, so neighbour handles and list handles use the same
representation.  We deliberately do **not** introduce a separate `MList`-style
wrapper: a list is referred to directly by (a pointer to) its first node.

Traversal/mutation uses hand-over-hand ("lock coupling"): to touch a node you
hold its lock; to touch its neighbour you acquire the neighbour's lock and then
release the one you no longer need.  Liveness / deadlock-freedom is out of scope;
we only care about safety and the resource invariants.
-/
namespace DoublyLinkedList

open SpinLock

/-! ## Implementation -/

/-- Allocate a fresh, isolated node holding `x` (`prev = next = none()`), i.e. a
singleton doubly linked list.  Returns the node handle `#l`. -/
def newNode : Val := hl_val%
  λ x,
    let lk := &newlock #();
    ref((lk, (x, (none(), none()))))

/-- Insert a fresh node holding `y` immediately *after* node `node`, maintaining
both link directions, and return the new node's handle.

Locking: acquire `node`'s lock, allocate the new node `m` (already pointing to
`node` as its `prev` and to `node`'s old `next` as its `next`), redirect
`node.next := some(m)`, and — if there was a successor — acquire it and set its
`prev := some(m)` before releasing. -/
def insertAfter : Val := hl_val%
  λ node y,
    let nlk := fst(!node);
    &acquire nlk;
    let n := !node;
    let next := snd(snd(snd(n)));
    let mlk := &newlock #();
    let m := ref((mlk, (y, (some(node), next))));
    node ← (nlk, (fst(snd(n)), (fst(snd(snd(n))), some(m))));
    (match next with
     | none() => #()
     | some(q) =>
       let qlk := fst(!q);
       &acquire qlk;
       let qc := !q;
       q ← (qlk, (fst(snd(qc)), (some(m), snd(snd(snd(qc))))));
       &release qlk);
    &release nlk;
    m

/-- Unlink node `node` from its list, rejoining its neighbours:
`prev.next := node.next` and `next.prev := node.prev`.

Locking: acquire `node`'s lock, read its `prev`/`next`, then for each existing
neighbour acquire that neighbour's lock, patch the relevant field, and release.
(If `node` was the first node, its successor becomes the new head; if it was the
last, its predecessor becomes the new tail.) -/
def delete : Val := hl_val%
  λ node,
    let nlk := fst(!node);
    &acquire nlk;
    let n := !node;
    let prev := fst(snd(snd(n)));
    let next := snd(snd(snd(n)));
    (match prev with
     | none() => #()
     | some(p) =>
       let plk := fst(!p);
       &acquire plk;
       let pc := !p;
       p ← (plk, (fst(snd(pc)), (fst(snd(snd(pc))), next)));
       &release plk);
    (match next with
     | none() => #()
     | some(q) =>
       let qlk := fst(!q);
       &acquire qlk;
       let qc := !q;
       q ← (qlk, (fst(snd(qc)), (prev, snd(snd(snd(qc))))));
       &release qlk);
    &release nlk

/-! ## Predicates

These are the *tricky* part and are left as `sorry`; the comments explain the
intended meaning and why a naive inductive definition does not work.
-/
section Predicates

variable [HeapLangGS hlc GF] [SpinLockG GF]

/-- The mutable *contents* guarded by a single node's lock: its cell storing the
lock value `lk`, the value `x`, and the `prev`/`next` head-values.

This is the resource `R` one would pass to `isLock γ lk R`.  Note it must own the
whole cell `l ↦ (lk, (x, (prev, next)))`, and — crucially for a doubly linked
list — record enough of `prev`/`next` to state the *coherence* invariant
(`l.next.prev = some l` and `l.prev.next = some l`). -/
def nodeCell (l : Loc) (lk : Val) (x : Int) (prev next : Val) : IProp GF := sorry

/-- Persistent knowledge that a node lives at `l` and is governed by a lock whose
invariant is `nodeCell l lk x prev next` (for *some* current fields).  Persistent
so that **both** neighbours can hold a reference to it simultaneously — this
sharing is exactly what a doubly linked list needs, and why the mutable cell must
sit *inside* the lock while only the persistent `isLock` is exposed here. -/
def isNode (l : Loc) : IProp GF := sorry

/-- A doubly linked list **segment**.

`dllSeg lprev first last rnext xs` describes a contiguous run of nodes holding
values `xs`, where

* `first`  is the head-value handle of the leftmost node (`some(#l)` / `none()`);
* `last`   is the head-value handle of the rightmost node;
* `lprev`  is the value that the leftmost node's `prev` field must equal
           (the pointer coming *into* the segment from the left);
* `rnext`  is the value that the rightmost node's `next` field must equal.

The segment form (rather than a plain `isDLL v xs`) is what makes doubly linked
invariants expressible: the back-pointer constraint "`node.prev` points to the
previous node" is *not* inductive in the forward direction, so we must thread the
incoming `prev` pointer (`lprev`) and the outgoing `next` pointer (`rnext`)
through the recursion, tying each node's `prev` to its predecessor and each
node's `next` to its successor.  Empty segment: `first = rnext`, `last = lprev`,
`xs = []`. -/
def dllSeg (lprev first last rnext : Val) (xs : List Int) : IProp GF := sorry

/-- A whole doubly linked list headed at handle `v`: a segment whose left
boundary is `none()` (first node has `prev = none()`) and whose right boundary is
`none()` (last node has `next = none()`).  `xs` are the values front-to-back. -/
def isDLL (v : Val) (xs : List Int) : IProp GF := sorry
-- Intended: `isDLL v xs := ∃ last, dllSeg (none()) v last (none()) xs`.

end Predicates

/-! ## Specifications

All proofs are left as `sorry`; the statements fix the intended contracts. -/
section Specs

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [SpinLockG GF]

/-- Creating a node yields a singleton doubly linked list. -/
theorem newNode_spec (x : Int) :
    ⊢ ⦃ True ⦄ hl(&newNode #x) ⦃ v, RET v; isDLL (GF := GF) v [x] ⦄ := by
  sorry

/-- Inserting `y` right after the head node of `x :: xs` produces `x :: y :: xs`
and returns the new node's handle.  (Stated at the head for simplicity; the
general "insert after an interior node" spec uses `dllSeg` to split the list
around the target node.) -/
theorem insertAfter_spec (v : Val) (x y : Int) (xs : List Int) :
    ⊢ ⦃ isDLL (GF := GF) v (x :: xs) ⦄ hl(&insertAfter &v #y)
        ⦃ m, RET m; isDLL v (x :: y :: xs) ⦄ := by
  sorry

/-- Deleting an interior node `p` (holding `x`) from a list `as ++ x :: bs`
rejoins the two surrounding segments, leaving `as ++ bs`.  The precondition needs
to *locate* `p` inside the abstract list; the honest way to phrase this is via
two `dllSeg`s meeting at `p`:

```
dllSeg (none()) v p'   lp   as   ∗   dllSeg lp p (some p') rn [x]   ∗
dllSeg (some p) rn' ... bs ...
```

Getting that boundary bookkeeping right is the crux of the doubly linked proof,
hence the simplified `isDLL`-level statement here plus a `sorry`. -/
theorem delete_spec (v p : Val) (x : Int) (pre post : List Int) :
    ⊢ ⦃ isDLL (GF := GF) v (pre ++ x :: post) ⦄ hl(&delete &p)
        ⦃ RET hl_val(#()); isDLL v (pre ++ post) ⦄ := by
  sorry

end Specs

end DoublyLinkedList

end Iris.Examples.HeapLang
