module

public import Iris.BI.Lib.Atomic
public import Iris.ProgramLogic.Atomic

@[expose] public section

/-!
# One-shot logically atomic triples (Perennial style)

This file ports the *one-shot* (abort-free) flavour of logically atomic triples used
throughout MIT PDOS' **Perennial**, and states the machinery we will need on top of
it.  Everything that is not yet proved is an explicit `axiom`, flagged as such.

--------------------------------------------------------------------------------
## 0. What Perennial actually has

`perennial/src/program_logic/atomic.v` is **116 lines of pure `Notation`** — no
`Definition`, no `Lemma`, no `Instance`, no `Ltac`.  `atomic_fupd.v` (73 lines) is the
same thing with `|NC={..}=>` replaced by `|={..}=>`.  Their TaDA-shaped notation is

```coq
Notation "'<<<' ∀∀ x1 .. xn , α '>>>' e @ Eo '<<<' ∃∃ y1 .. yn , β '>>>'
          {{{ z1 .. zn , 'RET' v ; Q } } }" :=
  (□ ∀ Φ, (▷ |={⊤∖Eo,∅}=> ∃ x1, .. (∃ xn, α ∗
             ∀ y1, .. (∀ yn, β -∗ |={∅,⊤∖Eo}=> ∀ z1, .. (∀ zn, Q -∗ Φ v) ..) ..) ..) -∗
   WP e @ ⊤ {{ Φ }})%I
```

Note what is **not** there: the `(α x ={Ei,Eo}=∗ ...)` abort conjunct.  That single
omission is the whole difference from `Iris.atomicUpdate`, and it is what makes the
predicate monotone (see §2).

### What supports it (verified against `master`, SHA `43d4efab`)

There is **no `MonotonicPred` typeclass** — a repo-wide search returns zero hits, and
no other typeclass plays that role.  There is **no `iAuIntro` / `iAaccIntro` analogue,
and no dedicated `Ltac` or `Tactic Notation` for opening or closing an atomic update
anywhere in the repository.**  Perennial also never uses upstream Iris'
`atomic_update` / `iAuIntro` / `iAaccIntro` / `aacc_aupd` (0 hits each).

The entire supporting machinery is three things we **already have** in iris-lean:

| Perennial (`src/program_logic/weakestpre.v`, `base_logic/lib/ncfupd.v`) | iris-lean |
| ---------------------------------------------------------------------- | --------- |
| `wp_atomic : (\|={E1,E2}=> WP e @ E2 {{ v, \|={E2,E1}=> Φ v }}) ⊢ WP e @ E1 {{ Φ }}` | `wp_atomic` (used in `SafeAPI.write_acquire_spec` already) |
| `ElimModal` instance so `iMod` fires on a fupd against an atomic `WP` goal | `imod` |
| `fupd_mask_intro` / `ncfupd_mask_intro` for clients with mismatched masks  | `fupd_mask_intro` (`Iris/BI/Updates.lean:339`) |

So Phase A9 (tactics) is mostly *empty*: there is nothing to port.  Monotonicity is
recovered from ordinary `Proper`/`wp_strong_mono` instances, not a bespoke class.

--------------------------------------------------------------------------------
## 1. Shape correspondence

| Perennial                       | iris-lean `atomicWP`         | here (`oneShotWP`)      |
| ------------------------------- | ---------------------------- | ----------------------- |
| `□`                             | absent (Lean thms reusable)  | absent                  |
| `{{{ P }}}` non-atomic pre      | outer `-∗`                   | outer `-∗`              |
| `∀∀ x1 .. xn`                   | `TA` telescope               | `TA`                    |
| `α`                             | `α : TA → PROP`              | same                    |
| `@ Eo` (mask **removed** from ⊤)| `@ E`, with `Eo = ⊤ \ E`     | same convention         |
| `∃∃ y1 .. yn`                   | `TB`                         | `TB`                    |
| `β`                             | `β : TA → TB → PROP`         | same                    |
| `{{{ z1 .. zn, RET v; Q }}}`    | `TP` / `POST` / `f`          | same                    |
| `▷` in front of the AU          | **absent**                   | **present** (see §5.1)  |
| abort conjunct                  | present (greatest fixpoint)  | **absent**              |
| `|NC={..}=>` (crash-aware fupd) | `|={..}=>`                   | `|={..}=>`              |

The two designs line up almost field for field.  The port is therefore mostly a
*deletion*: drop the abort branch, drop the coinduction.

### Notation choice
`⟪ .. ⟫ e @ E ⟪ .. ⟫` is already taken by the coinductive `atomicWP`, so — mirroring
Perennial's own `<<<` vs `<<{` split — one-shot triples get a decorated bracket:

* `⟪  ..  ⟫`  coinductive TaDA (upstream, `Iris.ProgramLogic.atomicWP`)
* `⟪{ .. }⟫`  **one-shot TaDA (this file)**, Perennial's `<<<`
* `⟪| .. |⟫`  HOCAP (reserved, not implemented), Perennial's `<<{`

--------------------------------------------------------------------------------
## 2. Why one-shot composes

```
atomicAcc Eo Ei α P β Φ :=
  |={Eo,Ei}=> ∃.. x, α x ∗ ( (α x ={Ei,Eo}=∗ P)              -- α NEGATIVE
                           ∧ (∀.. y, β x y ={Ei,Eo}=∗ Φ x y) )
atomicUpdate := ν P. atomicAcc Eo Ei α P β Φ
```

`α` occurs both positively and negatively, so it has no polarity and there is no
monotonicity lemma — indeed `atomicUpdate_mono` does not exist anywhere in iris-lean,
and the one lemma that does exist, `atomicAcc_wand`, varies only `P` and `Φ`, i.e.
exactly the two purely-positive arguments.

`oneShotAU` deletes the negative occurrence, so `α` is covariant, `β` contravariant,
`Φ` covariant, and there is no fixpoint.  All three monotonicity lemmas become
one-liners (§4), which is what makes a `MonotonicPred`-style typeclass viable.

**What one-shot does NOT buy:** `⟨α⟩ e₁ ⟨β⟩` and `⟨β⟩ e₂ ⟨γ⟩` still do not compose
into `⟨α⟩ e₁;e₂ ⟨γ⟩`.  Two linearisation points are two linearisation points; other
threads can observe the intermediate state.  That is physics, not logic.  What
one-shot buys is *proof structure*: a nested coinductive obligation
(`aacc_aupd` / `aacc_aacc`) collapses into a single `fupd` chain.

--------------------------------------------------------------------------------
## 3. PORTING PLAN (SUPERSEDED — see §9–§11)

The plan below was written before the Perennial/vMVCC survey.  It is kept because
Phase A is still accurate and still done, but **Phases B/C/D are superseded**: the
survey showed the leverage is not "make the lock's own spec one-shot" but "move the
physical resources into an invariant and hand clients a ghost fragment".  Read §9–§11
instead.

### Phase A — this file (logic layer)                                    [PARTIAL]
* A1  `oneShotAU`, `oneShotWP`                                            DONE
* A2  `⟪{ .. }⟫` notation, 0/1/2 `∀` binders                              DONE (0/1/2)
* A3  `au_to_oneShotAU : atomicUpdate ⊢ oneShotAU`                        **PROVED**
* A4  `oneShotWP_to_atomicWP` — old specs are a free corollary            axiom
* A5  monotonicity in α / β / Φ, framing                                  axiom
* A6  ~~`MonotonicPred`~~ — **does not exist in Perennial.**  Dropped; use
      ordinary `Proper` / `wp_strong_mono`-style monotonicity instead.        N/A
* A7  `oneShotWP_seq`  (cf. `atomicWP_seq`)                               axiom
* A8  `oneShotWP_inv`  (cf. `atomicWP_inv`)                               axiom
* A9  tactics — **nothing to port.**  Perennial has no `iAuIntro`/`iAaccIntro`
      analogue; it uses `wp_atomic` + `imod` + `fupd_mask_intro`, all of which
      iris-lean already has.                                                  N/A
* A10 delaborator for `⟪{ }⟫`                                             TODO

### Phase B — SafeAPI prerequisite: physical words into invariants
One-shot is **impossible** for `read_acquire` and `Weak.tryUpgrade` as they stand,
and the reason is *not* the spin:

```
def read_acquire := rec acquire l :=
  let state := fst(l);
  let n := !state;                                       -- physical step 1: pure read
  if n < #0 then acquire l
  else if snd(cmpXchg(state, n, n + #1)) then snd(l) else acquire l
```

`state ↦ n` currently lives inside `isRwLock`, i.e. inside `α`.  So the bare load is
already an *open-look-abort*, even if the loop runs exactly once.  Same for
`tryUpgrade`.  Additionally `write_acquire_spec` opens-and-aborts once at the very top
purely to learn the pure fact `⌜l = (#p, &x)⌝`, which one-shot cannot express.

* B1  shadow RA `constOF (DFracAgreeR (LeibnizO RwLock.State))`,
      **asymmetric fractions: client 3/4, invariant 1/4** — see §5.2
* B2  `rwPhysInv N γ' p := inv N (∃ s, ⌜Valid s⌝ ∗ p ↦ #(counter s) ∗ physShare γ' 1/4 s)`
* B3  `isRwLock γ γ' N l s x := ⌜l = (#p,&x)⌝ ∗ ⌜Valid s⌝ ∗ physShare γ' 3/4 s ∗ rwStateOwn γ s`
      — **`rwStateOwn` (the `●`) must NEVER enter the invariant**; see §5.3
* B4  masks: `@ ∅` becomes `@ ↑N`; `isRwLock` gains a namespace parameter
* B5  reprove `write_release` (1 step, easiest), `write_acquire`, `read_release`,
      `read_acquire` (hardest: 2 physical steps per iteration)
* B6  Arc: **not needed yet.**  `clone` / `downgrade` / `get` / `dropStrong` /
      `dropWeak` are all single-step, and `isArc` already contains no `↦` at all
      (only `arcMetaOwn` + `arcStrongOwn`, both `◯` fragments).  Only
      `Weak.tryUpgrade` spins, and `Array.lean` uses `isWeak`/`upgrade` zero times.
      Required for `capa-engine` (`parent : CapabilityWeak<T>` + `upgrade()`).

### Phase C — migration (zero risk)
`au_to_oneShotAU` gives `oneShotWP e E α β POST f ⊢ atomicWP e E α β POST f`, so each
SafeAPI spec can be *restated* in one-shot form and the existing coinductive spec
re-derived in one line.  **`Array.lean` keeps compiling unchanged.**  Clients migrate
one at a time, whenever they want the fupd-chain proof style.

### Phase D — client payoff
* D1 `sharedViewWriteAcquireSpec` / `sharedViewWriteReleaseSpec` in one-shot form
     (each opens `α` exactly once already)
* D2 drop `aacc_aupd` / `aacc_aacc` / `itele_reduce` plumbing from those proofs

--------------------------------------------------------------------------------
## 4. Deliberate deviations from Perennial

* **No `□`.**  Perennial needs it because the spec is an `iProp` hypothesis reused at
  many call sites; in Lean a `theorem` is already reusable.
* **No separate `{{{ P }}}` slot.**  iris-lean passes non-atomic preconditions with an
  ordinary `-∗` in front of the triple (e.g. `rwGuard γ .write -∗ ⟪ .. ⟫ ..`), which is
  the same thing.
* **No crash conditions / `WPC` / `|NC={}=>`.**  iris-lean has no crash logic.
* **Telescopes instead of iterated binders.**  Perennial's `∀∀ x1 .. xn` is Coq
  notation-level iteration; iris-lean uses `Tele` + `∃..`/`∀..`, which is what the
  upstream `atomicWP` already does.

--------------------------------------------------------------------------------
## 5. Traps

### 5.1 The `▷`
Perennial puts `▷` in front of the whole AU.  It makes the AU *easier to provide*
(the client may supply it one step late) at the cost of forcing the implementation to
take at least one physical step before the linearisation point.  That is free in
practice: `wp_store`, `wp_cmpXchg`, … strip one `▷` at the step, and the LP *is* a
step.  Kept here for faithfulness; drop it if it ever bites.

### 5.2 `isRwLock_exclusive` breaks under Phase B
`SafeAPI.isRwLock_exclusive` is proved **entirely** via `pointsTo_ne`; the authority
components are discarded in its `icases`.  Once `p ↦ ..` moves into the invariant, the
authority cannot replace it: `isRwLock .. .write = ●{1/4} 0`, and `●{1/4} ∗ ●{1/4} =
●{1/2}` is *valid*.  Hence B1's asymmetric split — with client `3/4`, two copies give
`3/2 > 1` and the contradiction is immediate without opening the invariant.

### 5.3 The authority must never enter the invariant
`inv` is persistent, so its token is duplicable.  If `rwStateOwn γ s` were stored in
the invariant, anybody holding the token could open it and rebuild `isRwLock`, and
`write_acquire`'s `α` would stop being exclusive — **drop safety would break on the
spot**.  General criterion:

> Take the *entire* contents of the invariant.  Can you rebuild `α` from it?
> If yes, you put too much in.

`p ↦ #(counter s)` is safe because holding it grants no permission: mutating the word
without matching ghost movement leaves the invariant unclosable, and `rwGuard γ .write`
can only be split out of `rwStateOwn γ .free`, which stays with the client.
`physShare γ' q s` is safe because a fractional agreement grants *knowing*, not
*changing*.

### 5.4 Drop safety is unaffected by Phase B
The chain
`arcNoStrong ⊣ count = 0` → incompatible with `nodeSlotShared`'s `arcHasStrong` →
only `retiredSlot`'s `∨ arcNoStrong` branch, which carries no `isRwLock` →
`write_acquire`'s `α` cannot be supplied
is **entirely ghost**; it never mentions `↦`.  Moving physical words into invariants
cannot affect it.  (Also: `pointsTo` is `Timeless` in HeapLang, and
`instIsRwLockTimeless` already exists, so `Timeless`-ness is *not* a reason to do
Phase B.  The only reason is one-shot.)

--------------------------------------------------------------------------------
## 6. How Perennial gives a one-shot spec to a *spinning* implementation

This is the single most useful thing the survey turned up, and it settles the
`read_acquire` / `Weak.tryUpgrade` question.

Perennial's channels *do* get one-shot atomic specs despite being blocking/retrying.
Two ingredients, both needed:

**(i) The physical state lives in an invariant; the atomic update holds only ghost.**
`is_chan ch γ V` is an `inv`; `send_au` mentions only the ghost `own_chan s`:

```coq
Definition send_au (Φ : iProp Σ) : iProp Σ :=
  |={⊤,∅}=> ▷ ∃ s, own_chan s ∗
    match s with
    | chanstate.RcvPending => own_chan (chanstate.SndCommit v) ={∅,⊤}=∗ Φ
    | chanstate.Idle       => own_chan (chanstate.SndPending v) ={∅,⊤}=∗ send_nested_au Φ
    | chanstate.Buffered b => own_chan (chanstate.Buffered (b ++ [v])) ={∅,⊤}=∗ Φ
    | chanstate.Closed _   => False
    | _ => True                                   (* try-fail arms *)
    end.
```

**(ii) The retry step takes `AU ∧ Φ_fail` — an *additive* conjunction, not `∗`.**

```coq
Local Lemma wp_TrySend_blocking ch v γ : ∀ Φ,
  is_chan ch γ V -∗
  send_au γ v (Φ #true) ∧ Φ #false -∗          (* ← ∧, not ∗ *)
  WP .. "TrySend" #v #true {{ Φ }}.
```

The proof reads the *physical* state out of `is_chan` first, and only then chooses a
side: not ready ⟹ `iRight in "HΦ"`, and the atomic update **is never opened**; ready
⟹ `iLeft in "HΦ"`, `iMod "HΦ"`, commit.  `P ⊢ P ∧ P` holds for additive conjunction,
so a single `send_au` supplies both sides of every iteration, and `wp_for` carries it
as the loop invariant.

**Consequence for us.**  Phase B is confirmed *necessary* — the decision to commit has
to be made from state that is **not** in `α`, i.e. from an invariant — and the `∧`
pattern is the missing piece of the loop structure:

```
iloeb as IH
wp_bind cmpXchg
iapply wp_atomic (E2 := ⊤ ∖ ↑N)
open inv N;  cmpXchg
  | fail => close inv;  IH  applied to the *unopened* AU        -- α untouched
  | succ => imod HAU (once);  agree;  update;  commit;  close inv
```

Note the loop invariant is literally "I still hold the unopened one-shot AU", which is
where the `∧` shows up if the spec is factored through a `try_*` helper the way
Perennial factors `TrySend` out of `Send`.

--------------------------------------------------------------------------------
## 7. Independent corroborations from the survey

* **Locks never get atomic specs in Perennial** (`new/golang/theory/lock.v`);
  `is_lock m R := inv nroot (∃ b, m ↦{1/4} b ∗ if b then True else m ↦{3/4} b ∗ R)`,
  with plain Hoare `wp_lock_lock` / `wp_lock_unlock` and `iLöb` inside.  This is why
  their `α` is always pure ghost, and why they never needed abort.
* That same definition splits `↦` **1/4 // 3/4 asymmetrically**, for exactly the
  reason §5.2 needs it: an asymmetric split makes two copies immediately
  contradictory.
* `new/atomic_fupd.v` writes the mask separator as `@@` rather than `@`, to avoid
  clashing with the older `src/program_logic/atomic_fupd.v`.  Our `⟪{ }⟫` vs `⟪ ⟫`
  split is the same move.

--------------------------------------------------------------------------------
## 8. Earlier verdict (SUPERSEDED by §11)

An earlier measurement of `Array.lean`'s `sharedViewWriteAcquireSpec` (lines
1184–1312) found the coinductive overhead to be ~20% abort blocks plus ~5%
`itele_reduce`/`aacc_aupd_commit` plumbing, and on that basis recommended not
switching.  That measurement is still correct, but it measured the wrong thing: it
compared "same architecture, different AU flavour".  The survey below shows Perennial
changes the *architecture*, and the architecture change is what pays.  See §11.

Also worth recording: much of the pain that motivated this investigation was
*upstream bugs* in the coinductive machinery — `peelComp`'s `constLevels!` panic on
two-level telescopes, `teleNames` misalignment, and `aacc_aacc`/`aacc_aupd*` ported
with plain `∀` instead of `∀..` (which silently disabled `itele_reduce`).  Those are
fixed, so "the coinductive machinery is unusable" is no longer a reason for anything.

--------------------------------------------------------------------------------
## 9. Perennial's actual architecture — five layers

Canonical, complete, verified example: `new/proof/sync_proof/rwmutex.v` @
`43d4efabc22eb148eb239ebee89d1dd2ee54c900` (661 lines).  **This is a reader-writer
lock with a one-shot logically atomic spec** — i.e. exactly the artefact we are
building — so it is worth transcribing rather than inventing.

### Layer 1 — protocol: pure ghost, physical values as *parameters*

```coq
Local Definition own_RWMutex_invariant γ
    (writer_sem reader_sem reader_count reader_wait : w32) (state : rwmutex) : iProp Σ :=
  ∃ wl pos_reader_count outstanding_reader_wait,
    "Houtstanding"     ∷ own_tok_auth γ.(read_wait_gn) outstanding_reader_wait ∗
    "Hwl"              ∷ ghost_var γ.(wlock_gn) (1/2) wl ∗
    "Hrlock_overflow"  ∷ own_tok_auth γ.(rlock_overflow_gn) (Z.to_nat actualMaxReaders) ∗
    "Hrlocks"          ∷ own_toks γ.(rlock_overflow_gn) (Z.to_nat (sint.Z pos_reader_count)) ∗
    ... ∗
    match wl, state with
    | NotLocked unnotified_readers, RLocked num_readers => ⌜ ... arithmetic ... ⌝
    | SignalingReaders remaining,   RLocked num_readers => ⌜ ... ⌝
    | WaitingForReaders,            RLocked num_readers => ... ∗ ⌜ ... ⌝
    | IsLocked,                     Locked              => ⌜ ... ⌝
    | _, _ => False
    end.

#[global] Instance own_RWMutex_invariant_timeless a b c d e f :
  Timeless (own_RWMutex_invariant a b c d e f) := _.
```

Note the physical counters appear as **plain `w32` parameters**, not as `↦`.  On top
of this sit **12 transition lemmas, every one a pure `==∗` with no `WP` in sight**:

```coq
Lemma step_RLock_readerCount_Add γ writer_sem reader_sem reader_count reader_wait state :
  own_toks γ.(rlock_overflow_gn) 1 ∗
  own_RWMutex_invariant γ writer_sem reader_sem reader_count reader_wait state ==∗
  if decide (0 ≤ sint.Z (word.add reader_count (W32 1))) then
    ∃ num_readers,
      ⌜ state = RLocked num_readers ⌝ ∗
      own_RWMutex_invariant γ writer_sem reader_sem (word.add reader_count (W32 1))
                              reader_wait (RLocked (S num_readers))
  else
      own_RWMutex_invariant γ writer_sem reader_sem (word.add reader_count (W32 1))
                              reader_wait state.
```

(the other eleven: `step_RLock_readerSem_Semacquire`,
`step_TryRLock_readerCount_CompareAndSwap`, `step_RUnlock_readerCount_Add`,
`step_rUnlockSlow_readerWait_Add`, `step_rUnlockSlow_writerSem_Semrelease`,
`step_Lock_readerCount_Add`, `step_Lock_readerWait_Add`,
`step_Lock_writerSem_Semacquire`, `step_TryLock_readerCount_CompareAndSwap`,
`step_Unlock_readerCount_Add`, `step_Unlock_readerSem_Semrelease`)

> **This is the direct analogue of `Array.lean`'s eight `isPhysical_*` lemmas** — but
> factored so that the physical values are *arguments* and the lemma is a bare ghost
> update.  Ours currently mix in `isRwLock` (which carries `↦`); Perennial's do not.

### Layer 2 — invariant: everything physical, plus one half of every ghost pair

```coq
Definition is_RWMutex (rw : loc) γ N : iProp Σ :=
  "#Hmu"           ∷ is_Mutex (struct_field_ref sync.RWMutex.t "w" rw)
                        (ghost_var γ.(prot_gn).(wlock_gn) (1/2) (NotLocked (W32 0))) ∗
  "#His_readerSem" ∷ is_sema (struct_field_ref sync.RWMutex.t "readerSem" rw)
                        γ.(reader_sem_gn) (N.@"sema") ∗
  "#His_writerSem" ∷ is_sema ... ∗
  "#Hinv" ∷ inv (N.@"inv") (
      ∃ writer_sem reader_sem reader_count reader_wait state,
        "Hstate"       ∷ ghost_var γ.(prot_gn).(state_gn) (1/2) state ∗
        "HreaderSem"   ∷ own_sema γ.(reader_sem_gn) reader_sem ∗
        "HwriterSem"   ∷ own_sema γ.(writer_sem_gn) writer_sem ∗
        "HreaderCount" ∷ own_Int32 (struct_field_ref sync.RWMutex.t "readerCount" rw)
                            (DfracOwn 1) reader_count ∗
        "HreaderWait"  ∷ own_Int32 ... (DfracOwn 1) reader_wait ∗
        "Hprot"        ∷ own_RWMutex_invariant γ.(prot_gn)
                            writer_sem reader_sem reader_count reader_wait state ∗
        "Hlocked"      ∷ match state with
                         | Locked => own_Mutex ... ∗ ghost_var γ.(prot_gn).(wlock_gn) (1/2) IsLocked
                         | _ => True end).

Global Instance is_RWMutex_pers rw γ N : Persistent (is_RWMutex rw γ N) := _.
```

`is_RWMutex` is **Persistent**.  The `↦`-carrying `own_Int32`s are inside.

### Layer 3 — client: half a `ghost_var`, Timeless

```coq
Definition own_RWMutex γ (state : rwmutex) : iProp Σ :=
  ghost_var γ.(prot_gn).(state_gn) (1/2) state.
Global Instance own_RWMutex_timeless γ state : Timeless (own_RWMutex γ state) := _.

Definition own_RLock_token γ : iProp Σ := own_toks γ.(prot_gn).(rlock_overflow_gn) 1.
```

### Layer 4 — the one-shot spec

```coq
Lemma wp_RWMutex__RLock γ rw N : ∀ Φ,
  is_pkg_init sync ∗ is_RWMutex rw γ N ∗ own_RLock_token γ -∗
  ▷(|={⊤∖↑N,∅}=> ∃ state, own_RWMutex γ state ∗
     (∀ num_readers, ⌜ state = RLocked num_readers ⌝ →
        own_RWMutex γ (RLocked (S num_readers)) ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP rw @! "RLock" #() {{ Φ }}.
```

`α = own_RWMutex γ state` — **half a ghost var, no `↦`, Timeless, one-shot**.  The
persistent handle and the overflow token sit in the non-atomic precondition.  The
`Try` variants use the additive-conjunction failure form of §6:

```coq
▷((|={⊤∖↑N,∅}=> ...) ∧ Φ #false)          (* wp_RWMutex__TryRLock / TryLock *)
```

### Layer 5 — seven local `Ltac`

```coq
Ltac rwInvStart := iInv "Hinv" as ">Hi" "Hclose"; iNamedSuffix "Hi" "_inv".
Ltac rwInvEnd   := iCombineNamed "*_inv" as "Hi"; iMod ("Hclose" with "[Hi]") as "_";
                     [iNamed "Hi"; solve [repeat iFrame] | ]; iModIntro.
Ltac rwStep x   := iMod (x with "[$]") as "Hprot_inv";
                     (runInPure word); []; try destruct decide; iNamed "Hprot_inv".

Ltac rwLinearizeStart :=
  iMod (fupd_mask_subseteq _) as "Hmask"; last first; [iMod "HΦ" | solve_ndisj];
  try (iDestruct "HΦ" as (?) "HΦ"); iDestruct "HΦ" as "[Hstate HΦ]";
  iCombine "Hstate Hstate_inv" gives %[_ ?]; simplify_eq;
  iMod (ghost_var_update_2 with "Hstate [$]") as "[Hstate2_inv Hstate_inv]";
    first apply Qp.half_half;
  try iModIntro.
Ltac rwLinearizeEnd :=
  first [ iMod ("HΦ" with "[$]") as "HΦ" | iMod ("HΦ" with "[//] [$]") as "HΦ" ];
  iMod "Hmask" as "_".

Ltac rwAtomicStart := iApply fupd_mask_intro; [solve_ndisj | iIntros "Hmask"].
Ltac rwAtomicEnd   := iMod "Hmask" as "_".
```

and a proof body reads:

```coq
wp_apply wp_Int32__Add.
rwInvStart.
rwStep step_RLock_readerCount_Add.
- rwAtomicStart. iFrame. iIntros "!> H1_inv". rwAtomicEnd. rwLinearize. rwInvEnd.
```

> **`rwLinearizeStart` is the whole one-shot discipline in six lines**: shrink the
> mask, open the client's AU **once**, agree the two ghost halves, update both.  There
> is no `iAuIntro`, no `iAaccIntro`, no coinduction — because there is nothing to
> restore.

### The minimal template, for reference (`new/proof/sync_proof/sema.v`)

```coq
Definition is_sema (x : loc) γ N : iProp Σ := inv N (∃ (v : w32), x ↦ v ∗ ghost_var γ (1/2) v).
Definition own_sema γ (v : w32) : iProp Σ := ghost_var γ (1/2) v.
```

Physical `x ↦ v` in the invariant, client holds the other ghost half.  That is the
entire idea; everything above is that idea scaled up.

--------------------------------------------------------------------------------
## 10. vMVCC evidence (ref `coq/tested` @ `394e461a`)

⚠ `src/program_proof/mvcc/` is **404 on `master`** (deleted 2026-01-30).  Use
`coq/tested`.

### 10.1 The boundary

```coq
Definition dbmap_auth  γ m     := ghost_map_auth γ.(mvcc_dbmap) 1 m.              (* in inv *)
Definition dbmap_ptsto γ k q v := ghost_map_elem γ.(mvcc_dbmap) k (DfracOwn q) v. (* client  *)
Definition dbmap_ptstos γ q m  := [∗ map] k ↦ v ∈ m, dbmap_ptsto γ k q v.

Definition mvcc_inv_sst_def γ p : iProp Σ :=
  ∃ tids_nca tids_fa tmods_fci tmods_fcc tmods ts m past future,
    "Hproph" ∷ mvcc_proph γ p future ∗
    "Hts"    ∷ ts_auth γ ts ∗
    "Hm"     ∷ dbmap_auth γ m ∗
    "Hkeys"  ∷ ([∗ set] key ∈ keys_all, per_key_inv_def γ key tmods ts m past) ∗ ...

Instance mvcc_inv_sst_timeless γ p : Timeless (mvcc_inv_sst_def γ p).
Proof. unfold mvcc_inv_sst_def. apply _. Defined.

Definition mvcc_inv_sst γ p := inv mvccNSST (mvcc_inv_sst_def γ p).
```

`α` contains **no `↦`**; `dbmap_ptsto`'s fraction is **always `1`**; the invariant body
gets an **explicit `Timeless` instance**.

### 10.2 Fractions — only `1`, `1/2`, `1/4` appear anywhere

| holder | share of `ptuple_auth` | what it buys |
| --- | --- | --- |
| SST invariant (`per_key_inv_def`) | `1/2` | may *read* the physical chain, cannot advance it alone |
| tuple mutex, `owned = false` | `1/2` | an update needs both halves ⟹ **every physical write is forced to carry a ghost step** |
| tuple mutex + writer's `mods_token` | `1/4` + `1/4` | the escaping `1/4` **is the write lock in ghost form** |
| `own_tuple_locked` | `1/4+1/4` recombined to `1/2` | pair with the invariant's half, then `vchain_update` |

```coq
Definition mods_token γ (k : u64) (ts : nat) : iProp Σ :=
  ∃ phys, ptuple_auth γ (1/4) k phys ∗ ⌜(length phys ≤ S ts)%nat⌝.
```

(Correction to an earlier note in this file: the `3/4` split I attributed to vMVCC is
in `src/program_proof/txn/`, a different system.)

### 10.3 Only the top layer is atomic

11 logically atomic specs in the whole of vMVCC, **all at the transaction layer**
(`wp_txn__Run`, `_xres`, `_readonly`, `_xres_readonly`, `wp_DB__Run`, `wp_txn__begin`,
`wp_TxnSite__Activate`, `wp_GenTID`, and the three `Resolve*`).  Tuple, Index and
WrBuf get **ordinary Hoare triples**, threaded by `own_*` predicates.  The only
AU-to-AU composition in the tree is a forwarding relay (`DB__Run → Txn__Run`,
`Txn__begin → TxnSite__Activate → GenTID`), each 10–20 lines of
`iMod "HAU"; ...; iMod ("HAU" ...)`.

### 10.4 Prophecy — the criterion, and why we do not need it

vMVCC linearizes at `txn.begin()`, but `β` mentions `ok : bool` and the write set `w`,
neither of which is known then (the body has not run, no OCC validation has happened).
`peek future ts` reads them out of a prophecy.  The criterion is exactly:

> **Prophecy is needed iff the linearization point must be committed before its
> outcome is decidable.**  If the LP is a CAS whose result immediately determines both
> "did it take effect" and "what is the new abstract state", a plain one-shot AU with
> the outcome existentially bound in `β` suffices.

Our LPs are `cmpXchg` / `store` with immediately-decidable outcomes.  **No prophecy.**

### 10.5 Cost

Coq 404.5 KB vs Go 17.5 KB ≈ **23×**.  Of the Coq, `mvcc_tuplext.v` + `mvcc_inv.v` +
`mvcc_ghost.v` + `mvcc_action.v` ≈ 104 KB (**26%**) contains **no `WP` at all** — it is
pure state-relation reasoning.  That is the standing cost of "ghost linearizes early,
physical catches up later".  Deliberately cut, per the vMVCC README: `uint64` keys
only, no durability, no range queries.

--------------------------------------------------------------------------------
## 11. THE PLAN

### 11.0 Architecture change (this is the actual deliverable)

```
now:   α = arrShared …      -- contains every node's isRwLock, which contains p ↦ …
                            -- ⟹ any sub-call that needs a lock must open α
                            -- ⟹ α must be restorable on abort ⟹ coinduction forced

after: inv arrN ( ∃ s M σ, isPlatform γp s platform ∗ isPhysical γ γp M σ s ∗ arrAuth γa σ )
       α = arrFrag γa σ     -- half a ghost var, pure ghost, Timeless
```

Established by reading the code, not assumed:
- `Iris/Instances/IProp/Instance.lean:543` `iOwn_timeless` (needs `OFE.DiscreteE`)
- `Iris/BI/Lib/GenHeap.lean:116` `instTimelessPointsTo`
- `Iris/BI/BigOp/BigSepMap.lean:160` `bigSepM_timeless_inst`
- `SafeAPI.lean:73-75, 211-213, 656, 661` — `isRwLock`, `rwGuard`, `rwGuardFrac`,
  `arcAuth`, `isArc`, `isWeak` are all already `Timeless`
- `ArrState`, `Cell`, `Arr` all have `OFE.Discrete` ⟹ every `iOwn` is Timeless
⟹ **no obstruction**; `Array.lean` needs ~10 mechanical `Timeless` instances (it has 0).

### 11.1 Definitions to add

| new | Perennial counterpart | notes |
| --- | --- | --- |
| `arrAuth γa σ` / `arrFrag γa σ` | `ghost_var γ (1/2) state`; `dbmap_auth`/`dbmap_ptsto` | `1/2`+`1/2`, or ghost-map auth/frag. **`stateVar` is already exactly `ghost_var`** — reuse `FracAgreeLocal` |
| `arrInvContent γ γa γp platform` | `is_RWMutex`'s `inv` body; `mvcc_inv_sst_def` | wraps existing `isPlatform ∗ isPhysical` unchanged |
| `Arr.isArr` → persistent | `is_RWMutex` / `is_sema` / `mvcc_inv_sst` | `inv arrN (arrInvContent …)`; gains a `Persistent` instance |
| `Arr.isContents γa σ` | `own_RWMutex` / `dbmap_ptstos γ 1 r` | the new `α`; `Timeless` |
| ~10 `Timeless` instances in `Array.lean` | `own_RWMutex_invariant_timeless`, `mvcc_inv_sst_timeless` | mechanical |

### 11.2 Classes

**None to port.**  `MonotonicPred` does not exist; monotonicity comes from ordinary
`Proper`/`wp_strong_mono`.  The only typeclass work is `Timeless` / `Persistent`
instances, which are instances of existing classes.

### 11.3 Lemmas / theorems

| new | Perennial counterpart | status |
| --- | --- | --- |
| `arrFrag_agree` (two halves agree) | `iCombine ... gives %[_ ?]` | **`stateVar_agree` already written** — reuse shape |
| `arrAuth_update` (update both halves) | `ghost_var_update_2 ... Qp.half_half` | **`stateVar_full_update` already written** |
| `arrFrag_split` / `_combine` | `vchain_split` / `vchain_combine` | **`stateVar_split` already written** |
| keep the 8 `isPhysical_*` | the 12 `step_*` lemmas | refactor so physical values are *parameters* and each is a bare `==∗` with no `isRwLock` inside |
| `au_to_oneShotAU` | — | **proved, this file** |
| `oneShotWP_to_atomicWP` | — | axiom, A4 |
| `oneShotWP_seq` / `oneShotWP_inv` | — | axioms, A7/A8 |
| monotonicity ×3 + frame | — | axioms, A5 |

### 11.4 Tactics — port five, and only five

| Lean name | Perennial | body |
| --- | --- | --- |
| `iinv` (**exists**, `HeapLang/Lib/IInv.lean`) | `rwInvStart` / `rwInvEnd` | already there |
| **`ilinearize`** ← the important one | `rwLinearizeStart` + `rwLinearizeEnd` | shrink mask → `imod HΦ` once → `arrFrag_agree` → `arrAuth_update` → close.  ~6 lines, no coinduction |
| **`iatomicstep`** | `rwAtomicStart` / `rwAtomicEnd` | `fupd_mask_intro` … `imod Hmask` — for an atomic step that is *not* the LP |
| `istep` | `rwStep x` | apply one transition lemma and case-split |
| — | `iNamedSuffix` / `iCombineNamed` | **cannot port**: iris-lean has no named-proposition library.  Use explicit `icases`/`iframe` |

`iauintro` / `iaaccintro` / `iaaccintro'` / `itele_reduce` are **not needed** in the
one-shot world and have no Perennial analogue.

### 11.5 Composition — three patterns, in order of preference

1. **Do not make it atomic.**  vMVCC's tuple/index/wrbuf layers and Perennial's plain
   `Mutex` get ordinary Hoare triples.  *Apply this to `Impl.insert`'s internal lock
   operations*: once the locks live in the invariant, acquiring one does not move the
   abstract state, so it does not need an atomic spec at all.
2. **Additive conjunction for a fallible attempt** (§6): `AU ∧ Φ_fail`.  Used for
   `TryRLock`/`TryLock`/`TrySend`.  Content is just `P ⊢ P ∧ P`.
3. **Commit to an intermediate abstract state and stash the rest** — `send_nested_au`,
   with the source comment *"NOTE: this leaves no freedom for picking the
   linearization order."*  Needed only for genuinely multi-phase protocols
   (rendezvous).  We should not need it.

A fourth exists but is advanced: **store the AU itself inside an invariant**
(`gentid_au` + `saved_pred_own` in `tid_proof.v`) — Perennial's helping mechanism.
This is only possible because a one-shot AU is an ordinary `iProp`; the coinductive
`atomicUpdate` is a greatest fixpoint and fights `▷`/contractiveness.  **This is the
one place where one-shot is a capability advantage rather than an ergonomic one.**
iris-lean has `LaterCredits.lean` but no `saved_pred_own` — would need porting first.

### 11.6 Order of work

1. `arrAuth`/`arrFrag` + the three ghost lemmas (mostly copy `stateVar_*`)
2. ~10 `Timeless` instances in `Array.lean`
3. `arrInvContent`, persistent `Arr.isArr`, `Arr.isContents`
4. `ilinearize` + `iatomicstep`
5. Restate `sharedViewWrite{Acquire,Release}Spec` as **ordinary Hoare triples**
   (pattern 11.5.1) — they stop being atomic specs entirely
6. Give `Impl.insert` / `Impl.revoke` one-shot specs with `α = arrFrag`
7. Only then consider refactoring the 8 `isPhysical_*` into `step_*` shape

Steps 1–3 are mechanical.  Step 5 is where the current proof text shrinks.

--------------------------------------------------------------------------------
## 12. Tulip — independent confirmation of the same architecture

Located at **`github.com/mit-pdos/tulip-proof`** @ `main` (Coq, 640 KB, last push
2025-12-08); Go implementation at `github.com/mit-pdos/tulip`.  There are also
Perennial branches `tulip-port` and `tchajed/new-tulip`.  Proofs live under
`src/program_proof/tulip/`.

### 12.1 The client fragment — the comment says it for us

`src/program_proof/tulip/res.v:20-28`:

```coq
(** Single-value logical database values. One half in the txnsys invariant,
one half given to the client. *)

Definition own_db_ptsto γ (k : dbkey) (v : dbval) : iProp Σ :=
  own γ.(db_ptsto) {[ k := (to_dfrac_agree (DfracOwn (1 / 2)) v) ]}.

Definition own_db_ptstos γ (m : dbmap) : iProp Σ :=
  [∗ map] k ↦ v ∈ m, own_db_ptsto γ k v.
```

`to_dfrac_agree (DfracOwn (1/2)) v` **is** `Iris/HeapLang/Lib/FracAgreeLocal.lean`'s
`FracAgree.mk (.own (1/2)) v`, i.e. exactly the shape of `Array.lean`'s existing
`stateVar`.  Nothing new needs inventing: `arrAuth`/`arrFrag` = `stateVar` at `1/2`
each.

### 12.2 One invariant for the entire system

`src/program_proof/tulip/inv.v:14-31`:

```coq
Definition tulip_inv_with_proph γ p : iProp Σ :=
  "Htxnsys" ∷ txnsys_inv γ p ∗
  "Hkeys"   ∷ ([∗ set] key ∈ keys_all, key_inv γ key) ∗
  "Hgroups" ∷ ([∗ set] gid ∈ gids_all, group_inv γ gid) ∗
  "Hrgs"    ∷ ([∗ set] gid ∈ gids_all, [∗ set] rid ∈ rids_all, replica_inv γ gid rid).

#[global] Instance tulip_inv_with_proph_timeless γ p :
  Timeless (tulip_inv_with_proph γ p).
Proof. apply _. Qed.

Definition know_tulip_inv_with_proph γ p : iProp Σ :=
  inv tulipcoreNS (tulip_inv_with_proph γ p).
Definition know_tulip_inv γ : iProp Σ := ∃ p, know_tulip_inv_with_proph γ p.
```

A whole distributed transaction system — transactions, keys, groups, replicas — is
**one `inv`, with an explicit `Timeless` instance**, and the handle is persistent.
This is the direct precedent for putting all of `isPlatform ∗ isPhysical` into a
single `inv arrN (…)`.

### 12.3 The atomic spec is at *transaction* granularity only

`src/program_proof/tulip/program/txn/txn_run.v:24-33` — structurally identical to
vMVCC's `wp_txn__Run`, down to the `Decision (Q r w)` side condition:

```coq
Theorem wp_Txn__Run txn (body : val) (P : dbmap -> Prop) (Q : dbmap -> dbmap -> Prop)
    (Rc : dbmap -> dbmap -> iProp Σ) (Ra : dbmap -> iProp Σ) γ :
  (∀ r w, (Decision (Q r w))) ->
  ⊢ {{{ own_txn_uninit txn γ ∗ (∀ tid r τ, body_spec body txn tid r P Q Rc Ra γ τ) }}}
    <<< ∀∀ (r : dbmap), ⌜P r ∧ dom r ⊆ keys_all⌝ ∗ own_db_ptstos γ r >>>
      Txn__Run #txn body @ ↑sysNS
    <<< ∃∃ (ok : bool) (w : dbmap),
          if ok then ⌜Q r w⌝ ∗ own_db_ptstos γ w else own_db_ptstos γ r >>>
    {{{ RET #ok; own_txn_uninit txn γ ∗ if ok then Rc r w else Ra r }}}.
```

Measured `<<<` counts: `program/txn/txn_read.v` **0**, `program/txn/txn_write.v` **0**,
`program/tuple/tuple_repr.v` **0**, `program/gcoord/gcoord_read.v` **0**.  Even the
user-facing `Read`/`Write` are ordinary triples; **only `Txn__Run` is atomic**.  The
linearization granularity is the whole transaction, not the individual operation.

### 12.4 File-level architecture, worth copying wholesale

```
res.v, res_group.v, res_key.v, res_network.v, res_replica.v, res_txnsys.v
      -- client-facing resources: the ghost fragments
inv.v, inv_group.v, inv_key.v, inv_replica.v, inv_txnlog.v, inv_txnsys.v
      -- invariant bodies: everything physical + the authoritative halves
invariance/   (22 files: linearize, commit, abort, read, prepare, validate, learn, …)
      -- PURE `==∗` ghost-update lemmas.  No `WP` anywhere.
program/      (txn/, tuple/, gcoord/, replica/, index/, txnlog/, paxos/, backup/)
      -- the WP proofs, which call `invariance/` lemmas at their linearization points
```

`invariance/linearize.v` (538 lines) is the analogue of Perennial's twelve `step_*`
lemmas and of `Array.lean`'s eight `isPhysical_*` lemmas: e.g.
`keys_inv_linearize_commit {γ kmodls rds} wrs ts tid : … ==∗ …`,
`txnsys_inv_linearize_abort {γ p ts tid future rds} form Q : … ==∗ …`.

> **Recommendation:** adopt the `res / inv / invariance / program` split in
> `Array.lean` too.  It is currently one 2000-line file mixing all four, and the
> `invariance` layer (the eight `isPhysical_*` lemmas plus the slot-level transfer
> lemmas) is exactly the part that should be `WP`-free and is not.

### 12.5 Summary of the three-system agreement

| | Perennial `rwmutex` | vMVCC | Tulip |
| --- | --- | --- | --- |
| client fragment | `ghost_var γ (1/2) state` | `ghost_map_elem … (DfracOwn 1)` | `to_dfrac_agree (DfracOwn (1/2)) v` |
| physical resources | inside `inv (N.@"inv")` | inside `inv mvccNSST` | inside `inv tulipcoreNS` |
| invariant `Timeless` | explicit instance | explicit instance | explicit instance |
| handle | `is_RWMutex`, Persistent | `mvcc_inv_sst`, Persistent | `know_tulip_inv`, Persistent |
| transition lemmas | 12 × `step_*`, pure `==∗` | `per_key_inv_*`, pure `==∗` | `invariance/`, 22 files, pure `==∗` |
| atomic specs | only `RLock`/`Lock`/`Try*` | only the txn layer (11) | only `Txn__Run` |
| abort branch | none (one-shot) | none | none |
| `↦` in `α` | none | none | none |

Three independent systems, one architecture.  That is the strongest evidence in this
file, and it is what §11 is copying.
-/

namespace Iris.OneShot

open BI ProgramLogic Language.Notation Std

/-! ## Definitions -/

section Definitions
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
variable {TA TB : Tele}

/-- **One-shot atomic update.**  Perennial's `<<< .. >>>` payload.

    Compare `Iris.atomicUpdate`, which is `ν P. |={Eo,Ei}=> ∃.. x, α x ∗
    ((α x ={Ei,Eo}=∗ P) ∧ (∀.. y, β x y ={Ei,Eo}=∗ Φ x y))`.  Deleting the left
    conjunct — the *abort* branch — removes the only negative occurrence of `α` and
    with it the need for a greatest fixpoint. -/
def oneShotAU (Eo Ei : CoPset) (α : TA → PROP) (β Φ : TA → TB → PROP) : PROP :=
  iprop(|={Eo, Ei}=> ∃.. x, α x ∗ (∀.. y, β x y ={Ei, Eo}=∗ Φ x y))

end Definitions

section WeakestPre
variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {TA TB TP : Tele}

/-- **One-shot logically atomic triple.**  Mask convention matches upstream
    `atomicWP`: the argument `E` is the part *removed* from `⊤`, i.e. `Eo = ⊤ \ E`.
    The `▷` mirrors Perennial; see §5.1. -/
abbrev oneShotWP
    (e : Expr) (E : CoPset)
    (α : TA → IProp GF)
    (β : TA → TB → IProp GF)
    (POST : TA → TB → TP → Option (IProp GF))
    (f : TA → TB → TP → Val) : IProp GF :=
  iprop(∀ (Φ : Val → IProp GF),
    ▷ oneShotAU (⊤ \ E) ∅ α β (λ x y => ∀.. z, POST x y z -∗? Φ (f x y z)) -∗
    WP e {{ Φ }})

end WeakestPre

/-! ## Notation

`⟪{ .. }⟫ e @ E ⟪{ .. }⟫`, deliberately distinct from the coinductive `⟪ .. ⟫`.
Only the 0-, 1- and 2-binder `∀` forms are provided; the remaining shapes are A2/TODO. -/

declare_syntax_cat osPre
declare_syntax_cat osPost

syntax "⟪{" ("∀ " ident ", ")? term "}⟫" : osPre
syntax "⟪{" "∀ " ident ", " "∀ " ident ", " term "}⟫" : osPre

syntax "⟪{" "∃ " ident ", " term " | " ident ", " "RET " term "; " term "}⟫" : osPost
syntax "⟪{" "∃ " ident ", " term " | " "RET " term "}⟫" : osPost
syntax "⟪{" term " | " "RET " term "}⟫" : osPost

syntax (name := oneShotTripleNotation)
  ppRealFill(osPre ppSpace term:arg " @ " term:arg ppSpace osPost) : term

macro_rules
  -- two ∀ binders, no ∃, no RET binders   (the `∀ σ, ∀ M` shape used in Array.lean)
  | `(⟪{ ∀ $x₁:ident, ∀ $x₂:ident, $α:term }⟫ $e:term @ $E:term
      ⟪{ $β:term | RET $v:term }⟫) =>
      `(oneShotWP
        (TA := Tele.cons <| λ _ => Tele.cons <| λ _ => Tele.nil.{0})
        (TB := Tele.nil.{0})
        (TP := Tele.nil.{0})
        $e $E
        (Tele.app <| λ $x₁ => λ $x₂ => ULift.up.{0,0} iprop($α))
        (Tele.app <| λ $x₁ => λ $x₂ =>
          ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} iprop($β)))
        (Tele.app <| λ $x₁ => λ $x₂ =>
          ULift.up.{0,0} <| Tele.app
            (ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} none)))
        (Tele.app <| λ $x₁ => λ $x₂ =>
          ULift.up.{0,0} <| Tele.app
            (ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} $v))))
  -- two ∀ binders, ∃ binder, no RET binders
  | `(⟪{ ∀ $x₁:ident, ∀ $x₂:ident, $α:term }⟫ $e:term @ $E:term
      ⟪{ ∃ $y:ident, $β:term | RET $v:term }⟫) =>
      `(oneShotWP
        (TA := Tele.cons <| λ _ => Tele.cons <| λ _ => Tele.nil.{0})
        (TB := Tele.cons <| λ _ => Tele.nil.{0})
        (TP := Tele.nil.{0})
        $e $E
        (Tele.app <| λ $x₁ => λ $x₂ => ULift.up.{0,0} iprop($α))
        (Tele.app <| λ $x₁ => λ $x₂ =>
          ULift.up.{0,0} <| Tele.app <| λ $y => ULift.up.{0,0} iprop($β))
        (Tele.app <| λ $x₁ => λ $x₂ =>
          ULift.up.{0,0} <| Tele.app <| λ $y =>
            ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} none))
        (Tele.app <| λ $x₁ => λ $x₂ =>
          ULift.up.{0,0} <| Tele.app <| λ $y =>
            ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} $v)))
  -- one ∀ binder, no ∃, no RET binders
  | `(⟪{ ∀ $x:ident, $α:term }⟫ $e:term @ $E:term ⟪{ $β:term | RET $v:term }⟫) =>
      `(oneShotWP
        (TA := Tele.cons <| λ _ => Tele.nil.{0})
        (TB := Tele.nil.{0})
        (TP := Tele.nil.{0})
        $e $E
        (Tele.app <| λ $x => ULift.up.{0,0} iprop($α))
        (Tele.app <| λ $x => ULift.up.{0,0} <| Tele.app
          (ULift.up.{0,0} iprop($β)))
        (Tele.app <| λ $x => ULift.up.{0,0} <| Tele.app
          (ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} none)))
        (Tele.app <| λ $x => ULift.up.{0,0} <| Tele.app
          (ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} $v))))
  -- one ∀ binder, ∃ binder, no RET binders
  | `(⟪{ ∀ $x:ident, $α:term }⟫ $e:term @ $E:term
      ⟪{ ∃ $y:ident, $β:term | RET $v:term }⟫) =>
      `(oneShotWP
        (TA := Tele.cons <| λ _ => Tele.nil.{0})
        (TB := Tele.cons <| λ _ => Tele.nil.{0})
        (TP := Tele.nil.{0})
        $e $E
        (Tele.app <| λ $x => ULift.up.{0,0} iprop($α))
        (Tele.app <| λ $x => ULift.up.{0,0} <| Tele.app <| λ $y =>
          ULift.up.{0,0} iprop($β))
        (Tele.app <| λ $x => ULift.up.{0,0} <| Tele.app <| λ $y =>
          ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} none))
        (Tele.app <| λ $x => ULift.up.{0,0} <| Tele.app <| λ $y =>
          ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} $v)))
  -- one ∀ binder, ∃ binder, RET binder + POST
  | `(⟪{ ∀ $x:ident, $α:term }⟫ $e:term @ $E:term
      ⟪{ ∃ $y:ident, $β:term | $z:ident, RET $v:term; $POST:term }⟫) =>
      `(oneShotWP
        (TA := Tele.cons <| λ _ => Tele.nil.{0})
        (TB := Tele.cons <| λ _ => Tele.nil.{0})
        (TP := Tele.cons <| λ _ => Tele.nil.{0})
        $e $E
        (Tele.app <| λ $x => ULift.up.{0,0} iprop($α))
        (Tele.app <| λ $x => ULift.up.{0,0} <| Tele.app <| λ $y =>
          ULift.up.{0,0} iprop($β))
        (Tele.app <| λ $x => ULift.up.{0,0} <| Tele.app <| λ $y =>
          ULift.up.{0,0} <| Tele.app <| λ $z =>
            ULift.up.{0,0} (some iprop($POST)))
        (Tele.app <| λ $x => ULift.up.{0,0} <| Tele.app <| λ $y =>
          ULift.up.{0,0} <| Tele.app <| λ $z => ULift.up.{0,0} $v))
  -- no binders at all
  | `(⟪{ $α:term }⟫ $e:term @ $E:term ⟪{ $β:term | RET $v:term }⟫) =>
      `(oneShotWP
        (TA := Tele.nil.{0})
        (TB := Tele.nil.{0})
        (TP := Tele.nil.{0})
        $e $E
        (Tele.app (ULift.up.{0,0} iprop($α)))
        (Tele.app (ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} iprop($β))))
        (Tele.app (ULift.up.{0,0} <| Tele.app
          (ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} none))))
        (Tele.app (ULift.up.{0,0} <| Tele.app
          (ULift.up.{0,0} <| Tele.app (ULift.up.{0,0} $v)))))

/-! ## A3 — the bridge, machine-checked

This is the only non-trivial statement in the file that is actually proved.  It is
what makes Phase C zero-risk: a one-shot spec *implies* the coinductive spec, so the
existing `SafeAPI` interface can be re-derived rather than migrated. -/

section Bridge
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
variable {TA TB : Tele} {α : TA → PROP} {β Φ : TA → TB → PROP}

/-- A coinductive atomic update can always be cashed in for a one-shot one: unfold it
    once and take the *commit* conjunct, throwing away the abort branch.

    The converse fails, which is exactly the sense in which a one-shot **spec** is
    stronger: the implementation is handed strictly less. -/
theorem au_to_oneShotAU (Eo Ei : CoPset) :
    atomicUpdate Eo Ei α β Φ ⊢ oneShotAU Eo Ei α β Φ := by
  refine (aupd_aacc α β Φ Eo Ei).trans ?_
  simp only [atomicAcc, oneShotAU]
  iintro HAU
  imod HAU with ⟨%x, Hα, Hcl⟩
  imodintro
  iexists x
  iframe Hα
  icases Hcl with ⟨-, Hcommit⟩
  iexact Hcommit

end Bridge

/-! ## Axioms

Everything below is stated but **not proved**.  Each carries the reason we expect it
to hold and what it is for.  Ordered by how much they matter. -/

section Axioms
variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {TA TB TP : Tele}

/-- **A4 — the migration lemma.**  Immediate from `au_to_oneShotAU` plus the fact that
    the atomic update sits in *negative* position inside the triple.  With this, every
    existing `SafeAPI` `atomicWP` spec is a one-line corollary of its one-shot
    replacement, so `Array.lean` never has to change. -/
axiom oneShotWP_to_atomicWP
    (e : Expr) (E : CoPset)
    (α : TA → IProp GF) (β : TA → TB → IProp GF)
    (POST : TA → TB → TP → Option (IProp GF)) (f : TA → TB → TP → Val) :
    oneShotWP e E α β POST f ⊢ atomicWP e E α β POST f

end Axioms

section MonoAxioms
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
variable {TA TB : Tele}

/-- **A5a — covariant in the atomic precondition.**  `α` occurs only positively, so
    unlike `atomicUpdate` this needs a *single* entailment, not a round trip.  This is
    the whole point of the exercise: TaDA's `AtCons` demands `α' ⊢ α` **and**
    `α ⊢ α'`; here one direction suffices. -/
axiom oneShotAU_mono_pre (Eo Ei : CoPset) (α α' : TA → PROP) (β Φ : TA → TB → PROP)
    (H : ∀ x, α x ⊢ α' x) :
    oneShotAU Eo Ei α β Φ ⊢ oneShotAU Eo Ei α' β Φ

/-- **A5b — contravariant in the atomic postcondition.**  `β` occurs only to the left
    of a wand. -/
axiom oneShotAU_mono_post (Eo Ei : CoPset) (α : TA → PROP) (β β' Φ : TA → TB → PROP)
    (H : ∀ x y, β' x y ⊢ β x y) :
    oneShotAU Eo Ei α β Φ ⊢ oneShotAU Eo Ei α β' Φ

/-- **A5c — covariant in the continuation.**  The analogue of `atomicAcc_wand`'s `Φ`
    argument, which is the only monotonicity upstream can offer. -/
axiom oneShotAU_mono_cont (Eo Ei : CoPset) (α : TA → PROP) (β Φ Φ' : TA → TB → PROP)
    (H : ∀ x y, Φ x y ⊢ Φ' x y) :
    oneShotAU Eo Ei α β Φ ⊢ oneShotAU Eo Ei α β Φ'

/-- **A5d — framing.**  A resource held across the linearisation point can be carried
    through without ever entering `α`.  Under `atomicUpdate` this is painful because
    `R` would have to survive every abort round trip. -/
axiom oneShotAU_frame (Eo Ei : CoPset) (R : PROP) (α : TA → PROP) (β Φ : TA → TB → PROP) :
    iprop(R ∗ oneShotAU Eo Ei α β Φ) ⊢
      oneShotAU Eo Ei α β (λ x y => iprop(R ∗ Φ x y))

end MonoAxioms

/-! ### A6 — ~~`MonotonicPred`~~ (retracted)

I previously reported, from secondhand information, that Perennial has a
`MonotonicPred` typeclass with around eight automatic instances.  **That is wrong.**
A repo-wide search on `master` (SHA `43d4efab`) returns zero hits, and nothing else
plays that role.  Monotonicity comes from ordinary `Proper (⊢) ==> (⊢)` instances on
the fancy update plus `wp_strong_mono`; both already exist in iris-lean.

What *is* worth having is the retry combinator from §6 — except that it turns out to
have no content: `AU ∧ Φ_fail` is built from `P ⊢ P ∧ P`, a BI triviality that already
exists.  It is a **proof idiom, not a lemma**.  (An earlier draft of this file stated
it as an axiom `oneShotAU ⊢ oneShotAU ∧ (Fail -∗ Fail)`, which is vacuous.  Removed.) -/

section StructuralAxioms
variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {TA TB TP : Tele}

/-- **A7 — sequential collapse.**  The one-shot analogue of `atomicWP_seq`: a client
    that owns `α` outright can use the atomic spec as an ordinary Hoare triple.  This
    is the rule `ArrayCopyClient.insert_hoare` uses. -/
axiom oneShotWP_seq
    (e : Expr) (E : CoPset)
    (α : TA → IProp GF) (β : TA → TB → IProp GF)
    (POST : TA → TB → TP → Option (IProp GF)) (f : TA → TB → TP → Val) :
    oneShotWP e E α β POST f ⊢
      iprop(∀ (Φ : Val → IProp GF), ∀.. x,
        α x -∗ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ WP e {{ Φ }})

/-- **A8 — absorb a client invariant into the atomic precondition.**  Verbatim the
    shape of `atomicWP_inv`, with `atomicWP` replaced by `oneShotWP`: a spec whose
    `α` demands `▷ I` alongside the real precondition can be traded for one that does
    not, at the price of the mask `↑N`. -/
axiom oneShotWP_inv
    (e : Expr) (E : CoPset)
    (α : TA → IProp GF) (β : TA → TB → IProp GF)
    (POST : TA → TB → TP → Option (IProp GF)) (f : TA → TB → TP → Val)
    (N : Namespace) (I : IProp GF) (HN : ↑N ⊆ E) :
    oneShotWP e (E \ ↑N)
      (λ x => iprop(▷ I ∗ α x))
      (λ x y => iprop(▷ I ∗ β x y)) POST f -∗
    inv N I -∗ oneShotWP e E α β POST f

end StructuralAxioms

/-! ## Smoke tests for the notation

These only check that each `macro_rule` elaborates; they assert nothing. -/

section Smoke
variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]

/-- No binders. -/
example (e : Expr) (E : CoPset) (P Q : IProp GF) (v : Val) : IProp GF :=
  ⟪{ P }⟫ e @ E ⟪{ Q | RET v }⟫

/-- One `∀` binder. -/
example (e : Expr) (E : CoPset) (P : Nat → IProp GF) (Q : IProp GF) (v : Val) : IProp GF :=
  ⟪{ ∀ n, P n }⟫ e @ E ⟪{ Q | RET v }⟫

/-- One `∀`, one `∃`. -/
example (e : Expr) (E : CoPset) (P : Nat → IProp GF) (Q : Nat → IProp GF) (v : Val) :
    IProp GF :=
  ⟪{ ∀ n, P n }⟫ e @ E ⟪{ ∃ m, Q m | RET v }⟫

/-- One `∀`, one `∃`, one RET binder with a `POST`. -/
example (e : Expr) (E : CoPset) (P : Nat → IProp GF) (Q R : Nat → IProp GF)
    (g : Nat → Val) : IProp GF :=
  ⟪{ ∀ n, P n }⟫ e @ E ⟪{ ∃ m, Q m | k, RET g k; R k }⟫

/-- Two `∀` binders — the `∀ σ, ∀ M` shape `Array.lean` uses throughout. -/
example (e : Expr) (E : CoPset) (P : Nat → Bool → IProp GF) (Q : IProp GF) (v : Val) :
    IProp GF :=
  ⟪{ ∀ n, ∀ b, P n b }⟫ e @ E ⟪{ Q | RET v }⟫

/-- Two `∀` binders plus an `∃`. -/
example (e : Expr) (E : CoPset) (P : Nat → Bool → IProp GF) (Q : Nat → IProp GF)
    (v : Val) : IProp GF :=
  ⟪{ ∀ n, ∀ b, P n b }⟫ e @ E ⟪{ ∃ m, Q m | RET v }⟫

end Smoke

end Iris.OneShot
