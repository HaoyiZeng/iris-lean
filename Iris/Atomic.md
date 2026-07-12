# Atomic port — proof-mode changes & design review

梳理围绕 atomic port 对 proof mode（notation / delab / instance / lemma / tactic）的所有改动，
加上对 reduce 方案的风险和设计取舍分析，供 review。

---

## 一、整体分层：两套独立的「telescope 消隐」机制

理解全部改动的关键：我们有**两条完全独立**的 telescope 处理链路，服务两个不同目的，
但共用底层 `reduceTeleApps`。

| | 显示链路（delab） | 项目链路（tactic） |
|---|---|---|
| 目的 | 只为 pretty-print，**不改 term** | 真把 goal 改成 defeq 形式，让 tactic 能推进、hyp 干净 |
| 入口 | `@[delab] delabAtomicUpdate` / `delabAtomicWP` | `itele_reduce` |
| 机制 | `peelComp`/`peelDelab` + `teleNames` + `reduceTeleApps` | `simp only [peeling lemmas]` + `reduceTeleApps`（`itele_reduce_apps`，走 `mvar.change`） |
| 触发者 | Lean 打印器自动 | 用户在证明里手动调 |

**这个二分本身就是最大的设计张力**（见「问题」）：同一个「把 `Tele.app`/`Σ…PUnit` 变干净」
的需求，显示端和项目端各写了一套。

---

## 二、Notation / Macro 层（`BI/Lib/Atomic.lean`, `ProgramLogic/Atomic.lean`）

- **`auPre` / `auPost` syntax cat**（134/137 行）+ `AU … @ Eo, Ei …`（`atomicUpdateNotation`），
  用 `ppRealFill` 做软换行。
- **两条 `macro_rules`**：full 变体（`⟪ ∀ y, β, COMM Φ ⟫`，TB=cons）和 nil 变体
  （`⟪ β, COMM Φ ⟫`，TB=nil）。它们把用户写的 `∃ x`/`∀ y` 编码成
  `Tele.cons (λ _ => Tele.nil)` + `Tele.app (λ x => ULift.up …)` 的打包形式。
- `ProgramLogic/Atomic.lean`：`atomicWP`（abbrev，Φ 用普通 `λ x y =>`）+ 三元组 notation + macros。

关键取舍：**用户语法里写普通 binder，底层强行编码成单层 telescope**。所有后续的「leak」都源于
这个编码（`Arg = Σ…PUnit`）。

---

## 三、Delab 层（`BI/Lib/Atomic.lean` §Delab, 569–705 行）

因为 Lean 的 `delab_rule`/`app_unexpander` **无法匹配嵌套子应用**（参数被 annotate），
只能写 full custom `@[delab app.Iris.atomicUpdate]`。核心四件套：

1. **`reduceTeleApps`**（581 行）：ctor-gated 的手写 whnf。只在 `Tele.app` 的第 4 个参数是
   `Sigma.mk`/`PUnit.unit`（构造子）时才 reduce，用 `whnfHeadPred` 停在 user const（不展开 `↦`）。
   额外分支处理 `.proj`、`ULift.down (ULift.up x)`、`Sigma.fst/snd ⟨…⟩`。
   **这是复刻 Rocq `Arguments tele_app … !_ /`**。
2. **`peelComp`**（649 行）：把一个 component（`α`/`β`/`Φ`）沿 telescope 列表**逐层 apply 到构造子参数**
   （cons → `⟨fv, ()⟩`，nil → `PUnit.unit`），每层 reduce。把打包 binder 变成普通 binder。
   universe 从 `argTy.constLevels!` 取；`Sigma.mk` 的依赖 `β` 用 `mkAppOptM` 显式给。
3. **`teleNames`**（603 行）：从**未 reduce 的原始结构**抽 binder 名字（因为 reduce 会 α-rename 成 `a`），
   保证 `α`/`β`/`Φ` 三者 binder 名一致。
4. **`delabAtomicUpdate`**（688 行）/ `delabAtomicWP`：组装成
   `AU ⟪ ∃ x, α ⟫ @ Eo, Ei ⟪ [∀ y,] β, COMM Φ ⟫`。COMM 强制复用 α/β 的名字
   （因为 `atomicWP` 的 Φ 是自带 `x`/`y` 名的普通 λ）。

---

## 四、Tactic 层：`itele_reduce`（622–638 行）

现在是个 macro：

```lean
macro "itele_reduce" : tactic =>
  `(tactic| (try simp only [biTexist_cons, biTexist_nil, biTforall_cons, biTforall_nil]
             itele_reduce_apps))
```

- `itele_reduce_apps`（原来的 elab）= `mvar.change (reduceTeleApps goal)`，规约构造子上的 `Tele.app`。
- 前置 `try simp only [4 条 peeling lemma]` = 新增的 pm_prettify 类比，把 concrete telescope 上的
  `biTexist`/`biTforall` peel 成普通 `∃`/`∀`。

### `iauopen`(`imod` + `itele_reduce` 的封装)

经验事实:证明里**唯一**需要 `itele_reduce` 的地方,就是刚用 `imod` 打开一个 client atomic update
之后(打开 AU 会露出 telescope 编码的 `α`,需要归一)。因此封了一个 tactic:

```lean
macro "iauopen" colGt pmt:pmTerm " with " colGt pat:icasesPat : tactic =>
  `(tactic| (imod $pmt with $pat; itele_reduce))
```

对应 Rocq 的 `iMod "AU" as (x) "[Hα Hclose]"`(其 telescope smart-intro 直接给出干净的
`∃ x, α x ∗ (abort ∧ commit)`)。所有派生 spec 里的 `imod HAU with …; itele_reduce`
都替换成了 `iauopen HAU with …`;普通 modality 仍用 `imod`。


---

## 五、新增 Lemma（`BI/Telescopes.lean`）

4 条 **defeq（`rfl`）** peeling 引理，复刻 Rocq `Arguments bi_texist/bi_tforall {_ !_} _ /`：

```lean
biTexist_nil  : biTexist Ψ = Ψ PUnit.unit
biTexist_cons : biTexist Ψ = iprop(∃ x, biTexist (fun xs => Ψ ⟨x, xs⟩))
biTforall_nil : biTforall Ψ = Ψ PUnit.unit
biTforall_cons: biTforall Ψ = iprop(∀ x, biTforall (fun xs => Ψ ⟨x, xs⟩))
```

用 `Eq` 而非 `⊣⊢`（才能 simp 进 `∗`/fupd 内部任意上下文）；只对 concrete telescope 匹配、
abstract `TT` 不动。**未加 `@[simp]`**（保守，只在 `itele_reduce` 里显式引用）。

---

## 六、Instance 层

- **`elimModAupd`**（260 行）：fupd-specific 的 `ElimModal`，让 `imod HAU` 能用 `aupd_acc` 打开
  atomic update。（之前 `∀ R` 版本因 `P'`/`Q'` 是 `outParam` 失败。）
- **`ProofMode/Instances.lean` 里既有的 telescope 实例保持不动**：
  `intoExists_biTexist`/`intoForall_biTforall`/`fromExists`/`fromForall`，它们把 `biTexist Φ`
  暴露成 `∃ (a : TT.Arg), Φ a`（**整包 Arg**）。**这正是 leak 的来源**——我们这次没动它，
  而是用 peeling lemma 在 destruct 之前把 `biTexist` 拍平，绕过它。
- **`ProofMode/Display.lean`**（个人本地，未上传）：IPM goal separator 从 `⊢` 改成 `────□`/`────∗`。
  会 break 两个 snapshot test，选择本地忽略。

---

## 七、用 reduce 的问题（review 重点）

1. **顺序敏感 / 构造子门槛**：`reduceTeleApps` 和 peeling 都要求「telescope 还是 `biTexist` head +
   witness 还是构造子 `⟨n, ()⟩`」。一旦 destruct，witness 变成不透明 fvar `n : Σ…`，两者都失效 →
   `Tele.app` 永久卡住。所以**必须 reduce-then-destruct，且必须先 `imod … with HAU'` 命名再 reduce**
   （因为 `imod … with ⟨⟩` 的 open+destruct 是原子的，中间插不进 reduce）。这是很 unintuitive 的 API。

2. **不自动**：Rocq 的 `pm_prettify` 每步自动跑；我们没有 hook，只能在用户证明里手撒 `itele_reduce`。
   既啰嗦又容易忘/放错位置。

3. **`reduceTeleApps` 是手写 whnf + 一堆 special-case 分支**（`.proj`、`ULift.down/up`、
   `Sigma.fst/snd`）：脆弱，和 `Std/Telescopes.lean` 的 `Arg`/`fold`/`bind` 编码强耦合，
   编码一改就要同步改。

4. **peeling `simp only` 是全局重写 + `try` 吞错**：会改写整条 entailment（在 atomic 场景恰好安全，
   因为 AU notation 底层不是 top-level `biTexist`，但作为通用机制有风险）；`try` 会静默吞掉任何 simp 错误。

5. **显示端和项目端两套机制会 drift**：`peelComp`（delab，作用于 Expr 打印）和
   peeling lemma + `reduceTeleApps`（tactic，作用于 goal）逻辑重叠但实现不同，改一个容易忘另一个。

6. **`teleNames` 这套「从未 reduce 结构抠名字」纯属为了对抗 reduce 的 α-rename**：额外复杂度，
   本质是 reduce 的副作用。

---

## 八、根设计取舍 & 能不能更好

**为什么把 `biTexist`/`biTforall` 保持 opaque def（不 reducible）**：delab 要靠 head symbol 匹配来打印
notation。代价 = proofmode 把它当不透明、暴露整包 `Arg` → leak → 才需要 peeling lemma 补救。
这是一切的源头取舍。

可能的改进方向（按 invasive 程度）：

- **A（现状）**：peeling lemma + 手动 `itele_reduce`。零改 core，但 UX 差、顺序敏感。
- **B：结构化 peeling `IntoExists`/`IntoForall` 实例**（对 `Tele.cons` 逐层剥 head binder，
  `nil` → body）。能让 `imod HAU with ⟨%n,…⟩` **一步到位**，不用 reduce-before-destruct。
  **难点**：剥到最后一层 `biTexist over nil` 要能对续接的 `IntoSep` 呈现成 body——要么让
  `biTexist`/`biTforall` `@[reducible]`（可能打乱 delab），要么加 nil 塌缩实例。碰 core proofmode，
  风险中等。
- **C：把 pm_prettify hook 进 `imod`/`icases` 实现**（真·Rocq parity，用 `change_no_check` 降成本）。
  UX 最好，但改 proofmode tactic 本身，改动最大。
- **D：改 `Tele` 编码**，让单层 telescope 直接是普通 binder（避免 `Σ…PUnit`）。从根上消灭 leak，
  但牵动整个 atomic port 和所有 telescope 用户。

建议 review 时重点评估 **B**：它直击「destruct 时 leak 整包 Arg」这个痛点，且能顺带让显示端和项目端
**统一到同一套 peeling 语义**（都基于「cons 剥一个 head、nil 塌 body」），有希望消掉
`teleNames`/双机制 drift。唯一要解决的是 nil-tail 对续接 tactic 的可见性。

---

## 九、Option B 原型验证结论（peeling instances）

针对上面的 Option B 做了原型验证（scratch，不改现有代码），核心发现：

**关键更正**：之前担心「尾 telescope `(fun _ => nil) x` 是 beta-redex，discr-tree 匹配不上 nil」是
**错的**——Lean instance resolution 会 whnf 这个 redex，nil 塌缩实例能正常 fire。因此结构化 peeling
`IntoExists`/`IntoForall` 实例对**任意层数** telescope 都能把 binder 剥成用户类型（Rocq 体验）。

### 各 instance 效果（都是 `.rfl`/defeq，priority 高于泛型）

| Instance | 位置 | 效果 | 局限 |
|---|---|---|---|
| `intoExists_biTexist_cons` | `icases`/`imod…with ⟨⟩` | `∃..` 剥一个普通 head binder，任意层数 | 只剥 binder，body 的 `Tele.app` 不规约 |
| `intoSep_biTexist_nil` / `intoAnd_biTexist_nil` | 最后一层 | nil `∃..` 塌 body，让 `⟨Hl,Hclose⟩` 拆 `∗`/`∧` | 每个消费类要单独一条 |
| `intoForall_biTforall_cons` | `ispecialize`/`imod H $$ %v` | `∀..` 假设剥普通 binder（免 `%PUnit.unit`） | 同上，只剥 binder |
| `intoWand_biTforall_nil` | 最后一层 | nil `∀..` 塌 body(wand)，让 `$$` 喂 premise | 只覆盖 IntoWand |
| `fromForall_biTforall_cons` | `iintro %x %y`（目标位） | `∀..` 目标剥普通 binder | — |

**共同做不到**：规约 `Tele.app ⟨n,()⟩ → l ↦ #n`（那是 `reduceTeleApps`）。不跑 `itele_reduce` 会留
`.fst`/nil 脏显示 + 偶发 defeq side-goal。

**已知 plumbing bug**：`itele_reduce` 的 `mvar.change` 触达不到**双层** telescope 的 proofmode 虚拟
hyp（单层/目标位正常；atomic 只用单层，不受影响）。

### 选定方案：Plan A（已实施）

- **Plan 0**：保持现状（3 步手动、顺序敏感）。
- **Plan A（已实施）**：加 `intoExists_biTexist_cons` + `intoSep/intoAnd_biTexist_nil`（3 条，
  放 `ProofMode/Instances.lean`）。→ `imod HAU with ⟨%n, Hl, Hclose⟩` **一步**、普通 binder、
  无 PUnit、无 rcases、**顺序无关**；仍保留 `itele_reduce` 清 body。零 core 改动、低风险。
- **Plan B**：Plan A + `intoForall/fromForall_biTforall_cons` + 逐消费类 nil 塌缩。∀ 侧收益不如 ∃ 侧
  （nil 透传要逐类补），仅当有多 binder RET 后置条件才划算。
- **Plan C**：pm_prettify hook 进 `iCasesExists`/`iIntroCore`（intro 时规约 body）。binder+body 全自动
  干净、彻底免 `itele_reduce`，但改 core tactic，改动最大。可与 Plan A 叠加。
- **Plan D**：修双层-hyp 规约 bug（遍历 hyps 逐个 change）。仅多层 telescope 需要，atomic 用不上。

### Plan A 落地记录

- `ProofMode/Instances.lean`：新增 `intoExists_biTexist_cons`、`intoSep_biTexist_nil`、
  `intoAnd_biTexist_nil`（`into_* := .rfl` / 透传，priority 10000）。
- `Tests/Atomic.lean` `inc_spec`：两处 destruct 改成一步 `imod HAU with ⟨%n/%w, Hl, Hclose⟩; itele_reduce`。
- 验证：`Tests.Atomic`/`Tests.Telescopes`/`Tests.Instances` 全绿；`Tests.Tactics` 的 29 处失败为
  `Display.lean` separator 个人改动的既有 breakage（Plan A 前后数量一致，**零新增回归**）。

---

## 十、`itele_reduce` 对 nil-telescope 的鲁棒性修复

**症状**：logically-atomic spec 里 `TA = nil`（无 `∀∀`/`∃∃` binder，如 release）时，若 destruct 写成
`imod HAU with ⟨%s, Hl, Hs⟩`（多写了 `%s`），`itele_reduce` **清不掉** context：`Hl`/`Hs` 里全是
`Tele.app { down := X } s`。

**根因**：`%s` 在 nil telescope 上经泛型 `intoExists_biTexist` 绑了一个 spurious `s : Tele.nil.Arg`
（= PUnit）**裸 fvar**；而旧 `reduceTeleApps` 只在 `Tele.app` 的**参数是构造子**（`PUnit.unit`/`⟨_,_⟩`）时
才规约，裸 fvar 卡住。

**修复（正确设计）**：`Tele.app` 在 `nil` 上**按定义忽略其参数**（`nil => λ f _ => f.down`），所以
`Tele.app { down := X } s` 对**任意** `s` 都可规约成 `X`。把 `reduceTeleApps` 的门槛放宽为
「telescope（`args[0]`）是 `Tele.nil`」**或**「参数是构造子」。这样 `itele_reduce` 对 nil-app 永远能清
干净，无需每个 proof 手动调整。（`BI/Lib/Atomic.lean` `reduceTeleApps`）

**验证**：release proof 里即便误写 `⟨%s, Hl, Hs⟩`，`itele_reduce` 后 `Hl : tada_lock_state γ Locked`、
`Hs : (… ={∅,⊤}=∗ AU …) ∧ (… ={∅,⊤}=∗ none -∗? Φ …)` 全干净（仅剩一个未用的 `s : Tele.nil.Arg`）。

**用法建议**：`TA = nil` 的 spec（release 之类）destruct 用 `⟨Hl, Hs⟩`（不写 `%s`）——没有 logical
binder 可 intro；nil-collapse 实例会直接把 body 的 `∗`/`∧` 拆开，连 `s` 都不会出现。

---

## 十一、`AtomicLock`：从 concrete spec 派生 abstract spec（concrete ⟹ abstract）

`HeapLang/Lib/AtomicLock.lean` 演示了 logically-atomic lock 的两套 spec，并证明后者可由前者**派生**：

- **Concrete（物理裸指针）**：`acquire_atomic_spec` / `release_atomic_spec` ——
  `⟪ ∀ b, l ↦ #b ⟫ … ⟪ l ↦ #… ⟫`,只谈物理 cell,无 ghost。
  另有加强版 `acquire_atomic_spec'`,commit 额外暴露 `⌜b = false⌝`(否则抽象 `Free→Locked`
  update underdetermined)。
- **Abstract（TaDA 风格）**:`plock_is_lock` / `plock_state`,用 `FracAgree`(fractional agreement)
  ghost var 把物理 `b` 和抽象 `Free`/`Locked` 绑定,invariant 持 `1/4`、client 持 `3/4`。

**结论**:concrete **严格强于** abstract —— concrete 能推出 abstract(在上面搭 ghost + invariant),
反之不行。`release_plock_spec` / `acquire_plock_spec` 就是用 `atomicWP_inv`(把 invariant 包进
client AU)+ 手工 accessor 完成的派生。

### `FracAgreeLocal`(不改 upstream 的变通)

`Algebra/Lib/DFracAgree.lean` 是全 `Algebra/Lib` 里**唯一**没有 `@[expose] public section` 的文件
(siblings `Frac`/`DFrac`/`Agree`/`MonoNat` 都有),所以它**什么都不导出**,任何模块都 import 不到
`DFracAgree.DFracAgreeR`/`Frac.mk`/…。**不修改该 upstream 文件**的前提下,`HeapLang/Lib/FracAgreeLocal.lean`
在独立的 `FracAgree` namespace 下,以 `@[expose] public section` 重新提供 AtomicLock 所需的最小子集
(`DFracAgreeR`、`mk`/`Frac.mk`、`mk_op`、`op_valid(_L)`、`update₂`)。证明只依赖已导出的 `DFrac`/`Agree`。

---

## 十二、移植 `elim_acc_aacc`:在 accessor 内部开 invariant

Rocq 的干净写法 `awp_apply …; iInv "H" as …; iAaccIntro with …` 依赖两个 iris-lean **未移植**的件:
`iInv`(`ProofMode/Porting.lean` 标 missing)和 `elim_acc_aacc`(ElimAcc-over-`atomicAcc`)。
`HeapLang/Lib/IInv.lean` 本地补齐了这条链:

- **`aacc_inv`**(= `elim_acc_aacc` 的数学核心,已证):在 `atomicAcc E1 E2 α P β Φ` 目标上打开
  timeless invariant `inv N I`,**保持它还是 accessor**;把 body `I` 交给你,要求 abort/commit
  各自归还 `I`(用来关 invariant)。mask `E1 → E1\N`。
- **`iinv`**(两种形式):
  - `iinv h with ⟨pat, cl⟩` —— fupd 目标(`|={E,E'}=>`),包 `inv_acc_timeless`;
  - `iinv h as body` —— `atomicAcc` 目标,dispatch 到 `aacc_inv`(Rocq `iInv` 的对应)。
- **`iaaccintro'`**:upstream `iaaccintro` 的 telescope-aware 版本。原版要求选中的假设**字面上**是
  `α x`(size-1 app),对具体的 `l ↦ #b`(三参数 `pointsTo`)+ telescope 编码的 `α` 匹配失败;
  `iaaccintro'` 用 `mkTeleArgMVar` 造一个 `Tele.Arg` 的 metavar 见证,让 `α x` 与假设**按 reduction 归一**
  地 unify。它还对自己产生的 abort/commit 子目标跑 `reduceTeleApps`,所以物理 accessor 侧**无 `Tele.app`**。

于是 `release_plock_spec` 的骨架就是真正的 Rocq idiom:

```lean
iapply release_atomic_spec.{0,0} l
iauintro
iinv Hinv as Hbody          -- 在 accessor 内开 invariant
simp only [lockRel, plock_state, stateVar]
icases Hbody with ⟨%b, Hl, Hst1⟩
iaaccintro' with Hl         -- 选物理 cell,自动分 abort/commit
· …abort… · …commit…
```

**残留噪音(诚实说明)**:client AU 侧(`imod HAU`)仍有 nil-telescope 编码,需 1–2 个 `itele_reduce`;
这是 iris-lean 对**任何** `atomicUpdate` 做 `imod` 的固有产物,`iaaccintro'` 够不到。

---

## 十三、`atomicAcc` 的 delaborator(`AACC⟪…⟫`)

问题:`atomicUpdate` 有 `delabAtomicUpdate`(打印成 `AU⟪…⟫`),但 `atomicAcc` **没有** delaborator,
所以中间的 accessor 目标里 `α`/`β`/`Φ` 全以裸 `Tele.app (fun b => {down := …})` 显示。

**修复**(`BI/Lib/Atomic.lean` §Delab,`delabAtomicUpdate` 之后):新增 `AACC⟪ … ⟫` notation 和
`delabAtomicAcc`,复用同文件的 `peelDelab`/`teleNames`,把
`atomicAcc Eo Ei α P β Φ` 打印成 `AACC⟪ α ⟫ @ Eo, Ei ⟪ β, COMM Φ ABORT P ⟫`。

要点(踩过的坑):
1. **抽象 telescope 会 panic**:`peelDelab`/`peelComp` 做 `getAppArgs[1]!`,假设 telescope 是具体的
   `Sigma`/`Tele.cons`;遇到抽象 `{TA TB : Tele}`(如 `aacc_inv` 的类型本身、抽象 test)会
   "index out of bounds"。→ 加 guard:仅当 `TA`/`TB` 是 `Tele.nil` 或 `Tele.cons …` 时才
   pretty-print,否则 `failure` 优雅回退默认打印。
2. **`iprop(…)` 包裹**:abort target `P` 用 `unpackIprop` 剥掉。
3. **spacing**:第二个 `⟪` 前用 `ppSpace`,避免 `∅⟪` 连在一起。

**重构(去重)**:`delabAtomicUpdate` 和 `delabAtomicAcc` 的 peel 逻辑(guard + `Eo`/`Ei` + `peelDelab`
`α`/`β`/`Φ` + 构造 `∃ x, α`/`∀ y, β`)抽成共享 helper `peelAtomicParts args αIdx βIdx ΦIdx`,返回
`(Eo, Ei, pre, comm, Φ)`;两个 delaborator 各自只剩一行组装 notation。顺带给 `delabAtomicUpdate` 也加上了
concrete-telescope guard(修掉它同样潜在的 panic)。AU 的 `#guard_msgs` 显示测试不变。

**`-∗?`(`wandM` / Rocq `maybe_wand`)的化简**:atomicWP 的 `Φ = λ.., ∀.. z, POST -∗? Φ(f)`,当
`POST = none` 时显示成 `none -∗? Φ`。Rocq 用 `cbn [maybe_wand]` 把 `maybe_wand None Q` 定义式化简为 `Q`。
照搬:在 `reduceTeleApps` 里加一条——`Iris.wandM` 且第一个参数是 `Option.none` 时规约到第二个参数
(用 **Name 字面量** `` `Iris.wandM `` 匹配,`wandM` 定义在 `ProgramLogic/Atomic` 更晚,不用 import)。
于是 **显示**(delab 经 `peelDelab`→`reduceTeleApps`)和 **tactic**(`itele_reduce`→`itele_reduce_apps`)
都会把 `none -∗? P` 变成 `P`。副作用:原来 proof 里 `itele_reduce` 之后的 `simp only [wandM]` 变冗余,
已删除(`Tests/Atomic.lean` inc_spec、`AtomicLock.lean` 各 physical spec 的 commit 分支)。

**最终显示**:
```
AACC ⟪ ∃ b, l ↦ some hl_val(#b) ⟫ @ ⊤ \ ∅, ∅
  ⟪ l ↦ some hl_val(#false), COMM ∀.. z, Φ hl_val(#())
    ABORT □ inv plockN (lockRel γ l) ∗ AU ⟪ … ⟫ ⟫
```
无 `Tele.app` / 无 `iprop(…)` / 无 `none -∗?`。仅剩的 `∀.. z` 是 POST-telescope(nil)的 vacuous
量词,和 `AU⟪⟫` 的显示**完全一致**(既有行为);tactic 侧 `itele_reduce` 会连它一起(`biTforall_nil`)
清掉,只有纯 delab 显示保留。
