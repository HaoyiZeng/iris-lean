module

public import Iris.Examples.Array
public import Iris.HeapLang.Lib.Par

@[expose] public section
namespace Iris.Examples.HeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.HeapLang Std PartialMap Spawn Par

section ArrayClient

variable {H : Type → Type}
variable {GF : BundledGFunctors} [LawfulFiniteMap H Nat]
variable [HeapLangGS hlc GF] [RwLockG GF] [ArcG GF] [ArrG GF H] [SpawnG GF]

/-! ## Model-level facts the client needs

The client's whole argument is: *the root cell never moves*.  `Impl.insert` splices
the new node in immediately **after** the node it is given, so inserting after the
root leaves the root at the head of the list — and in particular the root stays
live, so every insert after it succeeds. -/

/-- Inserting after the head leaves the head where it is. -/
theorem Arr.insert_head_stable (σ : Arr) (id : Nat) (v x : Int)
    (rest : List (Nat × Int)) (hd : σ.cells = (id, v) :: rest) :
    ((Arr.insert σ id x).1).cells.head? = some (id, v) ∧
    (Arr.insert σ id x).2 = some σ.counter := by
  have hany : σ.cells.any (·.1 = id) = true := by
    rw [List.any_eq_true]; exact ⟨(id, v), hd ▸ (by simp), by simp⟩
  unfold Arr.insert
  simp only [hany, ↓reduceIte]
  refine ⟨?_, trivial⟩
  rw [hd]
  simp

/-! ## The shared client invariant -/

def clientN : Namespace := ndot nroot "arrclient"

/-- What the two threads agree on: the array always starts with the root cell
    `(0, 1)`.  This is enough to know the root is live, hence every insert after
    it linearizes successfully. -/
def clientInv (γ : Arrγ) : IProp GF := iprop%
  ∃ σ : Arr, arrFrag γ σ ∗ ⌜σ.cells.head? = some (0, 1)⌝

instance instClientInvTimeless (γ : Arrγ) :
    Timeless (clientInv (GF := GF) (H := H) γ) := by
  unfold clientInv arrFrag; infer_instance

omit [SpawnG GF] in
/-- **Per-thread insert.**  The logically atomic `insert_spec` is linearized against
    the shared client invariant, which is opened only at the commit point.  Because
    the invariant pins the root at the head of the list, the insert is guaranteed to
    succeed — the thread gets a genuine node back. -/
theorem Impl.insert_conc (N : Namespace) (γ : Arrγ) (γp : GName)
    (platform node : Val) (x : Int)
    (hsub : (↑clientN : CoPset) ⊆ ((⊤ : CoPset) \ (↑N : CoPset))) :
  ⊢@{IProp GF}
    isArrInv N γ γp platform -∗
    inv clientN (clientInv γ) -∗
    Arr.isId γ node 0 -∗
    WP hl(&Impl.insert &platform &node #x)
      {{ v, ∃ (nid : Nat) (node' : Val),
              ⌜v = hl_val(some(&node'))⌝ ∗
              Arr.isId γ node 0 ∗ Arr.isId γ node' nid }} := by
  iintro #Hinv #Hcl Hid
  iapply Impl.insert_spec N γ γp platform node 0 x $$ Hinv Hid
  iauintro
  iapply aacc_inv _ _ _ _ hsub $$ Hcl
  iintro Hbody
  iunfold clientInv at Hbody
  icases Hbody with ⟨%σ, Hfrag, %hhd⟩
  -- the head of the list is the root, so `Arr.insert` really does fire
  obtain ⟨rest, hcells⟩ : ∃ rest, σ.cells = (0, 1) :: rest := by
    cases hc : σ.cells with
    | nil => simp [hc] at hhd
    | cons c cs =>
        have hc1 : c = (0, 1) := by simpa [hc] using hhd
        exact ⟨cs, by rw [hc1]⟩
  obtain ⟨hhd', hret⟩ := Arr.insert_head_stable σ 0 1 x rest hcells
  iaaccintro' with Hfrag
  · -- abort: nothing happened, put the abstract state straight back
    iintro Hfrag
    imodintro
    isplitl [Hfrag]
    · unfold clientInv
      iexists σ
      iframe Hfrag
      ipureintro; exact hhd
    · repeat' first | (imodintro; iassumption) | isplitl []
  · -- commit: the array grew by one node; the root is still at the head
    itele_reduce
    simp only [hret]
    iintro %ret Hβ
    icases Hβ with ⟨Hfrag, Hid, Hnew⟩
    imodintro
    isplitl [Hfrag]
    · unfold clientInv
      iexists (Arr.insert σ 0 x).1
      iframe Hfrag
      ipureintro; exact hhd'
    · icases Hnew with ⟨%node', %hret', Hnew⟩
      iexists σ.counter, node'
      isplitl []
      · ipureintro; exact hret'
      · iframe Hid Hnew

/-- **Two threads inserting concurrently** after the same root node.  Each holds its
    own strong reference (`Arr.isId`), and both succeed. -/
theorem Impl.parClient_spec (N : Namespace) (γ : Arrγ) (γp : GName)
    (platform node1 node2 : Val)
    (hsub : (↑clientN : CoPset) ⊆ ((⊤ : CoPset) \ (↑N : CoPset))) :
  ⊢@{IProp GF}
    isArrInv N γ γp platform -∗
    inv clientN (clientInv γ) -∗
    Arr.isId γ node1 0 -∗ Arr.isId γ node2 0 -∗
    WP hl(&Impl.insert &platform &node1 #2 ‖ &Impl.insert &platform &node2 #3)
      {{ v, ∃ v1 v2 : Val, ⌜v = hl_val((&v1, &v2))⌝ ∗
              (∃ (nid : Nat) (n' : Val), ⌜v1 = hl_val(some(&n'))⌝ ∗ Arr.isId γ n' nid) ∗
              (∃ (nid : Nat) (n' : Val), ⌜v2 = hl_val(some(&n'))⌝ ∗ Arr.isId γ n' nid) }} := by
  iintro #Hinv #Hcl Hid1 Hid2
  iapply (Par.wp_par
    (fun v => iprop% ∃ (nid : Nat) (n' : Val), ⌜v = hl_val(some(&n'))⌝ ∗
      Arr.isId γ node1 0 ∗ Arr.isId γ n' nid)
    (fun v => iprop% ∃ (nid : Nat) (n' : Val), ⌜v = hl_val(some(&n'))⌝ ∗
      Arr.isId γ node2 0 ∗ Arr.isId γ n' nid) _ _) $$ [Hid1] [Hid2] []
  · iapply Impl.insert_conc N γ γp platform node1 2 hsub $$ Hinv Hcl Hid1
  · iapply Impl.insert_conc N γ γp platform node2 3 hsub $$ Hinv Hcl Hid2
  · iintro %v1 %v2 ⟨⟨%nid1, %n1, %h1, -, Hn1⟩, ⟨%nid2, %n2, %h2, -, Hn2⟩⟩
    inext
    iexists v1, v2
    isplitl []
    · ipureintro; rfl
    · isplitl [Hn1]
      · iexists nid1, n1
        iframe Hn1
        ipureintro; exact h1
      · iexists nid2, n2
        iframe Hn2
        ipureintro; exact h2

/-! ## End-to-end setup

`Arr.isId` is *linear* — it carries one strong reference — so the two threads cannot
simply share the root handle: it has to be `Arc::clone`d.  The clone has to happen
before the array is bound to the invariant, because that is the only moment at which
the root's `arcAuth` is directly in our hands. -/

omit [SpawnG GF] in
/-- Duplicate the handle to the node at the head of a not-yet-shared array. -/
theorem Arr.isList_clone_head (γ : Arrγ) (id : Nat) (x : Int)
    (rest : List (Nat × Int)) (cnt : Nat) (node : Val) :
  ⊢@{IProp GF}
    Arr.isList γ { cells := (id, x) :: rest, counter := cnt } -∗
    Arr.isId γ node id -∗
    WP hl(&Arc.clone &node)
      {{ v, Arr.isList γ { cells := (id, x) :: rest, counter := cnt } ∗
            Arr.isId γ node id ∗ Arr.isId γ v id }} := by
  iintro Hlist Hid
  iunfold Arr.isList at Hlist
  icases Hlist with ⟨%M, Hcontent, Hstate⟩
  iunfold arrContent at Hcontent
  icases Hcontent with ⟨HM, %hwf, %hdom, Hview⟩
  iunfold exclusiveView at Hview
  icases Hview with ⟨Hghost, Hretired⟩
  iunfold isGhost at Hghost
  simp only [isGhostHelp]
  icases Hghost with ⟨%d, %hval, #Hat, Hslot, Hrest⟩
  iunfold Arr.isId at Hid
  icases Hid with ⟨%d', #Hat', Harc⟩
  ihave %hdd := metaAt_agree $$ Hat' Hat
  subst d'
  iunfold nodeSlotExclusive at Hslot
  icases Hslot with ⟨Hstrong, Hlock, Hcell, HP⟩
  iunfold arcHasStrong at Hstrong
  icases Hstrong with ⟨%n, %m, Hauth, %hn⟩
  iapply Arc.clone_spec (γ := d.arc) node d.mux $$ Harc
  iauintro
  iaaccintro' with Hauth
  · iintro Hauth
    imodintro
    iframe
    repeat' first | (imodintro; iassumption) | isplitl []
  · itele_reduce
    iintro Hpost
    icases Hpost with ⟨Hauth, Harc1, Harc2⟩
    imodintro
    -- put the (now heavier) reference count back into the slot
    isplitl [HM Hauth Hlock Hcell HP Hrest Hretired Hstate]
    · unfold Arr.isList arrContent exclusiveView isGhost
      iexists M
      iframe HM Hstate Hretired
      isplitl []
      · ipureintro; exact hwf
      isplitl []
      · ipureintro; exact hdom
      simp only [isGhostHelp]
      iexists d
      isplitl []
      · ipureintro; exact hval
      isplitl []
      · iexact Hat
      iframe Hrest
      unfold aliveSlot nodeSlotExclusive
      iframe Hlock Hcell HP
      unfold arcHasStrong
      iexists (n + 1), m
      iframe Hauth
      ipureintro; omega
    · isplitl [Harc1]
      · unfold Arr.isId
        iexists d
        iframe Harc1
        iexact Hat
      · unfold Arr.isId
        iexists d
        iframe Harc2
        iexact Hat

/-- Allocate the array, bind it to a platform, and hand out two root handles. -/
def Impl.clientSetup : Val := hl_val%
  λ _,
    let root := &Impl.init #1;
    let p := &Impl.platformNew #();
    let root2 := &Arc.clone root;
    (p, (root, root2))

omit [SpawnG GF] in
theorem Impl.clientSetup_spec (N : Namespace) :
  ⊢@{IProp GF}
    ⦃ True ⦄
      hl(&Impl.clientSetup #())
    ⦃ v, RET v;
      ∃ (γ : Arrγ) (γp : GName) (p n1 n2 : Val),
        ⌜v = hl_val((&p, (&n1, &n2)))⌝ ∗
        isArrInv N γ γp p ∗ inv clientN (clientInv γ) ∗
        Arr.isId γ n1 0 ∗ Arr.isId γ n2 0 ⦄ := by
  iintro %Φ - HΦ
  iapply wp_fupd
  unfold Impl.clientSetup
  wp_pures
  wp_bind &Impl.init _
  iapply Impl.init_spec (1 : Int)
  · itrivial
  iintro %root !> ⟨%γ, Hlist, Hid⟩
  wp_pures
  wp_bind &Impl.platformNew _
  iapply Impl.platformNew_spec
  · itrivial
  iintro %p !> ⟨%γp, Hplat⟩
  wp_pures
  wp_bind &Arc.clone _
  simp only [Arr.init]
  ihave Hclone := Arr.isList_clone_head γ 0 1 [] 1 root $$ Hlist Hid
  iapply wp_wand $$ Hclone
  iintro %root2 ⟨Hlist, Hid1, Hid2⟩
  wp_pures
  -- publish the array, then publish the client's own view of it
  imod Arr.isList_bind N γ γp { cells := [(0, 1)], counter := 1 } p $$ Hlist Hplat
    with Harr
  iunfold Arr.isArr at Harr
  icases Harr with ⟨#Hinv, Hfrag⟩
  ihave Hbody : clientInv γ $$ [Hfrag]
  · unfold clientInv
    iexists { cells := [(0, 1)], counter := 1 }
    iframe Hfrag
    ipureintro; rfl
  imod inv_alloc clientN ⊤ (clientInv γ) $$ Hbody with #Hcl
  imodintro
  iapply HΦ
  iexists γ, γp, p, root, root2
  isplitl []
  · ipureintro; rfl
  iframe Hid1 Hid2
  isplitl []
  · iexact Hinv
  · iexact Hcl

/-! ## Putting it together

`par`'s two thunks are *values*, and HeapLang substitution does not descend into
values, so the thunks have to be written as expression-level lambdas that the
enclosing binders can actually reach. -/

/-- Fork the two inserts. -/
def Impl.parInsert : Val := hl_val%
  λ p n1 n2, &Par.par (λ _, &Impl.insert p n1 #2) (λ _, &Impl.insert p n2 #3)

/-- The complete client: build the array, hand each thread its own root handle,
    and insert concurrently. -/
def Impl.client : Val := hl_val%
  λ _,
    let ps := &Impl.clientSetup #();
    let p := fst(ps);
    let n1 := fst(snd(ps));
    let n2 := snd(snd(ps));
    &Impl.parInsert p n1 n2

/-- The result of one thread: a genuine new node. -/
def insertedNode (γ : Arrγ) (v : Val) : IProp GF := iprop%
  ∃ (nid : Nat) (n' : Val), ⌜v = hl_val(some(&n'))⌝ ∗ Arr.isId γ n' nid

theorem Impl.parInsert_spec (N : Namespace) (γ : Arrγ) (γp : GName)
    (platform node1 node2 : Val)
    (hsub : (↑clientN : CoPset) ⊆ ((⊤ : CoPset) \ (↑N : CoPset))) :
  ⊢@{IProp GF}
    isArrInv N γ γp platform -∗
    inv clientN (clientInv γ) -∗
    Arr.isId γ node1 0 -∗ Arr.isId γ node2 0 -∗
    WP hl(&Impl.parInsert &platform &node1 &node2)
      {{ v, ∃ v1 v2 : Val, ⌜v = hl_val((&v1, &v2))⌝ ∗
              insertedNode γ v1 ∗ insertedNode γ v2 }} := by
  iintro #Hinv #Hcl Hid1 Hid2
  unfold Impl.parInsert
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  iapply (Par.par_spec
    (fun v => iprop% Arr.isId γ node1 0 ∗ insertedNode γ v)
    (fun v => iprop% Arr.isId γ node2 0 ∗ insertedNode γ v) _ _) $$ [Hid1] [Hid2] []
  · wp_pures
    ihave Hw := Impl.insert_conc N γ γp platform node1 2 hsub $$ Hinv Hcl Hid1
    iapply wp_wand $$ Hw
    iintro %v ⟨%nid, %n', %hv, Hid, Hn⟩
    unfold insertedNode
    iframe Hid
    iexists nid, n'
    iframe Hn
    ipureintro; exact hv
  · wp_pures
    ihave Hw := Impl.insert_conc N γ γp platform node2 3 hsub $$ Hinv Hcl Hid2
    iapply wp_wand $$ Hw
    iintro %v ⟨%nid, %n', %hv, Hid, Hn⟩
    unfold insertedNode
    iframe Hid
    iexists nid, n'
    iframe Hn
    ipureintro; exact hv
  · iintro %v1 %v2
    inext
    iintro ⟨⟨-, Hn1⟩, ⟨-, Hn2⟩⟩
    inext
    iexists v1, v2
    iframe Hn1 Hn2
    ipureintro; rfl

/-- Concrete namespaces: the array's invariant and the client's are disjoint. -/
def arrN : Namespace := ndot nroot "arr"

theorem clientN_sub_arrN : (↑clientN : CoPset) ⊆ ((⊤ : CoPset) \ (↑arrN : CoPset)) := by
  have hd : (↑clientN : CoPset) ## ↑arrN :=
    ndot_ne_disjoint nroot (by decide : "arrclient" ≠ "arr")
  intro y hy
  rw [CoPset.in_diff]
  exact ⟨CoPset.mem_full, fun hya => hd y ⟨hy, hya⟩⟩

/-- **End to end.**  Allocating a one-element array and running two concurrent
    inserts after its root: both threads come back with a fresh, live node. -/
theorem Impl.client_spec :
  ⊢@{IProp GF}
    ⦃ True ⦄
      hl(&Impl.client #())
    ⦃ v, RET v;
      ∃ (γ : Arrγ) (v1 v2 : Val), ⌜v = hl_val((&v1, &v2))⌝ ∗
        insertedNode γ v1 ∗ insertedNode γ v2 ⦄ := by
  iintro %Φ - HΦ
  unfold Impl.client
  wp_pures
  wp_bind &Impl.clientSetup _
  iapply Impl.clientSetup_spec arrN
  · itrivial
  iintro %ps !> ⟨%γ, %γp, %p, %n1, %n2, %hps, #Hinv, #Hcl, Hid1, Hid2⟩
  subst hps
  wp_pures
  ihave Hpar := Impl.parInsert_spec arrN γ γp p n1 n2 clientN_sub_arrN
    $$ Hinv Hcl Hid1 Hid2
  iapply wp_wand $$ Hpar
  iintro %v ⟨%v1, %v2, %hv, Hn1, Hn2⟩
  iapply HΦ
  iexists γ, v1, v2
  iframe Hn1 Hn2
  ipureintro; exact hv

end ArrayClient

end Iris.Examples.HeapLang
