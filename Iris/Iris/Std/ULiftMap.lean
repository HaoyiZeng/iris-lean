module

public import Iris.Std.PartialMap
public import Iris.Algebra.ULiftInst

@[expose] public section

/-!
# `ULift` for map types

Lean 4 has no universe cumulativity, so a map at `Type u → Type u` cannot serve
where `Type u → Type (u+1)` is required.  That situation arises for the
generalised heap: `constOF` fixes the resource universe, which forces
`HeapView K V H` — and hence `H V` — one level above the values `V`.

Lifting the *map* rather than the *values* is what keeps `l ↦ v` unchanged for
clients: `v` retains its original type, only the container moves up.
-/

namespace Iris.Std

/-- The map `M`, with its container type lifted one universe. -/
abbrev ULiftMap (M : Type u → Type v) : Type u → Type (max v w) :=
  fun V => ULift.{w} (M V)

variable {M : Type u → Type v} {K : Type _}

instance instPartialMapULiftMap [PartialMap M K] : PartialMap (ULiftMap.{u, v, w} M) K where
  get? m k := PartialMap.get? m.down k
  insert m k v := ⟨PartialMap.insert m.down k v⟩
  delete m k := ⟨PartialMap.delete m.down k⟩
  empty := ⟨PartialMap.empty⟩
  bindAlter f m := ⟨PartialMap.bindAlter f m.down⟩
  merge op m₁ m₂ := ⟨PartialMap.merge op m₁.down m₂.down⟩

instance instLawfulPartialMapULiftMap [LawfulPartialMap M K] :
    LawfulPartialMap (ULiftMap.{u, v, w} M) K where
  get?_empty k := LawfulPartialMap.get?_empty (M := M) k
  get?_insert_eq h := LawfulPartialMap.get?_insert_eq (M := M) h
  get?_insert_ne h := LawfulPartialMap.get?_insert_ne (M := M) h
  get?_delete_eq h := LawfulPartialMap.get?_delete_eq (M := M) h
  get?_delete_ne h := LawfulPartialMap.get?_delete_ne (M := M) h
  get?_bindAlter := LawfulPartialMap.get?_bindAlter (M := M)
  get?_merge := LawfulPartialMap.get?_merge (M := M)
  equiv_iff_eq {V m₁ m₂} :=
    Iff.intro
      (fun h => by
        cases m₁; cases m₂
        exact congrArg ULift.up (LawfulPartialMap.equiv_iff_eq (M := M) (V := V) |>.mp h))
      (fun h => LawfulPartialMap.equiv_iff_eq (M := M) (V := V) |>.mpr (congrArg ULift.down h))

instance instFiniteMapULiftMap [FiniteMap M K] : FiniteMap (ULiftMap.{u, v, w} M) K where
  toList m := FiniteMap.toList m.down

instance instLawfulFiniteMapULiftMap [LawfulFiniteMap M K] :
    LawfulFiniteMap (ULiftMap.{u, v, w} M) K where
  toList_empty := LawfulFiniteMap.toList_empty (M := M)
  toList_noDupKeys := LawfulFiniteMap.toList_noDupKeys (M := M)
  toList_get := LawfulFiniteMap.toList_get (M := M)

instance instHeapULiftMap [Heap M K] : Heap (ULiftMap.{u, v, w} M) K where
  notFull m := Heap.notFull m.down
  fresh h := Heap.fresh (M := M) h
  get?_fresh := Heap.get?_fresh (M := M)

instance instUnboundedHeapULiftMap [UnboundedHeap M K] :
    UnboundedHeap (ULiftMap.{u, v, w} M) K where
  notFull_empty := UnboundedHeap.notFull_empty (M := M)
  notFull_insert_fresh := UnboundedHeap.notFull_insert_fresh (M := M)

end Iris.Std
