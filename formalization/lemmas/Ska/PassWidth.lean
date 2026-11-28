import lemmas.Ska.PassClosureA

/-!
# The width is a depth bound (track F, README Gaps 16)

`WidthFin` (`PassDepth.lean`) asks that the identities a pass loop finishes lie
in one finite list.  By `gIn_okId` every identity in the graph is already
`OkId`: its formula is among a finite list and the leaves of its subject sock
are among a finite list.  So the only thing left is the depth of the subject
socks: `widthFin_of_depth` proves `WidthFin` from `DepthFin`, a bound on that
depth along every chain of passes, and `depthFin_of_width` the converse.  In
particular the order in which `+git:mi` meets the entries of `done` (point (c)
of Gaps 16) cannot make a loop wider by itself: a different answer at the same
call adds no identity unless it leads to a deeper subject sock.

* `BT.depthW`, `btsUpTo`, `mem_btsUpTo`: the trees of bounded depth over a
  finite list of leaves are a finite list.
* `btSock`, `btSock_capeBT`: a shaped sock is its tree.
* `sockDepth`, `okIdsUpTo`, `mem_okIdsUpTo`: the `OkId` identities of bounded
  depth are a finite list.
* `gIn_okId_reach`: along the passes from the loop's entry, every identity in
  the graph is `OkId`.
* `DepthFin`, `widthFin_of_depth`, `depthFin_of_width`, `passLoop_returns_wd`.
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## 1. Trees of bounded depth -/

/-- The depth of a tree: a leaf has depth 0. -/
def BT.depthW {α : Type} : BT α → Nat
  | BT.leaf _ => 0
  | BT.node l r => Nat.max (BT.depthW l) (BT.depthW r) + 1

/-- Every tree of depth at most `D` with leaves among `Ls`. -/
def btsUpTo {α : Type} (Ls : List α) : Nat → List (BT α)
  | 0 => Ls.map BT.leaf
  | D + 1 => Ls.map BT.leaf ++ (btsUpTo Ls D).flatMap fun x => (btsUpTo Ls D).map (BT.node x)

theorem mem_btsUpTo {α : Type} (Ls : List α) :
    ∀ (D : Nat) (t : BT α), BT.depthW t ≤ D → (∀ a ∈ BT.leaves t, a ∈ Ls) → t ∈ btsUpTo Ls D
  | 0, BT.leaf a, _, hl => List.mem_map.mpr ⟨a, hl a (by simp [BT.leaves]), rfl⟩
  | D + 1, BT.leaf a, _, hl =>
    List.mem_append_left _ (List.mem_map.mpr ⟨a, hl a (by simp [BT.leaves]), rfl⟩)
  | 0, BT.node l r, hd, _ => absurd hd (by simp [BT.depthW])
  | D + 1, BT.node l r, hd, hl => by
    have hd' : Nat.max (BT.depthW l) (BT.depthW r) ≤ D := by simp only [BT.depthW] at hd; omega
    have h1 : BT.depthW l ≤ D := Nat.le_trans (Nat.le_max_left _ _) hd'
    have h2 : BT.depthW r ≤ D := Nat.le_trans (Nat.le_max_right _ _) hd'
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨l, ?_, List.mem_map.mpr ⟨r, ?_, rfl⟩⟩)
    · exact mem_btsUpTo Ls D l h1 (fun a ha => hl a (by simp [BT.leaves, ha]))
    · exact mem_btsUpTo Ls D r h2 (fun a ha => hl a (by simp [BT.leaves, ha]))

/-! ## 2. A shaped sock is its tree -/

/-- The sock of a tree of socks: a leaf is its sock, a node the cell of its
two socks. -/
def btSock : BT Sock → Sock
  | BT.leaf s => s
  | BT.node l r =>
    match btSock l, btSock r with
    | Sock.mk c1 d1, Sock.mk c2 d2 => Sock.mk (Cape.cell c1 c2) (Noun.cell d1 d2)
    | _, _ => Sock.void

theorem btSock_capeBT : ∀ (c : Cape) (d : Noun), Shaped c d → btSock (capeBT c d) = Sock.mk c d
  | Cape.yes, _, _ => rfl
  | Cape.no, _, _ => rfl
  | Cape.cell _ _, Noun.atom _, h => absurd h (by simp [Shaped])
  | Cape.cell a b, Noun.cell x y, h => by
    simp only [capeBT, btSock, btSock_capeBT a x h.1, btSock_capeBT b y h.2]

/-- The depth of the tree of a sock. -/
def sockDepth : Sock → Nat
  | Sock.void => 0
  | Sock.mk c d => BT.depthW (capeBT c d)

/-- Every identity with a formula among `Fs` and a subject of depth at most
`D` with leaves among `Ls`. -/
def okIdsUpTo (Fs : List Noun) (Ls : List Sock) (D : Nat) : List Ident :=
  Fs.flatMap fun f => (btsUpTo Ls D).map fun t => (btSock t, f)

/-- **The `OkId` identities of bounded depth are a finite list.** -/
theorem mem_okIdsUpTo {Fs : List Noun} {Ls : List Sock} {D : Nat} {i : Ident} (h : OkId Fs Ls i)
    (hd : sockDepth i.1 ≤ D) : i ∈ okIdsUpTo Fs Ls D := by
  obtain ⟨hf, c, d, e, hs, hl⟩ := h
  have hd' : BT.depthW (capeBT c d) ≤ D := by rw [e] at hd; exact hd
  refine List.mem_flatMap.mpr ⟨i.2, hf, List.mem_map.mpr ⟨capeBT c d, mem_btsUpTo Ls D _ hd' hl, ?_⟩⟩
  rw [btSock_capeBT c d hs, ← e]

/-! ## 3. The width from the depth -/

/-- **Along the passes from the loop's entry, every identity in the graph is
`OkId`**: `gIn_okId` at every state `PassReachQ` reaches. -/
theorem gIn_okId_reach (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNorm memoF) (hmI : MemoNI memoF) {As : List Nat} {B : Nat} (hmG : MemoG (NGood As B) memoF)
    {id : Ident} {index : Nat} {rest : List Ident} {x : Nat × SkaState M R}
    (hc : ChainInv memoF id index rest x.2) (hx : ClInv (NGood As B) x.2) :
    ∀ y, PassReachQ env memoF id index x y → ∀ i, GIn y.2 i → OkId (nounsUpTo As B) (leafList As B) i := by
  intro y hy
  have hcy : ClInv (NGood As B) y.2 := by
    induction hy with
    | refl => exact hx
    | step _ hp ih => exact passGoOn_C env memoF (subC_nGood As B) (safC_nGood As B) hmG ih hp
  have hiy := passReachQ_inv env hmF hmT hmN hmI hy hc
  intro i hi
  cases e : Treap.get y.2.g i with
  | none => exact absurd e hi
  | some d => exact gIn_okId hcy hiy.2.1 e

/-- **The depth of one pass loop**: along every chain of passes from `x`, the
subject socks of the identities that entered the graph after `x` and are not
on the stack (the functions the loop finished) have depth at most one bound. -/
def DepthFin (env : Env R) (memoF : Memo M) (id : Ident) (index : Nat) (x : Nat × SkaState M R) : Prop :=
  ∀ f : Nat → Nat × SkaState M R, (∀ k, PassNextQ env memoF id index x (f (k + 1)) (f k)) →
    ∃ D, ∀ k i, GIn (f k).2 i → ¬ GIn x.2 i → i ∉ (f k).2.stk → sockDepth i.1 ≤ D

/-- **The width from the depth.** -/
theorem widthFin_of_depth (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNorm memoF) (hmI : MemoNI memoF) {As : List Nat} {B : Nat} (hmG : MemoG (NGood As B) memoF)
    {id : Ident} {index : Nat} {rest : List Ident} {x : Nat × SkaState M R}
    (hc : ChainInv memoF id index rest x.2) (hx : ClInv (NGood As B) x.2)
    (hD : DepthFin env memoF id index x) : WidthFin env memoF id index x := by
  intro f hf
  obtain ⟨D, hD'⟩ := hD f hf
  refine ⟨okIdsUpTo (nounsUpTo As B) (leafList As B) D, fun k i hi hnx hs => ?_⟩
  exact mem_okIdsUpTo (gIn_okId_reach env hmF hmT hmN hmI hmG hc hx _ (hf k).1 i hi) (hD' k i hi hnx hs)

theorem depth_bound_list : ∀ l : List Ident, ∃ D, ∀ i ∈ l, sockDepth i.1 ≤ D
  | [] => ⟨0, fun _ h => absurd h (List.not_mem_nil)⟩
  | a :: l => by
    obtain ⟨D, hD⟩ := depth_bound_list l
    refine ⟨Nat.max (sockDepth a.1) D, fun i hi => ?_⟩
    rcases List.mem_cons.mp hi with e | hi
    · rw [e]; exact Nat.le_max_left _ _
    · exact Nat.le_trans (hD i hi) (Nat.le_max_right _ _)

/-- **The depth from the width**: the two hypotheses say the same. -/
theorem depthFin_of_width {env : Env R} {memoF : Memo M} {id : Ident} {index : Nat}
    {x : Nat × SkaState M R} (hw : WidthFin env memoF id index x) : DepthFin env memoF id index x := by
  intro f hf
  obtain ⟨I, hI⟩ := hw f hf
  obtain ⟨D, hD⟩ := depth_bound_list I
  exact ⟨D, fun k i hi hnx hs => hD i (hI k i hi hnx hs)⟩

/-- **The pass loop of one component returns** from `KruskalBT`, `RunHalts`,
the depth `DepthFin`, a good stack at its entry, and the arm invariant at its
entry: `passLoop_returns_wc` with the width given by the depth. -/
theorem passLoop_returns_wd (hK : KruskalBT) (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF)
    (hmT : MemoTP memoF) (hmN : MemoNorm memoF) (hmI : MemoNI memoF) (hrun : RunHalts env memoF)
    (hhe : env.he = Compiler.heSock) {As : List Nat} {B : Nat} (hmG : MemoG (NGood As B) memoF)
    (id : Ident) (index : Nat) (rest : List Ident) (x : Nat × SkaState M R)
    (hc : ChainInv memoF id index rest x.2) (hsg : SG env x.2) (hx : ClInv (NGood As B) x.2)
    (hD : DepthFin env memoF id index x) :
    ∃ n r, passLoop env memoF n id index x.1 x.2 = some r :=
  passLoop_returns_wc hK env hmF hmT hmN hmI hrun hhe hmG id index rest x hc hsg hx
    (widthFin_of_depth env hmF hmT hmN hmI hmG hc hx hD)

end Ana
end SkaModel
end Formalization
