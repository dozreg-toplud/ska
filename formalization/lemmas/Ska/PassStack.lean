import lemmas.Ska.PassIdents
import lemmas.Ska.HeBound

/-!
# No infinite sequence of pushes that stay on the stack (track F, Gaps 16)

The author's termination argument (the comment of `+recursive-call`): "an
infinite chain has infinitely many functions with one formula (the callable
formulas are finitely many), so past the threshold HE applies to it".  Here
it is proved for every sequence of pushed identities whose earlier members
are all on the stack when a later one is pushed, with no push tree and no
finite branching:

* `recLoop_none`, `recursiveCall_none`: when `+recursive-call` answers `~`
  with the embedding test on (`he-threshold` frames of the kid's formula on
  the stack), no frame of that formula is embedded (`he kid.1 j.1 = false`);
* `resolveStep_new`: `resolve` analyses `idT` afresh exactly after a miss in
  the graph, a miss of `+git:mi` and that answer `~`, so `push_guard`: the
  pushed identity is not `he`-above any frame of its formula on the stack once
  the threshold is reached;
* **`noStackSeq_of_kruskal`**: from `KruskalBT`, finitely many formulas, and
  a tree view `sub` of identities for which an embedding of trees gives `he`
  of the later subject over the earlier one, there is no infinite sequence of
  distinct identities, each pushed with the guard of `push_guard` against a
  stack that holds every earlier one.

Two instances: an infinite descent of nested `+analyze` calls that never
return (every root stays on the stack), and the members of one component's
pass loop (with fix (b), dab8478, `+cull` runs only before the first pass and
at the stable end, and a nested `+pop` removes only its own members, so a
member stays on the stack until the loop ends).  What it does not cover is
the width of the analysis: the identities that a loop pushes and that finish
(popped into `done`) before later ones are pushed are never on the stack
together, so the embedding test never compares them (README Gaps 16).
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- **`+recursive-call`'s loop answering `~`**: no frame of the kid's formula
is embedded by the kid's subject when the embedding test is on. -/
theorem recLoop_none {he : Sock → Sock → Bool} {heOn : Bool} {g : Sock × Noun → Option Datum}
    {kid : Sock × Noun} : ∀ {stk : List (Sock × Noun)}, recLoop he heOn g kid stk = some none →
    ∀ j ∈ stk, j.2 = kid.2 → heOn = true → he kid.1 j.1 = false
  | [], _, j, hj, _, _ => absurd hj List.not_mem_nil
  | i :: stk, h, j, hj, hf, ho => by
    unfold recLoop at h
    split at h
    · rename_i hne
      rcases List.mem_cons.mp hj with rfl | hj
      · exact absurd hf.symm hne
      · exact recLoop_none h j hj hf ho
    · split at h
      · cases h
      · cases h
      · split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨_, _, h⟩ := h
          cases h
        · rename_i hc
          rcases List.mem_cons.mp hj with rfl | hj
          · cases e : he kid.1 j.1
            · rfl
            · exact absurd ⟨ho, e⟩ hc
          · exact recLoop_none h j hj hf ho

/-- **`+recursive-call` answering `~` past the threshold**: with at least
`he-threshold` frames of the kid's formula on the stack, the kid's subject
embeds none of their subjects. -/
theorem recursiveCall_none {he : Sock → Sock → Bool} {th : Nat} {kid : Sock × Noun}
    {stk : List (Sock × Noun)} {g : Sock × Noun → Option Datum}
    (h : recursiveCall he th kid stk g = some none)
    (hth : th ≤ (stk.filter (fun i => i.2 = kid.2)).length) :
    ∀ j ∈ stk, j.2 = kid.2 → he kid.1 j.1 = false :=
  fun j hj hf => recLoop_none h j hj hf (decide_eq_true hth)

/-- **When `resolve` analyses afresh**: a miss in the graph, a miss of
`+git:mi` in `done`, and `+recursive-call` answering `~`. -/
theorem resolveStep_new {env : Env R} {res : ResGo M R} {an : AnaGo M R} {orig idT : Ident}
    {gen : GenS M R} (hg : Treap.get gen.st.g idT = none) (hm : gitMi gen.st.done orig.2 idT.1 = some none)
    (hr : recursiveCall env.he env.threshold idT gen.st.stk (gCore gen.st.g) = some none) :
    resolveStep env res an orig idT gen =
      (an idT gen.st).map fun r => ((idT, gitG r.2.g idT), { gen with st := r.2, low := min gen.low r.1 }) := by
  simp only [resolveStep, hg, hm, hr]

/-- **The guard of a push**: an identity that `resolve` analyses afresh, with
`he-threshold` frames of its formula on the stack, embeds none of them. -/
theorem push_guard {env : Env R} {idT : Ident} {gen : GenS M R}
    (hr : recursiveCall env.he env.threshold idT gen.st.stk (gCore gen.st.g) = some none)
    (hth : env.threshold ≤ (gen.st.stk.filter (fun i => i.2 = idT.2)).length) :
    ∀ j ∈ gen.st.stk, j.2 = idT.2 → env.he idT.1 j.1 = false :=
  recursiveCall_none hr hth

/-- `n` distinct elements of a list with one formula make its filter at least `n` long. -/
theorem count_ge_of_seq {w : Nat → Ident} {s : Nat → Nat} (hs : ∀ n, s n < s (n + 1))
    (hinj : ∀ i j, i < j → w i ≠ w j) {F : Noun} (hF : ∀ n, (w (s n)).2 = F) (S : List Ident) :
    ∀ n, (∀ k, k < n → w (s k) ∈ S) → n ≤ (S.filter (fun i => i.2 = F)).length := by
  have build : ∀ n, ∃ l : List Ident, l.Nodup ∧ l.length = n ∧ ∀ x ∈ l, ∃ k, k < n ∧ x = w (s k) := by
    intro n
    induction n with
    | zero => exact ⟨[], List.nodup_nil, rfl, fun _ h => absurd h List.not_mem_nil⟩
    | succ n ih =>
      obtain ⟨l, hl, hlen, hx⟩ := ih
      refine ⟨w (s n) :: l, List.nodup_cons.mpr ⟨fun hm => ?_, hl⟩, by simp [hlen], fun x hx' => ?_⟩
      · obtain ⟨k, hk, e⟩ := hx _ hm
        exact hinj (s k) (s n) (strictMono_le hs hk) e.symm
      · rcases List.mem_cons.mp hx' with rfl | hx'
        · exact ⟨n, Nat.lt_succ_self n, rfl⟩
        · obtain ⟨k, hk, e⟩ := hx x hx'
          exact ⟨k, by omega, e⟩
  intro n hS
  obtain ⟨l, hl, hlen, hx⟩ := build n
  rw [← hlen]
  refine hl.length_le_of_subset fun x hx' => ?_
  obtain ⟨k, hk, rfl⟩ := hx x hx'
  exact List.mem_filter.mpr ⟨hS k hk, by simp [hF k]⟩

/-- **No infinite sequence of pushes that stay on the stack**, from Kruskal's
theorem.  `w n` is the `n`-th pushed identity and `S n` the stack at its push;
the identities are distinct, their formulas are among `Fs`, every earlier one
is on the stack at a later push, and each push has the guard of `push_guard`
(past `th` frames of its formula, `he` of its subject over theirs is false).
`hemb` is the tree view: an embedding of the trees of an earlier and a later
identity gives `he` of the later subject over the earlier one. -/
theorem noStackSeq_of_kruskal {L : Type} (hK : KruskalBT) (ls : List L) (hls : ∀ a : L, a ∈ ls)
    (he : Sock → Sock → Bool) (th : Nat) (sub : Ident → BT L)
    (hemb : ∀ a b : Ident, BTEmb (sub a) (sub b) → he b.1 a.1 = true) (Fs : List Noun) :
    ¬ ∃ (w : Nat → Ident) (S : Nat → List Ident),
      (∀ n, (w n).2 ∈ Fs) ∧ (∀ i j, i < j → w i ≠ w j) ∧ (∀ i j, i < j → w i ∈ S j) ∧
      (∀ j, th ≤ ((S j).filter (fun i => i.2 = (w j).2)).length →
        ∀ x ∈ S j, x.2 = (w j).2 → he (w j).1 x.1 = false) := by
  rintro ⟨w, S, hFs, hinj, hstk, hguard⟩
  obtain ⟨F, hF⟩ := pigeon_inf Fs (fun n => (w n).2) hFs
  obtain ⟨s, hs, hsF⟩ := subseq_of_inf hF
  obtain ⟨i, j, hij, hb⟩ := hK L ls hls (fun n => sub (w (s (th + n))))
  have hlt : s (th + i) < s (th + j) := strictMono_le hs (by omega)
  have hcount : th ≤ ((S (s (th + j))).filter (fun x => x.2 = (w (s (th + j))).2)).length := by
    rw [hsF (th + j)]
    exact Nat.le_trans (Nat.le_add_right th j)
      (count_ge_of_seq hs hinj hsF _ (th + j) fun k hk => hstk _ _ (strictMono_le hs hk))
  have hfalse := hguard (s (th + j)) hcount (w (s (th + i))) (hstk _ _ hlt)
    (by rw [hsF (th + i), hsF (th + j)])
  rw [hemb _ _ hb] at hfalse
  cases hfalse

/-! ## The tree view of a sock under which an embedding gives `+he-sock` -/

/-- The binary tree of a sock: a node where the cape is a cell over a cell,
else a leaf holding the sock. -/
def capeBT : Cape → Noun → BT Sock
  | Cape.cell a b, Noun.cell d e => BT.node (capeBT a d) (capeBT b e)
  | c, d => BT.leaf (Sock.mk c d)

/-- A sock whose data is a cell wherever its cape is a cell. -/
def Shaped : Cape → Noun → Prop
  | Cape.cell a b, Noun.cell d e => Shaped a d ∧ Shaped b e
  | Cape.cell _ _, Noun.atom _ => False
  | _, _ => True

theorem capeBT_leaf {c : Cape} {d : Noun} {a : Sock} (hs : Shaped c d) (h : capeBT c d = BT.leaf a) :
    a = Sock.mk c d := by
  cases c with
  | cell x y =>
    cases d with
    | atom _ => exact absurd hs (by simp [Shaped])
    | cell _ _ => simp [capeBT] at h
  | yes => simp only [capeBT, BT.leaf.injEq] at h; exact h.symm
  | no => simp only [capeBT, BT.leaf.injEq] at h; exact h.symm

theorem capeBT_node {c : Cape} {d : Noun} {t1 t2 : BT Sock} (h : capeBT c d = BT.node t1 t2) :
    ∃ a b d1 d2, c = Cape.cell a b ∧ d = Noun.cell d1 d2 ∧ capeBT a d1 = t1 ∧ capeBT b d2 = t2 := by
  cases c with
  | cell x y =>
    cases d with
    | atom _ => simp [capeBT] at h
    | cell d1 d2 =>
      simp only [capeBT, BT.node.injEq] at h
      exact ⟨x, y, d1, d2, rfl, rfl, h.1, h.2⟩
  | yes => simp [capeBT] at h
  | no => simp [capeBT] at h

open Compiler in
theorem heSock_cape_le {cy cx : Cape} {dy dx : Noun} (h : heSock (Sock.mk cy dy) (Sock.mk cx dx) = true) :
    capeSize cx ≤ capeSize cy := by
  by_cases e : Sock.mk cy dy = Sock.mk cx dx
  · cases e; exact Nat.le_refl _
  · obtain ⟨_, _, _, _, e1, e2, hle⟩ := heSock_size h e
    cases e1; cases e2; exact hle

open Compiler in
/-- **An embedding of the trees gives `+he-sock`**: if the tree of the sock
`x` embeds in the tree of `y`, both shaped, then `(he-sock y x)`. -/
theorem heSock_of_btEmb : ∀ {s t : BT Sock}, BTEmb s t → ∀ {cx cy : Cape} {dx dy : Noun},
    Shaped cx dx → Shaped cy dy → capeBT cx dx = s → capeBT cy dy = t →
    heSock (Sock.mk cy dy) (Sock.mk cx dx) = true := by
  intro s t h
  induction h with
  | leaf a =>
    intro cx cy dx dy hx hy ex ey
    rw [← capeBT_leaf hx ex] at *
    rw [capeBT_leaf hy ey, heSock.eq_def, if_pos rfl]
  | @left s t1 t2 _ ih =>
    intro cx cy dx dy hx hy ex ey
    obtain ⟨a, b, d1, d2, rfl, rfl, e1, _⟩ := capeBT_node ey
    have hi := ih hx hy.1 ex e1
    have hle := heSock_cape_le hi
    rw [heSock.eq_def]
    split
    · rfl
    · simp only
      rw [if_neg (by simp only [capeSize]; omega)]
      cases cx <;> simp [So.hed, hi]
  | @right s t1 t2 _ ih =>
    intro cx cy dx dy hx hy ex ey
    obtain ⟨a, b, d1, d2, rfl, rfl, _, e2⟩ := capeBT_node ey
    have hi := ih hx hy.2 ex e2
    have hle := heSock_cape_le hi
    rw [heSock.eq_def]
    split
    · rfl
    · simp only
      rw [if_neg (by simp only [capeSize]; omega)]
      cases cx <;> simp [So.tel, hi]
  | @node s1 s2 t1 t2 _ _ ih1 ih2 =>
    intro cx cy dx dy hx hy ex ey
    obtain ⟨a, b, d1, d2, rfl, rfl, e1, e2⟩ := capeBT_node ey
    obtain ⟨c, d, f1, f2, rfl, rfl, g1, g2⟩ := capeBT_node ex
    have h1 := ih1 hx.1 hy.1 g1 e1
    have h2 := ih2 hx.2 hy.2 g2 e2
    have l1 := heSock_cape_le h1
    have l2 := heSock_cape_le h2
    rw [heSock.eq_def]
    split
    · rfl
    · simp only
      rw [if_neg (by simp only [capeSize]; omega)]
      simp [So.hed, So.tel, h1, h2]

/-! ## With `+he-sock` and finitely many leaves -/

/-- Relabel the leaves of a tree. -/
def BT.map {α β : Type} (f : α → β) : BT α → BT β
  | BT.leaf a => BT.leaf (f a)
  | BT.node l r => BT.node (BT.map f l) (BT.map f r)

/-- The leaves of a tree. -/
def BT.leaves {α : Type} : BT α → List α
  | BT.leaf a => [a]
  | BT.node l r => BT.leaves l ++ BT.leaves r

/-- An embedding of relabelled trees is one of the trees, when the labels
are relabelled injectively on a set holding every leaf. -/
theorem btEmb_of_map {α β : Type} {f : α → β} {P : α → Prop}
    (hf : ∀ x y, P x → P y → f x = f y → x = y) :
    ∀ {s' t' : BT β}, BTEmb s' t' → ∀ {s t : BT α}, s' = BT.map f s → t' = BT.map f t →
      (∀ x ∈ BT.leaves s, P x) → (∀ x ∈ BT.leaves t, P x) → BTEmb s t := by
  intro s' t' h
  induction h with
  | leaf a =>
    intro s t es et ps pt
    cases s with
    | node _ _ => simp [BT.map] at es
    | leaf x =>
    cases t with
    | node _ _ => simp [BT.map] at et
    | leaf y =>
    simp only [BT.map, BT.leaf.injEq] at es et
    have e : x = y := hf x y (ps x (by simp [BT.leaves])) (pt y (by simp [BT.leaves])) (es.symm.trans et)
    rw [e]; exact BTEmb.leaf y
  | left _ ih =>
    intro s t es et ps pt
    cases t with
    | leaf _ => simp [BT.map] at et
    | node u1 u2 =>
    simp only [BT.map, BT.node.injEq] at et
    exact BTEmb.left (ih es et.1 ps fun x hx => pt x (by simp [BT.leaves, hx]))
  | right _ ih =>
    intro s t es et ps pt
    cases t with
    | leaf _ => simp [BT.map] at et
    | node u1 u2 =>
    simp only [BT.map, BT.node.injEq] at et
    exact BTEmb.right (ih es et.2 ps fun x hx => pt x (by simp [BT.leaves, hx]))
  | node _ _ ih1 ih2 =>
    intro s t es et ps pt
    cases s with
    | leaf _ => simp [BT.map] at es
    | node v1 v2 =>
    cases t with
    | leaf _ => simp [BT.map] at et
    | node u1 u2 =>
    simp only [BT.map, BT.node.injEq] at es et
    exact BTEmb.node (ih1 es.1 et.1 (fun x hx => ps x (by simp [BT.leaves, hx]))
        (fun x hx => pt x (by simp [BT.leaves, hx])))
      (ih2 es.2 et.2 (fun x hx => ps x (by simp [BT.leaves, hx])) (fun x hx => pt x (by simp [BT.leaves, hx])))

open Compiler in
/-- **No infinite sequence of pushes that stay on the stack, for `+he-sock`**:
`noStackSeq_of_kruskal` with `he = heSock`, the tree view `capeBT`, and as
hypotheses only that the formulas are among `Fs` and that the subjects are
shaped socks whose leaves (atom capes with their data) are among `Ls`. -/
theorem noStackSeq_heSock (hK : KruskalBT) (th : Nat) (Fs : List Noun) (Ls : List Sock) :
    ¬ ∃ (w : Nat → Ident) (S : Nat → List Ident),
      (∀ n, (w n).2 ∈ Fs) ∧
      (∀ n, ∃ c d, (w n).1 = Sock.mk c d ∧ Shaped c d ∧ ∀ a ∈ BT.leaves (capeBT c d), a ∈ Ls) ∧
      (∀ i j, i < j → w i ≠ w j) ∧ (∀ i j, i < j → w i ∈ S j) ∧
      (∀ j, th ≤ ((S j).filter (fun i => i.2 = (w j).2)).length →
        ∀ x ∈ S j, x.2 = (w j).2 → heSock (w j).1 x.1 = false) := by
  rintro ⟨w, S, hFs, hsh, hinj, hstk, hguard⟩
  have hne : Ls ≠ [] := by
    obtain ⟨c, d, _, _, hl⟩ := hsh 0
    intro e
    have : ∀ t : BT Sock, BT.leaves t ≠ [] := by
      intro t; induction t with
      | leaf _ => simp [BT.leaves]
      | node _ _ ih _ => simp [BT.leaves, ih]
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (this (capeBT c d))
    have := hl a ha
    rw [e] at this
    exact absurd this List.not_mem_nil
  obtain ⟨d0, hd0⟩ := List.exists_mem_of_ne_nil _ hne
  let L := { a : Sock // a ∈ Ls }
  let toL : Sock → L := fun a => if h : a ∈ Ls then ⟨a, h⟩ else ⟨d0, hd0⟩
  have hinjL : ∀ x y, x ∈ Ls → y ∈ Ls → toL x = toL y → x = y := by
    intro x y hx hy e
    simp only [toL, dif_pos hx, dif_pos hy] at e
    exact congrArg Subtype.val e
  let tree : Ident → BT Sock := fun i => match i.1 with
    | Sock.mk c d => capeBT c d
    | Sock.void => BT.leaf Sock.void
  let ls : List L := Ls.attach
  have hls : ∀ a : L, a ∈ ls := fun a => List.mem_attach Ls a
  obtain ⟨F, hF⟩ := pigeon_inf Fs (fun n => (w n).2) hFs
  obtain ⟨s, hs, hsF⟩ := subseq_of_inf hF
  obtain ⟨i, j, hij, hb⟩ := hK L ls hls (fun n => BT.map toL (tree (w (s (th + n)))))
  have hlt : s (th + i) < s (th + j) := strictMono_le hs (by omega)
  obtain ⟨ci, di, ei, shi, li⟩ := hsh (s (th + i))
  obtain ⟨cj, dj, ej, shj, lj⟩ := hsh (s (th + j))
  have ti : tree (w (s (th + i))) = capeBT ci di := by simp only [tree, ei]
  have tj : tree (w (s (th + j))) = capeBT cj dj := by simp only [tree, ej]
  have hb' : BTEmb (capeBT ci di) (capeBT cj dj) :=
    btEmb_of_map (P := fun a => a ∈ Ls) hinjL hb (by rw [ti]) (by rw [tj]) li lj
  have hhe := heSock_of_btEmb hb' shi shj rfl rfl
  have hcount : th ≤ ((S (s (th + j))).filter (fun x => x.2 = (w (s (th + j))).2)).length := by
    rw [hsF (th + j)]
    exact Nat.le_trans (Nat.le_add_right th j)
      (count_ge_of_seq hs hinj hsF _ (th + j) fun k hk => hstk _ _ (strictMono_le hs hk))
  have hfalse := hguard (s (th + j)) hcount (w (s (th + i))) (hstk _ _ hlt)
    (by rw [hsF (th + i), hsF (th + j)])
  rw [ei, ej, hhe] at hfalse
  cases hfalse

end Ana
end SkaModel
end Formalization
