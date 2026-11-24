import lemmas.Ska.OptAliasSSAHops

/-!
# `+remove-hops` keeps `DefOnceB`

**`hk_once`**: after `+remove-hops`, every register still has at most one
definition that counts.  A block reachable after is the merge of a chain of
blocks before (`HkMem o x`: `x` is reached from `o` by hops each into a block
whose only predecessor in `rev` is the block before it, `HkMerges`).

* Each place of a merged body goes to one definition before (`HkSites`, the
  map `f`, built by induction on `MTail` in `hk_sites`): an op of the chain
  member `x` at `j` to `(x, some j)`, a move into a parameter of `x` to
  `(x, none)`.  For a fixed register the map is injective (`HkSites.inj`: the
  moves of one hop write distinct parameters, `ParNodup`, and the chain has
  no repeated member, the rank of `Acyclic` falling along it), and never gives
  `(o, none)`, the place of the merged block's own parameters.
* The chains of two blocks reachable after are disjoint (`hk_disj`): a block
  reachable after has no predecessor before that merges it (`hk_no_merged`),
  since the block jumping to it after ends its chain with `stop`, and `rev`
  lists the jumping block as the only predecessor.
* A dead fill before at `(x, j)` is one after at the place `f` maps to it
  (`hk_live`): `x` ends in `%bom`, so it ends its chain and its suffix from
  `j` is the suffix of the merged body (`HkSites.fill`), and a read after is a
  read before in the chain (`HkSites.read`), at an earlier place when it is
  in `x` before `j`.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSectionVars false

/-- `x` is merged into `p`: `p` ends in a hop to `x`, and `p` is the only
predecessor of `x` in `rev`. -/
def HkMerges (bl : Map Blob) (rev : Map (List Nat)) (p x : Nat) : Prop :=
  ∃ bp t, HoonMap.get bl p = some bp ∧ bp.fin = Termin.hop t ∧ t.there = x ∧ getJa rev x = [p]

/-- A member of the chain merged at `o`. -/
inductive HkMem (bl : Map Blob) (rev : Map (List Nat)) (o : Nat) : Nat → Prop
  | refl : HkMem bl rev o o
  | step {p x : Nat} : HkMem bl rev o p → HkMerges bl rev p x → HkMem bl rev o x

section
variable {bl : Map Blob} {rev : Map (List Nat)}

theorem hk_mem_trans {o p x : Nat} (h1 : HkMem bl rev o p) (h2 : HkMem bl rev p x) : HkMem bl rev o x := by
  induction h2 with
  | refl => exact h1
  | step _ hm ih => exact HkMem.step ih hm

theorem hk_mem_rank {ρ : Nat → Nat}
    (hρ : ∀ o b j, HoonMap.get bl o = some b → j ∈ getJmps b.fin → ρ j.there < ρ o)
    {o x : Nat} (h : HkMem bl rev o x) : ρ x ≤ ρ o := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ hm ih =>
    obtain ⟨bp, t, hbp, hf, rfl, -⟩ := hm
    have := hρ _ bp t hbp (by rw [hf]; simp [getJmps])
    omega

theorem hk_mem_reach {o x : Nat} (h : HkMem bl rev o x) (ho : Reach bl o) : Reach bl x := by
  induction h with
  | refl => exact ho
  | step _ hm ih =>
    obtain ⟨bp, t, hbp, hf, rfl, -⟩ := hm
    exact Reach.jump (j := t) ih hbp (by rw [hf]; simp [getJmps])

theorem hk_reach_rank {ρ : Nat → Nat}
    (hρ : ∀ o b j, HoonMap.get bl o = some b → j ∈ getJmps b.fin → ρ j.there < ρ o)
    {o : Nat} (h : Reach bl o) : ρ o ≤ ρ 0 := by
  induction h with
  | zero => exact Nat.le_refl _
  | jump _ hb hj ih => have := hρ _ _ _ hb hj; omega

/-- The end of a merged chain is the end of a member that stops it. -/
theorem hk_mt_end {o : Nat} {b : Blob} {T : List Pole} {F : Termin} (hm : MTail bl rev o b T F) :
    HoonMap.get bl o = some b → ∃ e be, HkMem bl rev o e ∧ HoonMap.get bl e = some be ∧ F = be.fin ∧
      ∀ t, be.fin = Termin.hop t → getJa rev t.there ≠ [e] := by
  induction hm with
  | @stop o b hs => intro hb; exact ⟨o, b, HkMem.refl, hb, rfl, hs⟩
  | @link o b t b1 ops T F hfin hpre hb1 _ _ ih =>
    intro hb
    obtain ⟨e, be, hme, hbe, hF, hs⟩ := ih hb1
    exact ⟨e, be, hk_mem_trans (HkMem.step HkMem.refl ⟨b, t, hb, hfin, rfl, hpre⟩) hme, hbe, hF, hs⟩

variable {bl' : Map Blob} {topo : List Nat}

/-- A block reachable after `+remove-hops` is reachable before. -/
theorem hk_reach_back (hB : HopsBlocks bl rev topo bl') {o : Nat} (h : Reach bl' o) : Reach bl o := by
  induction h with
  | zero => exact Reach.zero
  | @jump y m j _ hm hj ih =>
    obtain ⟨b, T, F, hb, hmt, rfl⟩ := hB.back y m hm
    obtain ⟨e, be, hme, hbe, hF, -⟩ := hk_mt_end hmt hb
    exact Reach.jump (j := j) (hk_mem_reach hme ih) hbe (by rw [← hF]; exact hj)

/-- **A block reachable after is merged into no block reachable before.** -/
theorem hk_no_merged (hB : HopsBlocks bl rev topo bl') (hT : TopoInv bl topo rev) (hA : Acyclic bl)
    {x p : Nat} (hx : Reach bl' x) (hm : HkMerges bl rev p x) (hp : Reach bl p) : False := by
  obtain ⟨bp, t, hbp, hf, hx', hpre⟩ := hm
  cases hx with
  | zero =>
    obtain ⟨ρ, hρ⟩ := hA
    have h1 := hρ p bp t hbp (by rw [hf]; simp [getJmps])
    rw [hx'] at h1
    have := hk_reach_rank hρ hp
    omega
  | @jump y m j hy hmy hj =>
    obtain ⟨b, T, F, hb, hmt, rfl⟩ := hB.back y m hmy
    obtain ⟨e, be, hme, hbe, hF, hs⟩ := hk_mt_end hmt hb
    have he : Reach bl e := hk_mem_reach hme (hk_reach_back hB hy)
    have hj' : j ∈ getJmps be.fin := by rw [← hF]; exact hj
    have hin := hT.2 e be j (hT.1.2.2.2.1 e he) hbe hj'
    rw [hpre] at hin
    have hep : e = p := List.mem_singleton.mp hin
    subst hep
    rw [hbe] at hbp; cases hbp
    exact hs t hf (by rw [hx']; exact hpre)

/-- **The chains of two blocks reachable after are disjoint.** -/
theorem hk_disj (hB : HopsBlocks bl rev topo bl') (hT : TopoInv bl topo rev) (hA : Acyclic bl)
    {o o' x : Nat} (ho : Reach bl' o) (ho' : Reach bl' o')
    (h : HkMem bl rev o x) (h' : HkMem bl rev o' x) : o = o' := by
  have hob := hk_reach_back hB ho
  have hob' := hk_reach_back hB ho'
  revert h'
  induction h with
  | refl =>
    intro h'
    cases h' with
    | refl => rfl
    | step hp hm => exact (hk_no_merged hB hT hA ho hm (hk_mem_reach hp hob')).elim
  | @step p x hp hm ih =>
    intro h'
    cases h' with
    | refl => exact (hk_no_merged hB hT hA ho' hm (hk_mem_reach hp hob)).elim
    | @step p' _ hp' hm' =>
      have e : p = p' := by
        obtain ⟨_, _, _, _, _, e1⟩ := hm
        obtain ⟨_, _, _, _, _, e2⟩ := hm'
        rw [e1] at e2
        exact (List.cons.inj e2).1
      subst e
      exact ih hp'

end

/-! ## The places of a merged body -/

theorem hk_nodup_idx {α : Type} : ∀ (l : List α) (a a' : Nat) (v : α), l.Nodup → l[a]? = some v →
    l[a']? = some v → a = a'
  | [], _, _, _, _, h, _ => by simp at h
  | x :: l, a, a', v, hn, h, h' => by
    have hn' := List.nodup_cons.mp hn
    cases a with
    | zero =>
      cases a' with
      | zero => rfl
      | succ a' =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at h h'
        subst h
        exact absurd (List.mem_of_getElem? h') hn'.1
    | succ a =>
      cases a' with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at h h'
        subst h'
        exact absurd (List.mem_of_getElem? h) hn'.1
      | succ a' =>
        simp only [List.getElem?_cons_succ] at h h'
        rw [hk_nodup_idx l a a' v hn'.2 h h']

theorem hk_argOp_dst (x : Option Nat × Nat) : aliasDst (argOp x) = some x.2 := by
  obtain ⟨a, p⟩ := x; cases a <;> rfl

/-- Two moves of one hop that write the same register are the same move. -/
theorem hk_seg_inj {as : List (Option Nat)} {ps : List Nat} {ops : List Pole}
    (h : hopSeg as ps [] = some ops) (hn : ps.Nodup) {a a' : Nat} {op op' : Pole} {r : Nat}
    (ha : ops[a]? = some op) (ha' : ops[a']? = some op') (hd : aliasDst op = some r)
    (hd' : aliasDst op' = some r) : a = a' := by
  rw [hopSeg_eq] at h
  split at h
  · rename_i hlen
    simp only [List.append_nil, Option.some.injEq] at h
    subst h
    have e : ((as.zip ps).reverse.map argOp).map aliasDst = (((as.zip ps).map Prod.snd).reverse).map some := by
      simp only [List.map_map, List.map_reverse]
      congr 1
      apply List.map_congr_left
      intro x _
      exact hk_argOp_dst x
    have hnd : ((((as.zip ps).map Prod.snd).reverse).map some).Nodup := by
      have hr : ps.reverse.Nodup := List.pairwise_reverse.mpr (hn.imp fun h e => h e.symm)
      rw [List.map_snd_zip (by omega)]
      exact List.Pairwise.map some (fun _ _ h e => h (Option.some.inj e)) hr
    rw [← e] at hnd
    refine hk_nodup_idx _ a a' (some r) hnd ?_ ?_
    · rw [List.getElem?_map, ha]; simp [hd]
    · rw [List.getElem?_map, ha']; simp [hd']
  · cases h

/-- The definition before of each place of the body of `merge b T F`. -/
structure HkSites (bl : Map Blob) (rev : Map (List Nat)) (o : Nat) (b : Blob) (T : List Pole) (F : Termin)
    (f : Nat → Nat × Option Nat) : Prop where
  mem : ∀ k, k < (b.body ++ T).length → HkMem bl rev o (f k).1 ∧ f k ≠ (o, none)
  op : ∀ k x j, k < (b.body ++ T).length → f k = (x, some j) →
    ∃ bx, HoonMap.get bl x = some bx ∧ bx.body[j]? = (b.body ++ T)[k]?
  par : ∀ k x op r, f k = (x, none) → (b.body ++ T)[k]? = some op → aliasDst op = some r →
    ∃ bx, HoonMap.get bl x = some bx ∧ r ∈ bx.par
  inj : ∀ k k' op op' r, (b.body ++ T)[k]? = some op → (b.body ++ T)[k']? = some op' →
    aliasDst op = some r → aliasDst op' = some r → f k = f k' → k = k'
  fill : ∀ k x j bx u, k < (b.body ++ T).length → f k = (x, some j) → HoonMap.get bl x = some bx →
    bx.fin = Termin.bom u → F = Termin.bom u ∧ (b.body ++ T).drop k = bx.body.drop j
  read : ∀ i r, ReadAt (merge b T F) i r → ∃ y byy i', HkMem bl rev o y ∧ HoonMap.get bl y = some byy ∧
    ReadAt byy i' r ∧ ∀ k x j, k < (b.body ++ T).length → f k = (x, some j) → x = y → i' < j → i < k

theorem hk_get3 {A B C : List Pole} {k : Nat} :
    (k < A.length → (A ++ (B ++ C))[k]? = A[k]?) ∧
    (A.length ≤ k → k < A.length + B.length → (A ++ (B ++ C))[k]? = B[k - A.length]?) ∧
    (A.length + B.length ≤ k → (A ++ (B ++ C))[k]? = C[k - (A.length + B.length)]?) := by
  refine ⟨fun h => List.getElem?_append_left h, fun h1 h2 => ?_, fun h => ?_⟩
  · rw [List.getElem?_append_right h1, List.getElem?_append_left (by omega)]
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    congr 1; omega

theorem hk_drop3 {A B C : List Pole} {k : Nat} (h : A.length + B.length ≤ k) :
    (A ++ (B ++ C)).drop k = C.drop (k - (A.length + B.length)) := by
  obtain ⟨d, rfl⟩ : ∃ d, k = A.length + (B.length + d) := ⟨k - (A.length + B.length), by omega⟩
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, List.drop_append,
    List.drop_eq_nil_of_le (by omega), List.nil_append]
  congr 1; omega

section
variable {bl : Map Blob} {rev : Map (List Nat)}

/-- **The places of a merged body go to definitions before** (`HkSites`). -/
theorem hk_sites {ρ : Nat → Nat}
    (hρ : ∀ o b j, HoonMap.get bl o = some b → j ∈ getJmps b.fin → ρ j.there < ρ o)
    (hpn : ParNodup bl) {o : Nat} {b : Blob} {T : List Pole} {F : Termin} (hm : MTail bl rev o b T F) :
    HoonMap.get bl o = some b → ∃ f, HkSites bl rev o b T F f := by
  induction hm with
  | @stop o b hs =>
    intro hb
    have e : merge b [] b.fin = b := by simp [merge]
    refine ⟨fun k => (o, some k), ⟨fun k _ => ⟨HkMem.refl, by simp⟩, fun k x j _ hk => ?_,
      fun k x op r hk => by simp at hk, fun k k' _ _ _ _ _ _ _ hk => by simpa using hk,
      fun k x j bx u _ hk hbx hu => ?_, fun i r hr => ?_⟩⟩
    · simp only [Prod.mk.injEq, Option.some.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact ⟨b, hb, by rw [List.append_nil]⟩
    · simp only [Prod.mk.injEq, Option.some.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rw [hb] at hbx; cases hbx
      exact ⟨hu, by rw [List.append_nil]⟩
    · rw [e] at hr
      refine ⟨o, b, i, HkMem.refl, hb, hr, fun k x j _ hk _ hij => ?_⟩
      simp only [Prod.mk.injEq, Option.some.injEq] at hk
      omega
  | @link o b t b1 ops T1 F hfin hpre hb1 hseg _ ih =>
    intro hb
    obtain ⟨f1, H1⟩ := ih hb1
    have hmo : HkMem bl rev o t.there := HkMem.step HkMem.refl ⟨b, t, hb, hfin, rfl, hpre⟩
    have hrk : ρ t.there < ρ o := hρ o b t hb (by rw [hfin]; simp [getJmps])
    have hno : ∀ z, HkMem bl rev t.there z → z ≠ o := fun z hz e => by
      have := hk_mem_rank hρ hz; rw [e] at this; omega
    have hne : t.there ≠ o := hno _ HkMem.refl
    generalize hL : b.body.length = L
    generalize hM : ops.length = M
    have hT : b.body ++ (ops ++ b1.body ++ T1) = b.body ++ (ops ++ (b1.body ++ T1)) := by
      rw [List.append_assoc]
    have hlen : (b.body ++ (ops ++ b1.body ++ T1)).length = L + M + (b1.body ++ T1).length := by
      simp only [List.length_append]; omega
    have g1 : ∀ k, k < L → (b.body ++ (ops ++ b1.body ++ T1))[k]? = b.body[k]? := fun k h => by
      rw [hT]; exact (hk_get3 (A := b.body) (B := ops) (C := b1.body ++ T1)).1 (by omega)
    have g2 : ∀ k, L ≤ k → k < L + M → (b.body ++ (ops ++ b1.body ++ T1))[k]? = ops[k - L]? := fun k h h' => by
      rw [hT, ← hL]; exact (hk_get3 (A := b.body) (B := ops) (C := b1.body ++ T1)).2.1 (by omega) (by omega)
    have g3 : ∀ k, L + M ≤ k → (b.body ++ (ops ++ b1.body ++ T1))[k]? = (b1.body ++ T1)[k - (L + M)]? :=
      fun k h => by
        rw [hT, ← hL, ← hM]; exact (hk_get3 (A := b.body) (B := ops) (C := b1.body ++ T1)).2.2 (by omega)
    have hopsd : ∀ a op, ops[a]? = some op → ∃ d, aliasDst op = some d ∧ d ∈ b1.par := fun a op h => by
      rcases ssk_seg_ops _ _ _ _ hseg op (List.mem_of_getElem? h) with h' | ⟨-, h'⟩
      · cases h'
      · have e : ∃ d, aliasDst op = some d := by
          rw [hopSeg_eq] at hseg; split at hseg
          · simp only [List.append_nil, Option.some.injEq] at hseg; subst hseg
            obtain ⟨x, -, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? h)
            exact ⟨_, hk_argOp_dst x⟩
          · cases hseg
        obtain ⟨d, hd⟩ := e
        exact ⟨d, hd, h' d hd⟩
    let f : Nat → Nat × Option Nat := fun k =>
      if k < L then (o, some k) else if k < L + M then (t.there, none) else f1 (k - (L + M))
    have f1e : ∀ k, k < L → f k = (o, some k) := fun k h => by simp only [f, if_pos h]
    have f2e : ∀ k, L ≤ k → k < L + M → f k = (t.there, none) := fun k h h' => by
      simp only [f, if_neg (show ¬ k < L by omega), if_pos h']
    have f3e : ∀ k, L + M ≤ k → f k = f1 (k - (L + M)) := fun k h => by
      simp only [f, if_neg (show ¬ k < L by omega), if_neg (show ¬ k < L + M by omega)]
    -- the values of `f1` lie in the chain of `t.there`, which does not hold `o`
    have h1o : ∀ k, k < (b1.body ++ T1).length → (f1 k).1 ≠ o := fun k hk => hno _ (H1.mem k hk).1
    have hcase : ∀ k : Nat, k < L ∨ (L ≤ k ∧ k < L + M) ∨ L + M ≤ k := fun k => by omega
    refine ⟨f, ⟨fun k hk => ?_, fun k x j hk hf => ?_, fun k x op r hf hop hd => ?_,
      fun k k' op op' r hop hop' hd hd' hf => ?_, fun k x j bx u hk hf hbx hu => ?_, fun i r hr => ?_⟩⟩
    · -- mem
      rw [hlen] at hk
      rcases hcase k with h | ⟨h, h'⟩ | h
      · rw [f1e k h]; exact ⟨HkMem.refl, by simp⟩
      · rw [f2e k h h']; exact ⟨hmo, by simp [hne]⟩
      · rw [f3e k h]
        obtain ⟨m1, m2⟩ := H1.mem (k - (L + M)) (by omega)
        refine ⟨hk_mem_trans hmo m1, fun e => h1o (k - (L + M)) (by omega) (by rw [e])⟩
    · -- op
      rw [hlen] at hk
      rcases hcase k with h | ⟨h, h'⟩ | h
      · rw [f1e k h] at hf
        simp only [Prod.mk.injEq, Option.some.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        exact ⟨b, hb, (g1 _ h).symm⟩
      · rw [f2e k h h'] at hf; simp at hf
      · rw [f3e k h] at hf
        obtain ⟨bx, hbx, e⟩ := H1.op _ x j (by omega) hf
        exact ⟨bx, hbx, by rw [g3 k h]; exact e⟩
    · -- par
      have hk : k < L + M + (b1.body ++ T1).length := by
        rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hop).1
      rcases hcase k with h | ⟨h, h'⟩ | h
      · rw [f1e k h] at hf; simp at hf
      · rw [f2e k h h'] at hf
        simp only [Prod.mk.injEq] at hf
        obtain ⟨rfl, -⟩ := hf
        rw [g2 k h h'] at hop
        obtain ⟨d, hd2, hdp⟩ := hopsd _ op hop
        rw [hd] at hd2; cases hd2
        exact ⟨b1, hb1, hdp⟩
      · rw [f3e k h] at hf
        rw [g3 k h] at hop
        exact H1.par _ x op r hf hop hd
    · -- inj
      have hk : k < L + M + (b1.body ++ T1).length := by
        rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hop).1
      have hk' : k' < L + M + (b1.body ++ T1).length := by
        rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hop').1
      rcases hcase k with h | ⟨h, h'⟩ | h <;> rcases hcase k' with g | ⟨g, g'⟩ | g
      · rw [f1e k h, f1e k' g] at hf; simpa using hf
      · rw [f1e k h, f2e k' g g'] at hf; simp at hf
      · rw [f1e k h, f3e k' g] at hf
        exact absurd (by rw [← hf]) (h1o (k' - (L + M)) (by omega))
      · rw [f2e k h h', f1e k' g] at hf; simp at hf
      · rw [g2 k h h'] at hop; rw [g2 k' g g'] at hop'
        have := hk_seg_inj hseg (hpn _ _ hb1) hop hop' hd hd'
        omega
      · rw [f2e k h h', f3e k' g] at hf
        exact absurd hf.symm ((H1.mem (k' - (L + M)) (by omega)).2)
      · rw [f3e k h, f1e k' g] at hf
        exact absurd (by rw [hf]) (h1o (k - (L + M)) (by omega))
      · rw [f3e k h, f2e k' g g'] at hf
        exact absurd hf ((H1.mem (k - (L + M)) (by omega)).2)
      · rw [f3e k h, f3e k' g] at hf
        rw [g3 k h] at hop; rw [g3 k' g] at hop'
        have := H1.inj _ _ op op' r hop hop' hd hd' hf
        omega
    · -- fill
      rw [hlen] at hk
      rcases hcase k with h | ⟨h, h'⟩ | h
      · rw [f1e k h] at hf
        simp only [Prod.mk.injEq, Option.some.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        rw [hb] at hbx; cases hbx
        rw [hfin] at hu; cases hu
      · rw [f2e k h h'] at hf; simp at hf
      · rw [f3e k h] at hf
        obtain ⟨hF, hd⟩ := H1.fill _ x j bx u (by omega) hf hbx hu
        refine ⟨hF, ?_⟩
        rw [hT, hk_drop3 (by rw [hL, hM]; exact h), hL, hM]; exact hd
    · -- read
      have hfo : ∀ k x j, k < (b.body ++ (ops ++ b1.body ++ T1)).length → f k = (x, some j) → x = o → k < L ∧ j = k :=
        fun k x j hk hf hx => by
          rw [hlen] at hk
          rcases hcase k with h | ⟨h, h'⟩ | h
          · rw [f1e k h] at hf
            simp only [Prod.mk.injEq, Option.some.injEq] at hf
            exact ⟨h, hf.2.symm⟩
          · rw [f2e k h h'] at hf; simp at hf
          · rw [f3e k h] at hf
            exact absurd (by rw [hf, hx]) (h1o (k - (L + M)) (by omega))
      rcases ssk_readAt_app (A := b.body) (B := ops ++ b1.body ++ T1) hr with ⟨hi, hrd⟩ | ⟨hi, hrd⟩
      · refine ⟨o, b, i, HkMem.refl, hb, Or.inl hrd, fun k x j hk hf hx hij => ?_⟩
        obtain ⟨-, rfl⟩ := hfo k x j hk hf hx
        exact hij
      · rw [List.append_assoc] at hrd
        rcases ssk_readAt_app (A := ops) (B := b1.body ++ T1) hrd with ⟨hi2, hrd2⟩ | ⟨hi2, hrd2⟩
        · obtain ⟨op, hop, hrop⟩ := ssk_read_op hrd2
          rcases ssk_seg_ops t.args b1.par [] ops hseg op hop with h | ⟨h, -⟩
          · cases h
          · have hend : ReadAt b b.body.length r :=
              Or.inr ⟨rfl, by rw [hfin]; exact mem_jmpRegs.mpr (h r hrop)⟩
            refine ⟨o, b, _, HkMem.refl, hb, hend, fun k x j hk hf hx hij => ?_⟩
            obtain ⟨h1, rfl⟩ := hfo k x j hk hf hx
            omega
        · obtain ⟨y, byy, i', hmy, hby, hry, hc⟩ := H1.read _ r hrd2
          refine ⟨y, byy, i', hk_mem_trans hmo hmy, hby, hry, fun k x j hk hf hx hij => ?_⟩
          rw [hlen] at hk
          rcases hcase k with h | ⟨h, h'⟩ | h
          · rw [f1e k h] at hf
            simp only [Prod.mk.injEq, Option.some.injEq] at hf
            obtain ⟨rfl, -⟩ := hf
            exact absurd hx.symm (hno _ hmy)
          · rw [f2e k h h'] at hf; simp at hf
          · rw [f3e k h] at hf
            have := hc _ x j (by omega) hf hx hij
            rw [hL] at hi; rw [hM] at hi2
            omega

end

/-! ## `DefOnceB` after the pass -/

/-- The definition before of a place `(o, opt)` of a merged block. -/
def hkSig (f : Nat → Nat × Option Nat) (o : Nat) : Option Nat → Nat × Option Nat
  | none => (o, none)
  | some k => f k

section
variable {bl bl' : Map Blob} {rev : Map (List Nat)} {topo : List Nat}

/-- A definition after that counts goes to one before that counts, in the
chain of its block. -/
theorem hk_live (hB : HopsBlocks bl rev topo bl') (hT : TopoInv bl topo rev) (hA : Acyclic bl)
    (hsites : ∀ o m, HoonMap.get bl' o = some m →
      ∃ b T F f, HoonMap.get bl o = some b ∧ m = merge b T F ∧ HkSites bl rev o b T F f)
    {o : Nat} {b : Blob} {T : List Pole} {F : Termin} {f : Nat → Nat × Option Nat}
    (hbo : HoonMap.get bl o = some b) (hmo : HoonMap.get bl' o = some (merge b T F))
    (hS : HkSites bl rev o b T F f) {r : Nat} {opt : Option Nat} (hl : LiveDef bl' r (o, opt)) :
    LiveDef bl r (hkSig f o opt) ∧ HkMem bl rev o (hkSig f o opt).1 := by
  obtain ⟨ho, hds, hnf⟩ := hl
  have hob : Reach bl o := hk_reach_back hB ho
  cases opt with
  | none =>
    obtain ⟨m, hm, hr⟩ := hds
    rw [hmo] at hm; cases hm
    exact ⟨⟨hob, ⟨b, hbo, hr⟩, fun i h => by cases h⟩, HkMem.refl⟩
  | some k =>
    obtain ⟨m, op, hm, hop, hd⟩ := hds
    rw [hmo] at hm; cases hm
    have hk : k < (b.body ++ T).length := (List.getElem?_eq_some_iff.mp hop).1
    obtain ⟨hmem, -⟩ := hS.mem k hk
    simp only [hkSig]
    refine ⟨⟨hk_mem_reach hmem hob, ?_, ?_⟩, hmem⟩
    · cases e : f k with
      | mk x oj =>
        cases oj with
        | none => exact hS.par k x op r e hop hd
        | some j =>
          obtain ⟨bx, hbx, hj⟩ := hS.op k x j hk e
          exact ⟨bx, op, hbx, by rw [hj]; exact hop, hd⟩
    · intro j hj hDF
      apply hnf k rfl
      revert hj hDF
      cases e : f k with
      | mk x oj =>
        intro hj hDF
        simp only at hj hDF
        subst hj
        obtain ⟨bx, hbx, ⟨u, hbom⟩, ⟨n, himm⟩, hall, hreads⟩ := hDF
        obtain ⟨hF, hdrop⟩ := hS.fill k x j bx u hk e hbx hbom
        have hxo : HkMem bl rev o x := by have := hmem; rw [e] at this; exact this
        refine ⟨merge b T F, hmo, ⟨u, hF⟩, ⟨n, ?_⟩, ?_, ?_⟩
        · show (b.body ++ T)[k]? = _
          rw [← List.head?_drop, hdrop, List.head?_drop, himm]
        · show ∀ op ∈ (b.body ++ T).drop k, _
          rw [hdrop]; exact hall
        · intro o' b'' j' ho' hb'' hrd
          obtain ⟨b2, T2, F2, f2, hb2, rfl, hS2⟩ := hsites o' b'' hb''
          obtain ⟨y, byy, i', hmy, hby, hry, -⟩ := hS2.read j' r hrd
          obtain ⟨rfl, -⟩ := hreads y byy i' (hk_mem_reach hmy (hk_reach_back hB ho')) hby hry
          have hoo := hk_disj hB hT hA ho' ho hmy hxo
          subst hoo
          rw [hmo] at hb''
          rw [← Option.some.inj hb''] at hrd
          obtain ⟨y', byy', i'', hmy', hby', hry', hc⟩ := hS.read j' r hrd
          obtain ⟨rfl, hij⟩ := hreads y' byy' i'' (hk_mem_reach hmy' hob) hby' hry'
          exact ⟨rfl, hc k y' j hk e rfl hij⟩

/-- **`+remove-hops` keeps `DefOnceB`**, on blocks with `Acyclic` and
`ParNodup`, with `TopoInv`. -/
theorem hk_once (hB : HopsBlocks bl rev topo bl') (hT : TopoInv bl topo rev) (hA : Acyclic bl)
    (hpn : ParNodup bl) (h1 : DefOnceB bl) : DefOnceB bl' := by
  obtain ⟨ρ, hρ⟩ := hA
  have hsites : ∀ o m, HoonMap.get bl' o = some m →
      ∃ b T F f, HoonMap.get bl o = some b ∧ m = merge b T F ∧ HkSites bl rev o b T F f := by
    intro o m hm
    obtain ⟨b, T, F, hb, hmt, rfl⟩ := hB.back o m hm
    obtain ⟨f, hf⟩ := hk_sites hρ hpn hmt hb
    exact ⟨b, T, F, f, hb, rfl, hf⟩
  have hA : Acyclic bl := ⟨ρ, hρ⟩
  have blk : ∀ {r o opt}, LiveDef bl' r (o, opt) → ∃ m, HoonMap.get bl' o = some m := by
    intro r o opt h
    cases opt with
    | none => obtain ⟨m, hm, -⟩ := h.2.1; exact ⟨m, hm⟩
    | some k => obtain ⟨m, -, hm, -⟩ := h.2.1; exact ⟨m, hm⟩
  rintro r ⟨o, opt⟩ ⟨o', opt'⟩ hs hs'
  obtain ⟨m, hm⟩ := blk hs
  obtain ⟨m', hm'⟩ := blk hs'
  obtain ⟨b, T, F, f, hb, rfl, hS⟩ := hsites o m hm
  obtain ⟨b', T', F', f', hb', rfl, hS'⟩ := hsites o' m' hm'
  obtain ⟨l1, M1⟩ := hk_live hB hT hA hsites hb hm hS hs
  obtain ⟨l2, M2⟩ := hk_live hB hT hA hsites hb' hm' hS' hs'
  have e := h1 r _ _ l1 l2
  rw [e] at M1
  have hoo : o = o' := hk_disj hB hT hA hs.1 hs'.1 M1 M2
  subst hoo
  obtain ⟨l3, -⟩ := hk_live hB hT hA hsites hb hm hS hs'
  have e2 := h1 r _ _ l1 l3
  have hk : ∀ {k}, LiveDef bl' r (o, some k) → ∃ op, (b.body ++ T)[k]? = some op ∧ aliasDst op = some r := by
    intro k h
    obtain ⟨m2, op, hm2, hop, hd⟩ := h.2.1
    rw [hm] at hm2; cases hm2
    exact ⟨op, hop, hd⟩
  cases opt with
  | none =>
    cases opt' with
    | none => rfl
    | some k' =>
      obtain ⟨op, hop, -⟩ := hk hs'
      exact absurd e2.symm (hS.mem k' (List.getElem?_eq_some_iff.mp hop).1).2
  | some k =>
    cases opt' with
    | none =>
      obtain ⟨op, hop, -⟩ := hk hs
      exact absurd e2 (hS.mem k (List.getElem?_eq_some_iff.mp hop).1).2
    | some k' =>
      obtain ⟨op, hop, hd⟩ := hk hs
      obtain ⟨op', hop', hd'⟩ := hk hs'
      rw [hS.inj k k' op op' r hop hop' hd hd' e2]

end

/-- **`HopsOnce` holds.** -/
theorem hopsOnce_proved {fuel : Nat} : HopsOnce Map fuel :=
  fun _ _ _ _ _ hd hi hs hh =>
    hk_once (hops_blocks hi.1.1 hi.1.2.1 hh) hi hd.1.2.1 hd.1.1.1 hs.1

/-- **`+optimize` keeps the code** on blocks with `DInvS`, given the field
`alias` (`DriverRestSSA`) alone. -/
theorem optimize_keeps_ssaD {fuel sfuel : Nat} {P : Passes Map} (H : DriverRestSSA fuel sfuel P)
    {s s' : Straight Map} (hb : DInvS s.blocks) (h : optimizeF fuel P s = some s') : Keeps s s' :=
  optimize_keeps_ssaO H hopsOnce_proved hb h

end Opt
end SkaModel
end Formalization
