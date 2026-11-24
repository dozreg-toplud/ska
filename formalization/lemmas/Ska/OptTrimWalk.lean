import lemmas.Ska.OptTrim

/-!
# `+trim-trace-hints`: the walk over `topo`

**`trimWalk_safe`**: on a `topo` with `TopoOK`, a `rev` that lists every
member of `topo` jumping to a block (the second half of `TopoInv`), and
bracketed hints (`TrimBr`), the unsafe keys the walk returns meet `SafeAt`
at every reachable block: at an op that may crash, every key with a frame on
the bracketed stack is unsafe, and at an end that is not `%clq`, `%eqq`,
`%brz`, `%hop`, so is every key with a frame on the stack at the end.

The invariant over the prefix `pre` of `topo` already walked (`WInv`):
every reachable `p` of `pre` has counts `c` in `out` that cover the stack at
its end (`CntLe`), and `SafeAt` holds of it for the current unsafe keys,
which only grow.  At the next label `o`, if `o` is `0` its stack is empty
(`cntLe_nil`), and otherwise `Reach` gives a reachable predecessor `p`,
which `TopoOK` with `Nodup` puts in `pre` (`mem_pre_of_jump`) and `rev`
lists, so the `max` join covers its stack, which is `K o` by `TrimBr`
(`trimOpen_cntLe`).  Then `trimBody_open` and `trimBody_crash` give the
facts of `o`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-- What the simulation needs of the unsafe keys at a block: every key with
a frame on the bracketed stack is unsafe at an op that may crash, and at an
end that is not quiet. -/
def SafeAt (K : Nat → List (Option TKey)) (uns : Uns) (o : Nat) (b : Blob) : Prop :=
  (∀ pre op post gm, b.body = pre ++ op :: post → brBody (K o) pre = some gm → traceKey op = none →
    notCrashing op = false → ∀ k, some k ∈ gm → uns k = true) ∧
  (finQuiet b.fin = false → ∀ g, brBody (K o) b.body = some g → ∀ k, some k ∈ g → uns k = true)

/-- `SafeAt` at every reachable block. -/
def TrimSafe (bl : Map Blob) (K : Nat → List (Option TKey)) (uns : Uns) : Prop :=
  ∀ o b, Reach bl o → HoonMap.get bl o = some b → SafeAt K uns o b

theorem SafeAt.mono {K : Nat → List (Option TKey)} {u u' : Uns} {o : Nat} {b : Blob} (h : SafeAt K u o b)
    (hu : ∀ k, u k = true → u' k = true) : SafeAt K u' o b :=
  ⟨fun pre op post gm hb hg he hc k hk => hu k (h.1 pre op post gm hb hg he hc k hk),
    fun hq g hg k hk => hu k (h.2 hq g hg k hk)⟩

/-- The invariant of the walk over the prefix `pre` already walked. -/
def WInv (bl : Map Blob) (K : Nat → List (Option TKey)) (pre : List Nat) (out : Map Cnt) (uns : Uns) : Prop :=
  ∀ p ∈ pre, Reach bl p → ∀ b, HoonMap.get bl p = some b →
    ∃ c g, HoonMap.get out p = some c ∧ brBody (K p) b.body = some g ∧ CntLe g c ∧ SafeAt K uns p b

theorem brBody_det {g : List (Option TKey)} {l : List Pole} {a b : List (Option TKey)}
    (ha : brBody g l = some a) (hb : brBody g l = some b) : a = b := by
  rw [ha] at hb; exact Option.some.inj hb

theorem idxOf_cons_ne' {a b : Nat} {l : List Nat} (h : a ≠ b) : (a :: l).idxOf b = l.idxOf b + 1 := by
  rw [List.idxOf_cons]; have : (a == b) = false := by simpa using h
  rw [this]; rfl

theorem idxOf_pre {pre l : List Nat} {o : Nat} (ho : o ∉ pre) : (pre ++ o :: l).idxOf o = pre.length := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
    have hne : a ≠ o := fun e => ho (e ▸ List.mem_cons_self)
    have ho' : o ∉ pre := fun h => ho (List.mem_cons_of_mem _ h)
    rw [List.cons_append, idxOf_cons_ne' hne, ih ho']
    rfl

theorem mem_pre_of_idx {pre l : List Nat} {p : Nat} (hp : (pre ++ l).idxOf p < pre.length) : p ∈ pre := by
  induction pre with
  | nil => simp at hp
  | cons a pre ih =>
    by_cases e : a = p
    · subst e; exact List.mem_cons_self
    · rw [List.cons_append, idxOf_cons_ne' e] at hp
      exact List.mem_cons_of_mem _ (ih (by simp at hp; omega))

/-- **A reachable predecessor of the next label was walked.** -/
theorem mem_pre_of_jump {bl : Map Blob} {pre l : List Nat} {o p : Nat} {b : Blob} {j : Jmp}
    (ht : TopoOK bl (pre ++ o :: l)) (hp : Reach bl p) (hb : HoonMap.get bl p = some b) (hj : j ∈ getJmps b.fin)
    (he : j.there = o) : p ∈ pre := by
  obtain ⟨hnd, -, -, hr, hf⟩ := ht
  have hpm := hr p hp
  have hl : (pre ++ o :: l).idxOf p < (pre ++ o :: l).length := List.idxOf_lt_length_of_mem hpm
  have hx : (pre ++ o :: l)[(pre ++ o :: l).idxOf p]? = some p := by
    rw [List.getElem?_eq_getElem hl, List.getElem_idxOf hl]
  obtain ⟨k, hk, hk'⟩ := hf _ p b j hx hb hj
  obtain ⟨hkl, hkv⟩ := List.getElem?_eq_some_iff.mp hk'
  have hko : (pre ++ o :: l).idxOf j.there = k := by rw [← hkv, hnd.idxOf_getElem k hkl]
  rw [he] at hko
  have hop : o ∉ pre := fun h => by
    have := (List.nodup_append.mp hnd).2.2 o h o List.mem_cons_self
    exact this rfl
  rw [idxOf_pre hop] at hko
  exact mem_pre_of_idx (l := o :: l) (by omega)

theorem walk_step_safe {K : Nat → List (Option TKey)} {o : Nat} {b : Blob} {opn : Cnt} {uns : Uns}
    {g : List (Option TKey)} (hg : brBody (K o) b.body = some g) (ho : CntLe (K o) opn) :
    CntLe g (trimBody b.body opn uns).1 ∧
      SafeAt K (if finQuiet b.fin then (trimBody b.body opn uns).2
        else (trimBody b.body opn uns).2.add (trimBody b.body opn uns).1) o b := by
  have hle := trimBody_open b.body (K o) g opn uns hg ho
  have hsub : ∀ k, (trimBody b.body opn uns).2 k = true →
      (if finQuiet b.fin then (trimBody b.body opn uns).2
        else (trimBody b.body opn uns).2.add (trimBody b.body opn uns).1) k = true := by
    intro k hk; split
    · exact hk
    · simp [Uns.add, hk]
  refine ⟨hle, fun pre op post gm hb hgm he hc k hk => hsub k ?_, fun hq g' hg' k hk => ?_⟩
  · have := trimBody_crash pre op post (uns := uns) hgm ho he hc k hk
    rw [← hb] at this; exact this
  · rw [hg] at hg'; cases hg'
    simp only [hq, Bool.false_eq_true, if_false, Uns.add, Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr (hle.pos hk)

/-- **The walk**, from a prefix with the invariant. -/
theorem trimWalk_inv {bl : Map Blob} {rev : Map (List Nat)} {K : Nat → List (Option TKey)} (hbr : TrimBr bl K) :
    ∀ (l pre : List Nat) (out : Map Cnt) (uns uf : Uns), TopoOK bl (pre ++ l) →
    (∀ o b j, o ∈ pre ++ l → HoonMap.get bl o = some b → j ∈ getJmps b.fin → o ∈ getJa rev j.there) →
    WInv bl K pre out uns → trimWalk bl rev l out uns = some uf →
    ∀ p ∈ pre ++ l, Reach bl p → ∀ b, HoonMap.get bl p = some b → SafeAt K uf p b
  | [], pre, out, uns, uf, _, _, hw, h => by
    simp only [trimWalk, Option.some.injEq] at h
    subst h
    intro p hp hr b hb
    obtain ⟨c, g, -, -, -, hs⟩ := hw p (by simpa using hp) hr b hb
    exact hs
  | o :: l, pre, out, uns, uf, ht, hrev, hw, h => by
    simp only [trimWalk, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, h⟩ := h
    have hnd := ht.1
    have hop : o ∉ pre := fun h => (List.nodup_append.mp hnd).2.2 o h o List.mem_cons_self rfl
    have ht' : TopoOK bl ((pre ++ [o]) ++ l) := by rw [List.append_assoc]; exact ht
    have hrev' : ∀ o' b j, o' ∈ (pre ++ [o]) ++ l → HoonMap.get bl o' = some b → j ∈ getJmps b.fin →
        o' ∈ getJa rev j.there := fun o' b j h => hrev o' b j (by rw [List.append_assoc] at h; exact h)
    have hfin := trimWalk_inv hbr l (pre ++ [o]) _ _ uf ht' hrev' ?_ h
    · intro p hp
      exact hfin p (by rw [List.append_assoc]; exact hp)
    intro p hp hr bp hbp
    rcases List.mem_append.mp hp with hp | hp
    · have hpo : p ≠ o := fun e => hop (e ▸ hp)
      obtain ⟨c, g, hc, hg, hle, hs⟩ := hw p hp hr bp hbp
      refine ⟨c, g, by simp [HoonMap.get_put, hpo, hc], hg, hle, hs.mono fun k hk => ?_⟩
      have := trimBody_uns_mono b.body (trimOpen rev out o) uns k hk
      split
      · exact this
      · simp [Uns.add, this]
    · simp only [List.mem_singleton] at hp
      subst hp
      rw [hb] at hbp; cases hbp
      obtain ⟨g, hg, -⟩ := hbr.2 p b hr hb
      have ho : CntLe (K p) (trimOpen rev out p) := by
        cases hr with
        | zero => rw [hbr.1]; exact cntLe_nil _
        | @jump q bq j hq hbq hj =>
          have hqm := mem_pre_of_jump ht hq hbq hj rfl
          obtain ⟨c, gq, hc, hgq, hle, -⟩ := hw q hqm hq bq hbq
          obtain ⟨gq', hgq', hK⟩ := hbr.2 q bq hq hbq
          rw [brBody_det hgq hgq', ← hK j hj] at hle
          exact trimOpen_cntLe (hrev q bq j (List.mem_append_left _ hqm) hbq hj) hc hle
      obtain ⟨hle, hs⟩ := walk_step_safe (uns := uns) hg ho
      exact ⟨_, g, by simp [HoonMap.get_put], hg, hle, hs⟩

/-- **The unsafe keys of the walk meet `SafeAt` at every reachable block.** -/
theorem trimWalk_safe {bl : Map Blob} {rev : Map (List Nat)} {topo : List Nat} {K : Nat → List (Option TKey)}
    {uf : Uns} (hbr : TrimBr bl K) (ht : TopoOK bl topo)
    (hrev : ∀ o b j, o ∈ topo → HoonMap.get bl o = some b → j ∈ getJmps b.fin → o ∈ getJa rev j.there)
    (h : trimWalk bl rev topo HoonMap.empty (fun _ => false) = some uf) : TrimSafe bl K uf :=
  fun o b hr hb => trimWalk_inv hbr topo [] _ _ uf ht hrev (fun _ h => absurd h List.not_mem_nil) h o
    (ht.2.2.2.1 o hr) hr b hb

end Opt
end SkaModel
end Formalization
