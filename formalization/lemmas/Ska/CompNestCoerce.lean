import lemmas.Ska.CompFinishF

/-!
# `+coerce-lazy` over a whole lazy tree

`entries laz` lists every lazy block of a lazy need with the need taken
there, at any depth, in the order in which `+coerce-lazy` visits them: the
bonds first, each followed by its own entries, then the forks, the yes
branch and its entries before the no branch and its entries.  `+coerce-lazy`
is `+coerce-lazy` of the sure need at the block of the `next` followed by the
same on every entry (`coerceLazyL_flat`).

`coerceSpecK` is `coerceSpec` of `CompTopOK.lean` with one more fact: the
ops change no register allocated before them outside the lazy need's own
(`FillSem`).  With it, `coerceLazyL_spec`: when the labels of the tree are
distinct, every lazy block gets in front of its body ops that fill the
need taken there from registers that hold the subject as the input need
asks, and keep the input registers, and no other block changes.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The entries of a lazy need -/

mutual
/-- Every lazy block of a lazy need with the need taken there, at any
depth, in the order of `+coerce-lazy`. -/
def entries : Lazy S → List (Nat × Lazy S)
  | mk _ f b => bondEntries b ++ forkEntries f

/-- The entries of a list of bonds. -/
def bondEntries : List (Nat × Lazy S) → List (Nat × Lazy S)
  | [] => []
  | (o, l) :: rest => ((o, l) :: entries l) ++ bondEntries rest

/-- The entries of a list of forks. -/
def forkEntries : List (ForkE S) → List (Nat × Lazy S)
  | [] => []
  | ((oy, y), (on, n)) :: rest => ((oy, y) :: entries y) ++ ((on, n) :: entries n) ++ forkEntries rest
end

theorem entries_ofSure (s : Sure S) : entries (ofSure s) = [] := by
  simp [ofSure, entries, bondEntries, forkEntries]

/-- `+coerce-lazy` of the sure need of each entry, in order. -/
def coerceList (ned : Need) (less : Cape) : List (Nat × Lazy S) → CM Map Unit
  | [] => pure ()
  | (o, l) :: rest => do
    coerceLazy ned o l.sure less
    coerceList ned less rest

theorem coerceList_append (ned : Need) (less : Cape) : ∀ (a b : List (Nat × Lazy S)),
    (coerceList ned less (a ++ b) : CM Map Unit) = (do coerceList ned less a; coerceList ned less b)
  | [], b => by simp [coerceList]
  | (o, l) :: rest, b => by
    simp only [List.cons_append, coerceList, bind_assoc]
    rw [coerceList_append ned less rest b]

mutual
/-- **`+coerce-lazy` is the coercion of the sure need, then of every
entry.** -/
theorem coerceLazyL_flat (ned : Need) (less : Cape) : ∀ (o : Nat) (l : Lazy S),
    (coerceLazyL ned less o l : CM Map Unit) =
      (do coerceLazy ned o l.sure less; coerceList ned less (entries l))
  | o, mk s f b => by
    unfold coerceLazyL
    simp only [sure_mk, entries]
    congr 1
    funext u
    split
    · rename_i hfb
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hfb
      obtain ⟨rfl, rfl⟩ := hfb
      simp [bondEntries, forkEntries, coerceList]
    · rw [coerceBonds_flat ned less b, coerceForks_flat ned less f, coerceList_append]

theorem coerceBonds_flat (ned : Need) (less : Cape) : ∀ (b : List (Nat × Lazy S)),
    (coerceBonds ned less b : CM Map Unit) = coerceList ned less (bondEntries b)
  | [] => by simp [coerceBonds, bondEntries, coerceList]
  | (o, l) :: rest => by
    unfold coerceBonds
    simp only [bondEntries, List.cons_append, coerceList]
    rw [coerceLazyL_flat ned less o l, coerceBonds_flat ned less rest, coerceList_append, bind_assoc]

theorem coerceForks_flat (ned : Need) (less : Cape) : ∀ (f : List (ForkE S)),
    (coerceForks ned less f : CM Map Unit) = coerceList ned less (forkEntries f)
  | [] => by simp [coerceForks, forkEntries, coerceList]
  | ((oy, y), (on, n)) :: rest => by
    unfold coerceForks
    rw [coerceLazyL_flat ned less oy y, coerceLazyL_flat ned less on n, coerceForks_flat ned less rest]
    simp only [forkEntries, List.cons_append, List.append_assoc, coerceList, coerceList_append, bind_assoc]
end

/-! ## What the ops of one coercion do -/

/-- **What the ops `A` in front of a lazy block do** for the need `L`
taken there: from registers that hold the subject `s` as the input need
`ned` asks, they fill `L` and keep the input registers and every register
below `lo` outside `L`'s, or crash when `s` has not `L`'s shape and looks. -/
def FillSem (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (ned : Need) (lo : Nat) (L : Sure S) (A : List Pole) (s : Noun) : Prop :=
  ∀ R : Map Noun, HoldsN ned R s →
    (FitsS L s → ∃ R', Runs lib O c gul st t A R R' ∧ HoldsS L R' s ∧
      ∀ x, (NMem ned x ∨ x < lo) → ¬ NMem L.ned x → SkaModel.read x R' = SkaModel.read x R) ∧
    (¬ FitsS L s → Crashes lib O c gul st t A R)

theorem FillSem.mono {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}
    {t : Trace} {ned : Need} {lo lo' : Nat} {L : Sure S} {A : List Pole} {s : Noun}
    (h : FillSem lib O c gul st t ned lo L A s) (hl : lo' ≤ lo) : FillSem lib O c gul st t ned lo' L A s :=
  fun R hR => ⟨fun f => by
    obtain ⟨R', r, hh, k⟩ := (h R hR).1 f
    exact ⟨R', r, hh, fun x hx hn => k x (hx.elim Or.inl fun e => Or.inr (Nat.lt_of_lt_of_le e hl)) hn⟩,
    (h R hR).2⟩

/-- **`coerceSpec` with the registers it keeps.** -/
theorem coerceSpecK {ned : Need} {o : Nat} {laz : Sure S} {less : Cape} {g g' : Gen Map}
    (h : coerceLazy ned o laz less g = some ((), g')) (hd : g.drop = false) (_dn : Distinct ned)
    (dl : Distinct laz.ned) (ll : ∀ r, NMem laz.ned r → r < g.re) (ln : ∀ r, NMem ned r → r < g.re)
    (nd : ∀ r, NMem ned r → ¬ NMem laz.ned r) :
    ∃ A, Front o g g' A ∧ ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) gul st t s,
      CapeAxes less s → FillSem lib O c gul st t ned g.re laz A s := by
  simp only [coerceLazy] at h
  obtain ⟨lok, g1, h1, h⟩ := bind_some h
  obtain ⟨l, hl, e⟩ := Option.map_eq_some_iff.mp h1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  rw [coerceLok_eq] at hl
  obtain ⟨C1, C2, _⟩ := coerceFold_spec less ned _ _ _ hl
  obtain ⟨tgt, g2, h2, h3⟩ := bind_some h
  have L := sureRequireLook_spec h2
  obtain ⟨k, rfl⟩ := L.gen
  obtain ⟨A, F, sem⟩ := sureLoop_spec ned tgt _ g' () h3 hd
  have F' := (front_reg (o := o) g L.le).trans F
  simp only [List.append_nil] at F'
  refine ⟨A, F', ?_⟩
  have dt : Distinct tgt := L.dist dl ll
  have lt : ∀ x, NMem tgt x → x < k := fun x hx =>
    (L.mem x hx).elim (fun h => Nat.lt_of_lt_of_le (ll x h) L.le) (fun h => h.2)
  have SS := sem dt lt (fun x hx => Nat.lt_of_lt_of_le (ln x hx) L.le)
    (fun x hx ht => (L.mem x ht).elim (fun h => nd x hx h) (fun h => by have := ln x hx; simp at h; omega))
  intro lib σ O c gul st t s hca R hs
  have S1 := SS lib σ O c gul st t R s hs
  have sub : ∀ y ∈ HoonSet.toList l, y ∈ HoonSet.toList laz.lok := fun y hy =>
    (C1 y hy).elim (fun h => absurd h (HoonSet.mem_empty y)) id
  refine ⟨fun hf => ?_, fun hf => S1.2 fun ft => hf ?_⟩
  · have ft : Comp.Fits tgt s := (L.fits s).mpr ⟨hf.1, fun x hx => hf.2 x (sub x hx)⟩
    obtain ⟨R', hr, hh, fr⟩ := S1.1 ft
    refine ⟨R', hr, ⟨L.holds R' s hh, hf.2⟩, fun x hx hnl => ?_⟩
    have hxg : x < g.re := hx.elim (ln x) id
    refine fr x (Nat.lt_of_lt_of_le hxg L.le) fun ht => ?_
    exact (L.mem x ht).elim hnl (fun h => by simp at h; omega)
  · have F2 := (L.fits s).mp ft
    refine ⟨F2.1, fun y hy => ?_⟩
    obtain ⟨hy0, hy⟩ := C2 y hy
    rcases hy with hc | hn | hm
    · exact hca y (by omega) hc
    · exact slot_of_axeInNeed y (by omega) ned s (fits_of_holds ned hs) hn
    · exact F2.2 y hm

/-! ## The coercion of a list of entries -/

/-- What `+coerce-lazy` assumes of an entry: its need's registers are
distinct, allocated, and apart from the input registers. -/
def EntryRegs (ned : Need) (lim : Nat) (e : Nat × Lazy S) : Prop :=
  Distinct e.2.sure.ned ∧ (∀ r, NMem e.2.sure.ned r → r < lim) ∧ ∀ r, NMem ned r → ¬ NMem e.2.sure.ned r

theorem EntryRegs.mono {ned : Need} {a b : Nat} {e : Nat × Lazy S} (h : EntryRegs ned a e) (hab : a ≤ b) :
    EntryRegs ned b e :=
  ⟨h.1, fun r hr => Nat.lt_of_lt_of_le (h.2.1 r hr) hab, h.2.2⟩

/-- What the coercion of the entries does to the blocks of the entries. -/
def FilledAt (ned : Need) (less : Cape) (lo : Nat) (g g' : Gen Map) (e : Nat × Lazy S) : Prop :=
  ∀ B fin, HoonMap.get g.blocks e.1 = some ⟨[], B, fin⟩ → ∃ A, HoonMap.get g'.blocks e.1 = some ⟨[], A ++ B, fin⟩ ∧
    ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) gul st t s,
      CapeAxes less s → FillSem lib O c gul st t ned lo e.2.sure A s

/-- **The coercion of a list of entries with distinct labels.** -/
theorem coerceList_spec (ned : Need) (less : Cape) : ∀ (es : List (Nat × Lazy S)) (g g' : Gen Map),
    coerceList ned less es g = some ((), g') → g.drop = false → Distinct ned → (∀ r, NMem ned r → r < g.re) →
    (∀ e ∈ es, EntryRegs ned g.re e) → (es.map Prod.fst).Nodup →
    g'.bo = g.bo ∧ g'.drop = g.drop ∧ g.re ≤ g'.re ∧
    (∀ o, o ∉ es.map Prod.fst → HoonMap.get g'.blocks o = HoonMap.get g.blocks o) ∧
    ∀ e ∈ es, FilledAt ned less g.re g g' e
  | [], g, g', h, _, _, _, _, _ => by
    simp only [coerceList, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, fun e he => absurd he (List.not_mem_nil)⟩
  | (o, l) :: rest, g, g', h, hd, dn, ln, he, hnd => by
    simp only [coerceList] at h
    obtain ⟨u, g1, h1, h2⟩ := bind_some h
    have e0 := he (o, l) List.mem_cons_self
    obtain ⟨A, F, sem⟩ := coerceSpecK h1 hd dn e0.1 e0.2.1 ln e0.2.2
    have hd1 : g1.drop = false := F.drop.trans hd
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨IHbo, IHdr, IHle, IHo, IHf⟩ := coerceList_spec ned less rest g1 g' h2 hd1 dn
      (fun r hr => Nat.lt_of_lt_of_le (ln r hr) F.le)
      (fun e hm => (he e (List.mem_cons_of_mem _ hm)).mono F.le) hnd.2
    refine ⟨IHbo.trans F.bo, IHdr.trans F.drop, Nat.le_trans F.le IHle, fun o' ho' => ?_, fun e hm => ?_⟩
    · simp only [List.map_cons, List.mem_cons, not_or] at ho'
      rw [IHo o' ho'.2, F.other o' ho'.1]
    · rcases List.mem_cons.mp hm with rfl | hm
      · intro B fin hb
        refine ⟨A, ?_, sem⟩
        rw [IHo _ hnd.1]; exact F.blk B fin hb
      · intro B fin hb
        have ne : e.1 ≠ o := fun eq => hnd.1 (eq ▸ List.mem_map_of_mem hm)
        rw [← F.other _ ne] at hb
        obtain ⟨A', hb', sem'⟩ := IHf e hm B fin hb
        exact ⟨A', hb', fun lib σ O c gul st t s hs => (sem' lib σ O c gul st t s hs).mono F.le⟩

/-- **`+coerce-lazy` over a whole lazy tree** whose labels, with the label
of the `next`, are distinct. -/
theorem coerceLazyL_spec {ned : Need} {less : Cape} {o : Nat} {laz : Lazy S} {g g' : Gen Map}
    (h : coerceLazyL ned less o laz g = some ((), g')) (hd : g.drop = false) (dn : Distinct ned)
    (ln : ∀ r, NMem ned r → r < g.re) (e0 : EntryRegs ned g.re (o, laz))
    (he : ∀ e ∈ entries laz, EntryRegs ned g.re e) (hnd : (o :: (entries laz).map Prod.fst).Nodup) :
    g'.bo = g.bo ∧ g'.drop = g.drop ∧ g.re ≤ g'.re ∧
    (∀ o', o' ≠ o → o' ∉ (entries laz).map Prod.fst → HoonMap.get g'.blocks o' = HoonMap.get g.blocks o') ∧
    FilledAt ned less g.re g g' (o, laz) ∧ ∀ e ∈ entries laz, FilledAt ned less g.re g g' e := by
  rw [coerceLazyL_flat] at h
  have h' : (coerceList ned less ((o, laz) :: entries laz) : CM Map Unit) g = some ((), g') := by
    simp only [coerceList]; exact h
  have := coerceList_spec ned less ((o, laz) :: entries laz) g g' h' hd dn ln
    (fun e hm => (List.mem_cons.mp hm).elim (fun eq => eq ▸ e0) (he e)) (by simpa using hnd)
  obtain ⟨b1, b2, b3, b4, b5⟩ := this
  refine ⟨b1, b2, b3, fun o' h1 h2 => b4 o' ?_, b5 _ List.mem_cons_self, fun e hm => b5 e (List.mem_cons_of_mem _ hm)⟩
  simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨h1, h2⟩

end Comp
end SkaModel
end Formalization
