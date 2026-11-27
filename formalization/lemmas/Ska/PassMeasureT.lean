import lemmas.Ska.PassMeasureK
import lemmas.Ska.FolRel
import lemmas.Ska.ProvFacts

/-!
# Tidy subject socks and normal maps: an invariant of the graph (track F)

`runDatum_measure` (`PassMeasureK.lean`) needs of an entry `Tidy bus` (data `0`
under every `|`, a cell of data under every cell of the cape, no `[| |]`) and
`PiNorm` of its old map (no `[~ ~]`), and `less_untidy_example` shows the step
is false without `Tidy bus`.

## 1. On the real compiler

`tools/hoon/passmeasure.py` checks both at the end of every `+run` (2026-11-27,
the corpus of the earlier session: 2,266 calls of `+ska-callgraph`, 13,297 runs,
6,464 of them after an entry's first): the subject sock `bus`, the product of
`fol-loop`, the old and the new product, the new `less-code` and the subject
socks of all callees are tidy, and the old map, the map of `fol-loop` and the
new map have no `[~ ~]`, in every run.  A control with `bus = [[& |] [[0 3] 7]]`
is flagged.

## 2. No way in

The analysis takes socks from outside only at the root `&+sub` of a `%full`
poke (tidy) and from the memo of earlier pokes (`memo.lon`, written only by
`+ska-poke` from `+memo-final-entry` of the graph: the subject `+app:ca indi
more` and the product of an entry).  The other pokes that `+poke` accepts do
not reach a subject sock: `%fast` templates are clammed by `+validate-ovum`
(which keeps data under `|` and `[| |]`), but `+register-template` normalizes
each (`|` to `|+~`, `[& &]` to `&`, a cell cape over an atom crashes the poke),
and templates only feed `+cole-match` and `+register-fast` (a `%fast` hint's
template), never an identity; `%dire` (bell by `+validate-bell`, data
unchecked, cape `[| |]` accepted) writes only the compile caches; `%jets ~`
only the rings.  Inside the analysis every sock comes from `&+d`, `|+~`,
`%void`, `+pull:so`, `+knit:so`, `+darn:so`, `+double-int`, `+msg-anno`,
`+patch-prod`, `+msg-sock` (`%he`) and `+app:ca` (`less-code`, the memo key),
all of which keep `Tidy`.

## 3. Here

Every one of those operations keeps `Tidy` and `PiNorm` (`AnnoTP` for a
sock with its map); so does one level of `fol-loop` with a table whose answers
at tidy subject socks have tidy products (`folStep_tp`), hence every run
(`folR_tp`, `folTopR_tp`, from `[bus 1]`), and the datum `+run` writes
(`runDatum_tp`).  `GStepT` is `GStepR` with the side conditions on tidiness
(the subject of a new identity, the table of a run, the hit of the memo), and
every write keeps `GraphTP` (`GStepT.tp`, `graphTP_stepsT`): every identity's
subject sock, `less-code` and product is tidy and every map `PiNorm`.  So
`runDatum_measure_graph` is `runDatum_measure` without `Tidy bus`,
`NormSock old.prod` and `PiNorm old.map`, on any graph built by `GStepT`.
Not here: that the writes of the state-passing analysis (`Analysis.lean`) are
`GStepT` writes, the counterpart of `AnaInv.lean` for `GStepR`.
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## Socks -/

theorem tidy_void : Tidy Sock.void := trivial

theorem tidy_yes (d : Noun) : Tidy (Sock.mk Cape.yes d) := trivial

theorem tidyC_of_not {c : Cape} (h1 : ¬ c = Cape.no) (h2 : ∀ x y, c = Cape.cell x y → False)
    (d : Noun) : TidyC c d := by
  cases c with
  | no => exact absurd rfl h1
  | yes => trivial
  | cell x y => exact (h2 x y rfl).elim

theorem tidy_pullLoop : ∀ (axe : Nat) (c : Cape) (d : Noun), TidyC c d → Tidy (So.pullLoop c d axe) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
  intro c d hc
  rw [So.pullLoop.eq_def]
  split
  · exact hc
  · split
    · exact tidy_dunno
    · split
      · exact tidy_dunno
      · split
        · split
          · exact ih _ (mas_lt axe (by omega)) _ _ hc.2.1
          · exact ih _ (mas_lt axe (by omega)) _ _ hc.2.2
        · split
          · exact ih _ (mas_lt axe (by omega)) _ _ (tidyC_of_not (by assumption) (by assumption) _)
          · exact ih _ (mas_lt axe (by omega)) _ _ (tidyC_of_not (by assumption) (by assumption) _)

/-- **`+pull:so` keeps a tidy sock tidy.** -/
theorem tidy_pull {S s : Sock} {a : Nat} (h : Tidy S) (hp : So.pull S a = some s) : Tidy s := by
  unfold So.pull at hp
  split at hp
  · cases hp
  · split at hp
    · cases hp; exact tidy_void
    · cases hp; exact tidy_pullLoop a _ _ h

theorem tidy_darnUp : ∀ (acc : List (Nat × Sock)) (two : Sock), Tidy two →
    (∀ p ∈ acc, Tidy p.2) → Tidy (So.darnUp two acc)
  | [], two, h, _ => h
  | (n, s) :: acc, two, h, ha => by
    have hs : Tidy s := ha (n, s) (by simp)
    have ht : ∀ p ∈ acc, Tidy p.2 := fun p hp => ha p (by simp [hp])
    rw [darnUp_eq]
    split
    · exact tidy_darnUp _ _ (tidy_knit h hs) ht
    · exact tidy_darnUp _ _ (tidy_knit hs h) ht

theorem tidy_darnDown : ∀ (ax : Nat) (one two : Sock) (acc : List (Nat × Sock)) (s : Sock),
    Tidy one → Tidy two → (∀ p ∈ acc, Tidy p.2) →
    So.darnDown one ax two acc = some s → Tidy s := by
  intro ax
  induction ax using Nat.strongRecOn with
  | _ ax ih =>
  intro one two acc s h1 h2 ha hd
  rw [So.darnDown] at hd
  split at hd
  · cases hd; exact tidy_darnUp acc two h2 ha
  · split at hd
    · cases hd
    · split at hd
      · exact ih (mas ax) (mas_lt ax (by omega)) _ _ _ _ (tidy_hed h1) h2
          (fun p hp => by
            simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact tidy_tel h1
            · exact ha p hp) hd
      · exact ih (mas ax) (mas_lt ax (by omega)) _ _ _ _ (tidy_tel h1) h2
          (fun p hp => by
            simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact tidy_hed h1
            · exact ha p hp) hd

/-- **`+darn:so` keeps tidy socks tidy.** -/
theorem tidy_darn {one two s : Sock} {ax : Nat} (h1 : Tidy one) (h2 : Tidy two)
    (hd : So.darn one ax two = some s) : Tidy s := by
  unfold So.darn at hd
  split at hd
  · cases hd; exact h2
  · split at hd
    · cases hd; exact tidy_void
    · split at hd
      · cases hd; exact tidy_dunno
      · exact tidy_darnDown ax one two [] s h1 h2 (by simp) hd

theorem tidy_msgSock' : ∀ (k : Nat) (a b m : Sock), nsize a.data < k → Tidy a → Tidy b →
    msgSock a b = some m → Tidy m := by
  intro k
  induction k with
  | zero => intro _ _ _ h; omega
  | succ k ih =>
  intro a b m hk ha hb hm
  unfold msgSock at hm
  split at hm
  · cases hm; exact ha
  · split at hm
    · cases hm; exact hb
    · cases hm; exact ha
    · rename_i ah aT ad1 ad2 bh bT bd1 bd2 _
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hm
      obtain ⟨h, hh, t, ht, rfl⟩ := hm
      simp only [Sock.data, nsize] at hk
      exact tidy_knit (ih (Sock.mk ah ad1) _ _ (by simp only [Sock.data]; omega) (tidy_hed ha) (tidy_hed hb) hh)
        (ih (Sock.mk aT ad2) _ _ (by simp only [Sock.data]; omega) (tidy_tel ha) (tidy_tel hb) ht)
    · cases hm
    · cases hm; exact tidy_dunno

/-- **`+msg-sock` (the `%he` generalization) keeps tidy socks tidy.** -/
theorem tidy_msgSock {a b m : Sock} (ha : Tidy a) (hb : Tidy b) (hm : msgSock a b = some m) : Tidy m :=
  tidy_msgSock' _ a b m (Nat.lt_succ_self _) ha hb hm

/-! ## Maps -/

theorem piNorm_atom (k : Nat) : PiNorm (A k) := trivial

theorem piNorm_cons {x y : Noun} (hx : PiNorm x) (hy : PiNorm y) : PiNorm (Pi.cons x y) := by
  unfold Pi.cons; split
  · trivial
  · rename_i h; exact ⟨h, hx, hy⟩

theorem piNorm_slot : ∀ (ax : Nat) (pin : Noun), PiNorm pin → PiNorm (Pi.slot pin ax) := by
  intro ax
  induction ax using Nat.strongRecOn with
  | _ ax ih =>
  intro pin hp
  rw [Pi.slot.eq_def]
  split
  · exact hp
  · split
    · trivial
    · trivial
    · split
      · trivial
      · split
        · exact ih _ (mas_lt ax (by omega)) _ hp.2.1
        · exact ih _ (mas_lt ax (by omega)) _ hp.2.2

theorem piNorm_composeLoop {b : Noun} (hb : PiNorm b) : ∀ a, PiNorm (Pi.composeLoop b a)
  | Noun.atom 0 => by simp only [Pi.composeLoop]; trivial
  | Noun.atom (k + 1) => by simp only [Pi.composeLoop]; exact piNorm_slot _ _ hb
  | Noun.cell h t => by
    simp only [Pi.composeLoop]; exact piNorm_cons (piNorm_composeLoop hb h) (piNorm_composeLoop hb t)

/-- **`+compose:pi`** is normal when the provenance of the subject is. -/
theorem piNorm_compose {b : Noun} (hb : PiNorm b) (a : Noun) : PiNorm (Pi.compose a b) := by
  unfold Pi.compose; split
  · trivial
  · exact piNorm_composeLoop hb a

theorem piNorm_editUp : ∀ (tack : List (Nat × Noun)) (don : Noun), PiNorm don →
    (∀ p ∈ tack, PiNorm p.2) → PiNorm (Pi.editUp don tack)
  | [], don, h, _ => h
  | (n, s) :: tack, don, h, ha => by
    have hs : PiNorm s := ha (n, s) (by simp)
    have ht : ∀ p ∈ tack, PiNorm p.2 := fun p hp => ha p (by simp [hp])
    rw [editUp_eq]
    split
    · exact piNorm_editUp _ _ (piNorm_cons h hs) ht
    · exact piNorm_editUp _ _ (piNorm_cons hs h) ht

theorem piNorm_editDown : ∀ (ax : Nat) (rec don : Noun) (tack : List (Nat × Noun)),
    PiNorm rec → PiNorm don → (∀ p ∈ tack, PiNorm p.2) → PiNorm (Pi.editDown rec ax don tack) := by
  intro ax
  induction ax using Nat.strongRecOn with
  | _ ax ih =>
  intro rec don tack h1 h2 ha
  rw [Pi.editDown]
  split
  · exact piNorm_editUp tack don h2 ha
  · split
    · trivial
    · split
      · exact ih (mas ax) (mas_lt ax (by omega)) _ _ _ (piNorm_hed h1) h2
          (fun p hp => by
            simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact piNorm_tel h1
            · exact ha p hp)
      · exact ih (mas ax) (mas_lt ax (by omega)) _ _ _ (piNorm_tel h1) h2
          (fun p hp => by
            simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact piNorm_hed h1
            · exact ha p hp)

/-- **`+edit:pi`** keeps normal maps normal. -/
theorem piNorm_edit {rec don : Noun} {ax : Nat} (h1 : PiNorm rec) (h2 : PiNorm don) :
    PiNorm (Pi.edit rec ax don) := by
  unfold Pi.edit
  split
  · exact h2
  · split
    · trivial
    · exact piNorm_editDown ax rec don [] h1 h2 (by simp)

/-! ## Sock-annotated nouns -/

/-- A tidy sock with a normal map. -/
def AnnoTP (a : Anno) : Prop := Tidy a.sock ∧ PiNorm a.src

theorem annoTP_dunno : AnnoTP Anno.dunno := ⟨tidy_dunno, trivial⟩

theorem annoTP_hed {s : Sock} {r : Noun} (h : AnnoTP ⟨s, r⟩) : AnnoTP ⟨So.hed s, Pi.hed r⟩ :=
  ⟨tidy_hed h.1, piNorm_hed h.2⟩

theorem annoTP_tel {s : Sock} {r : Noun} (h : AnnoTP ⟨s, r⟩) : AnnoTP ⟨So.tel s, Pi.tel r⟩ :=
  ⟨tidy_tel h.1, piNorm_tel h.2⟩

theorem annoTP_knit {h t : Anno} (hh : AnnoTP h) (ht : AnnoTP t) : AnnoTP (knitAnno h t) :=
  ⟨tidy_knit hh.1 ht.1, piNorm_cons hh.2 ht.2⟩

theorem annoTP_doubleInt' : ∀ (k : Nat) (a b : Anno), Sock.msr a.sock + Sock.msr b.sock < k →
    AnnoTP a → AnnoTP b → AnnoTP (doubleInt a b) := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk ha hb
  by_cases hab : a = b
  · subst hab; rw [doubleInt_self]; exact ha
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  cases sa with
  | void => rw [doubleInt_void_left rfl hab]; exact hb
  | mk ca da =>
  cases sb with
  | void => rw [doubleInt_void_right rfl (by simp) hab]; exact ha
  | mk cb db =>
    apply doubleInt_cases AnnoTP hab annoTP_dunno
    intro hno
    simp only [not_or] at hno
    have h1 : Sock.msr (So.hed (Sock.mk ca da)) + Sock.msr (So.hed (Sock.mk cb db)) < k := by
      have := msr_hed_lt hno.1 da; have := msr_hed_lt hno.2 db; simp only at hk; omega
    have h2 : Sock.msr (So.tel (Sock.mk ca da)) + Sock.msr (So.tel (Sock.mk cb db)) < k := by
      have := msr_tel_lt hno.1 da; have := msr_tel_lt hno.2 db; simp only at hk; omega
    exact annoTP_knit (ih _ _ h1 (annoTP_hed ha) (annoTP_hed hb)) (ih _ _ h2 (annoTP_tel ha) (annoTP_tel hb))

/-- **`+double-int`** keeps tidy socks and normal maps. -/
theorem annoTP_doubleInt {a b : Anno} (ha : AnnoTP a) (hb : AnnoTP b) : AnnoTP (doubleInt a b) :=
  annoTP_doubleInt' _ a b (Nat.lt_succ_self _) ha hb

/-- **`+msg-anno`** keeps tidy socks and normal maps. -/
theorem annoTP_msgAnno (a b : Anno) (ha : AnnoTP a) (hb : AnnoTP b) : AnnoTP (msgAnno a b) := by
  fun_induction msgAnno a b with
  | case1 => exact ha
  | case2 => exact hb
  | case3 => exact ha
  | case4 _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    exact annoTP_knit (ih1 (annoTP_hed ha) (annoTP_hed hb)) (ih2 (annoTP_tel ha) (annoTP_tel hb))
  | case5 => exact annoTP_dunno

theorem annoTP_mergeProd (moved : Bool) {a b : Anno} (ha : AnnoTP a) (hb : AnnoTP b) :
    AnnoTP (mergeProd moved a b) := by
  unfold mergeProd
  split
  · exact annoTP_msgAnno a b ha hb
  · exact annoTP_doubleInt ha hb

theorem patchProd_void' (σ : Noun) (new : Sock) : patchProd Sock.void σ new = ⟨Sock.void, σ⟩ := by
  rw [patchProd.eq_def]; simp

/-- **`+patch-prod`** keeps a tidy product with a normal map, for a tidy
subject sock. -/
theorem annoTP_patchProd {new : Sock} (hn : Tidy new) :
    ∀ (σ : Noun) (S : Sock), AnnoTP ⟨S, σ⟩ → AnnoTP (patchProd S σ new) := by
  intro σ
  induction σ with
  | atom a =>
    intro S hS
    by_cases ha : a = 0
    · subst ha; rw [patchProd_zero]; exact hS
    by_cases hv : S = Sock.void
    · subst hv; rw [patchProd_void']; exact hS
    rw [patchProd_atom new ha hv]
    refine ⟨?_, trivial⟩
    cases hp : So.pull new a with
    | none => exact tidy_void
    | some s' => exact tidy_pull hn hp
  | cell h t ih1 ih2 =>
    intro S hS
    by_cases hv : S = Sock.void
    · subst hv; rw [patchProd_void']; exact hS
    rw [patchProd_cell new hv]
    exact annoTP_knit (ih1 _ ⟨tidy_hed hS.1, hS.2.2.1⟩) (ih2 _ ⟨tidy_tel hS.1, hS.2.2.2⟩)

theorem annoTP_patchDatum {d : Datum} {s : Sock} (hd : AnnoTP ⟨d.prod, d.map⟩) (hs : Tidy s) :
    AnnoTP ⟨(patchDatum d s).prod, (patchDatum d s).map⟩ :=
  annoTP_patchProd hs d.map d.prod hd

theorem annoTP_consProd {l r : FolOut} (hl : AnnoTP l.prod) (hr : AnnoTP r.prod) :
    AnnoTP (consProd l r).1 := by
  unfold consProd; split
  · exact ⟨trivial, trivial⟩
  · exact ⟨tidy_knit hl.1 hr.1, piNorm_cons hl.2 hr.2⟩

/-! ## `fol-loop` -/

/-- The table's answers at tidy subject socks have tidy products. -/
def TabTP (tab : Tab) : Prop := ∀ s f a, Tidy s → tab s f = some a → Tidy a.prod

/-- A recursion that keeps a tidy subject's product tidy and its map normal. -/
def GoTP (go : FolGo) : Prop :=
  ∀ fol sub mk bc df gen out gen', AnnoTP sub → go fol sub mk bc df gen = some (out, gen') → AnnoTP out.prod

theorem callStep_tp {tab : Tab} {go : FolGo} (htab : TabTP tab) (IH : GoTP go)
    {mk : Option Noun} {bc df : Bool} {s f out : FolOut} {gen gen' : Gen}
    (hs : AnnoTP s.prod) (h : callStep tab go mk bc df s f gen = some (out, gen')) : AnnoTP out.prod := by
  unfold callStep at h
  by_cases hv : s.prod.sock = Sock.void ∨ f.prod.sock = Sock.void
  · rw [if_pos hv] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨trivial, trivial⟩
  rw [if_neg hv] at h
  have dflt : ∀ (o : FolOut) (g : Gen), some (o, g) = some (out, gen') → o.prod = Anno.dunno →
      AnnoTP out.prod := by
    intro o g e hp
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rw [hp]; exact annoTP_dunno
  cases hf : f.prod.sock with
  | void => exact absurd (Or.inr hf) hv
  | mk c d =>
  rw [hf] at h
  cases c with
  | no => exact dflt _ _ h rfl
  | cell _ _ => exact dflt _ _ h rfl
  | yes =>
  cases d with
  | atom _ => exact dflt _ _ h rfl
  | cell fa fb =>
  cases bc with
  | true => exact dflt _ _ h rfl
  | false =>
  simp only at h
  split at h
  · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨i, hi, rfl, rfl⟩ := h
    have w := IH _ _ _ _ _ _ _ _ hs hi
    exact w
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨dd, hd, h⟩ := h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨htab _ _ _ hs.1 hd, piNorm_compose hs.2 _⟩

/-- **One level of `fol-loop` keeps `GoTP`.** -/
theorem folStep_tp {tab : Tab} {go : FolGo} (htab : TabTP tab) (IH : GoTP go) :
    GoTP (folStep tab go) := by
  intro fol sub mk bc df gen out gen' hsub h
  cases hs : shape fol with
  | cons a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨l, g1⟩, h1, ⟨r, g2⟩, h2, rfl, rfl⟩ := h
    exact annoTP_consProd (IH _ _ _ _ _ _ _ _ hsub h1) (IH _ _ _ _ _ _ _ _ hsub h2)
  | op0 p =>
    simp only [folStep, hs, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨pr, hpr, rfl, rfl⟩ := h
    split at hpr
    · cases hpr; exact annoTP_dunno
    · split at hpr
      · cases hpr; exact hsub
      · simp only [Option.map_eq_some_iff] at hpr
        obtain ⟨s', hs', rfl⟩ := hpr
        exact ⟨tidy_pull hsub.1 hs', piNorm_slot _ _ hsub.2⟩
  | op1 p =>
    simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨trivial, trivial⟩
  | op2 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff] at h
    obtain ⟨⟨s1, g1⟩, h1, ⟨f1, g2⟩, h2, h3⟩ := h
    exact callStep_tp htab IH (IH _ _ _ _ _ _ _ _ hsub h1) h3
  | op3 a b =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, rfl, rfl⟩ := h
    exact annoTP_dunno
  | op4 a b =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, rfl, rfl⟩ := h
    exact annoTP_dunno
  | op5 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    exact annoTP_dunno
  | op6 a b q r =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, ⟨r1, g3⟩, h3, rfl, rfl⟩ := h
    exact annoTP_doubleInt (IH _ _ _ _ _ _ _ _ hsub h2) (IH _ _ _ _ _ _ _ _ hsub h3)
  | op7 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    have w := IH _ _ _ _ _ _ _ _ (IH _ _ _ _ _ _ _ _ hsub h1) h2
    exact w
  | op8 a b q =>
    simp only [folStep, hs] at h
    exact IH _ _ _ _ _ _ _ _ hsub h
  | op9 p a b =>
    simp only [folStep, hs] at h
    exact IH _ _ _ _ _ _ _ _ hsub h
  | op10 ax don r1 r2 =>
    simp only [folStep, hs] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact annoTP_dunno
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨dn, g1⟩, h1, ⟨rc, g2⟩, h2, s', hd, rfl, rfl⟩ := h
      have w1 := IH _ _ _ _ _ _ _ _ hsub h1
      have w2 := IH _ _ _ _ _ _ _ _ hsub h2
      exact ⟨tidy_darn w2.1 w1.1 hd, piNorm_edit w2.2 w1.2⟩
  | op11s p a b =>
    simp only [folStep, hs] at h
    split at h
    · exact IH _ _ _ _ _ _ _ _ hsub h
    · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨q1, g1⟩, h1, rfl, rfl⟩ := h
      have w := IH _ _ _ _ _ _ _ _ hsub h1
      exact w
  | op11d tag h1 h2 f =>
    simp only [folStep, hs, Option.bind_eq_some_iff] at h
    obtain ⟨⟨hh, g1⟩, e1, h⟩ := h
    split at h
    · exact IH _ _ _ _ _ _ _ _ hsub h
    · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨arm, harm, ⟨fr, g3⟩, h3, rfl, rfl⟩ := h
      have w := IH _ _ _ _ _ _ _ _ hsub h3
      exact w
  | op11c x y h1 h2 f =>
    simp only [folStep, hs] at h
    exact IH _ _ _ _ _ _ _ _ hsub h
  | op12 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    exact annoTP_dunno
  | other =>
    simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact annoTP_dunno

/-- **A run with answers in `P`** keeps a tidy subject's product tidy and its
map normal, when the answers of `P` at tidy subject socks have tidy products. -/
theorem folR_tp {P : Sock → Noun → TabEntry → Prop} (hP : ∀ tab, TabIn P tab → TabTP tab) :
    ∀ (n : Nat) {fol : Noun} {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen gen' : Gen}
      {out : FolOut}, AnnoTP sub → FolR P n fol sub mk bc df gen out gen' → AnnoTP out.prod
  | 0, _, _, _, _, _, _, _, _, _, h => h.elim
  | n + 1, _, _, _, _, _, _, _, _, hs, h => by
    obtain ⟨tab, go, g', ht, hgo, h, _⟩ := h
    exact folStep_tp (hP tab ht) (fun _ _ _ _ _ _ _ _ hs' hg => folR_tp hP n hs' (hgo _ _ _ _ _ _ _ _ hg))
      _ _ _ _ _ _ _ _ hs h

/-- **The run of an entry** from a tidy `bus`: the first map is `1`. -/
theorem folTopR_tp {P : Sock → Noun → TabEntry → Prop} (hP : ∀ tab, TabIn P tab → TabTP tab)
    {n : Nat} {bus : Sock} {fol : Noun} {out : FolOut} {gen' : Gen} (hb : Tidy bus)
    (h : FolTopR P n bus fol out gen') : AnnoTP out.prod :=
  folR_tp hP n (sub := ⟨bus, A 1⟩) ⟨hb, trivial⟩ h

/-- **The datum `+run` writes**: `less-code` is tidy, the product tidy and the
map normal. -/
theorem runDatum_tp {moved : Bool} {bus : Sock} {out : FolOut} {gen' : Gen} {old : Datum}
    (hb : Tidy bus) (ho : AnnoTP out.prod) (hd : AnnoTP ⟨old.prod, old.map⟩) :
    Tidy (runDatum moved bus out gen' old).1.less ∧
      AnnoTP ⟨(runDatum moved bus out gen' old).1.prod, (runDatum moved bus out gen' old).1.map⟩ :=
  ⟨tidy_app _ hb, annoTP_mergeProd moved ho hd⟩

/-! ## The graph -/

/-- **The invariant**: every identity's subject sock, `less-code` and product
is tidy, and every map is normal. -/
def GraphTP (g : Graph) : Prop :=
  ∀ i d, g i = some d → Tidy i.1 ∧ Tidy d.less ∧ Tidy d.prod ∧ PiNorm d.map

theorem graphTP_empty : GraphTP (fun _ => none) := fun _ _ h => by cases h

theorem graphTP_put {g : Graph} {i : Sock × Noun} {d : Datum} (hg : GraphTP g) (hi : Tidy i.1)
    (hl : Tidy d.less) (hp : Tidy d.prod) (hm : PiNorm d.map) : GraphTP (g.put i d) := by
  intro j e hj
  unfold Graph.put at hj
  split at hj
  · rename_i h; subst h; cases hj; exact ⟨hi, hl, hp, hm⟩
  · exact hg j e hj

/-- The writes of `GStepR` with the side conditions on tidiness: the subject
sock of a new identity, the answers of the run's table, the hit of the memo. -/
inductive GStepT : Graph → Graph → Prop where
  | start {g : Graph} {i : Sock × Noun} : Tidy i.1 → GStepT g (g.put i Datum.bunt)
  | run {g : Graph} {i : Sock × Noun} {P : Sock → Noun → TabEntry → Prop} {n : Nat} {out : FolOut}
      {gen' : Gen} {moved : Bool} {old : Datum} :
      (∀ tab, TabIn P tab → TabTP tab) → FolTopR P n i.1 i.2 out gen' → g i = some old →
      GStepT g (g.put i (runDatum moved i.1 out gen' old).1)
  | pop {g : Graph} {i : Sock × Noun} {d : Datum} : g i = some d →
      GStepT g (g.put i (if d.prod = Sock.void then { d with prod := Sock.dunno } else d))
  | cull {g : Graph} {i : Sock × Noun} : GStepT g (g.del i)
  | memo {g : Graph} {i : Sock × Noun} {d : Datum} : Tidy i.1 → Tidy d.less → Tidy d.prod →
      PiNorm d.map → GStepT g (g.put i (patchDatum d i.1))

/-- **Every write keeps `GraphTP`.** -/
theorem GStepT.tp {g g' : Graph} (hs : GStepT g g') (hg : GraphTP g) : GraphTP g' := by
  cases hs with
  | start hi => exact graphTP_put hg hi tidy_dunno tidy_void trivial
  | run hP h ho =>
    obtain ⟨hi, _, hp, hm⟩ := hg _ _ ho
    obtain ⟨hl', hpm⟩ := runDatum_tp (moved := _) (gen' := _) hi (folTopR_tp hP hi h) ⟨hp, hm⟩
    exact graphTP_put hg hi hl' hpm.1 hpm.2
  | pop ho =>
    obtain ⟨hi, hl, hp, hm⟩ := hg _ _ ho
    split
    · exact graphTP_put hg hi hl tidy_dunno hm
    · exact graphTP_put hg hi hl hp hm
  | cull =>
    intro j e hj
    unfold Graph.del at hj
    split at hj
    · cases hj
    · exact hg j e hj
  | memo hi hl hp hm =>
    have := annoTP_patchDatum (d := _) ⟨hp, hm⟩ hi
    exact graphTP_put hg hi hl this.1 this.2

/-- A sequence of writes. -/
inductive GStepsT : Graph → Graph → Prop where
  | refl (g : Graph) : GStepsT g g
  | tail {g g' g'' : Graph} : GStepsT g g' → GStepT g' g'' → GStepsT g g''

theorem graphTP_stepsT {g g' : Graph} (hs : GStepsT g g') (hg : GraphTP g) : GraphTP g' := by
  induction hs with
  | refl => exact hg
  | tail _ h ih => exact h.tp ih

/-- **The step of an entry on a graph built by `GStepT`**: `runDatum_measure`
with `Tidy bus`, `NormSock old.prod` and `PiNorm old.map` from `GraphTP`.
What is left: the old `less-code` is a mask of `bus` (true after the entry's
first run, `runDatum`), and the old product is not `%void`. -/
theorem runDatum_measure_graph {g : Graph} (hg : GraphTP g) {i : Sock × Noun} {old : Datum}
    (ho : g i = some old) (moved : Bool) (out : FolOut) (gen' : Gen) {c0 : Cape}
    (h0 : old.less = Ca.app c0 i.1) (hv : old.prod ≠ Sock.void) :
    let d := (runDatum moved i.1 out gen' old).1
    kS d.less ≤ kS i.1 ∧ d.prod ≠ Sock.void ∧
    (kS old.less < kS d.less ∨
      (d.less = old.less ∧
        (kS d.prod < kS old.prod ∨
          (d.prod = old.prod ∧
            (MapLt (darkOf old.prod) d.map old.map ∨
              (d.map = old.map ∧
                (d.indi = old.indi ∨ d.indi = Ca.lack (msgCa (Ca.lack gen'.indi (darkOf i.1)) old.indi) (darkOf i.1)) ∧
                (d.indi = old.indi → d.seek = old.seek ∨ (d.seek = msgCa gen'.seek old.seek ∧ CapeLe old.seek d.seek)))))))) := by
  obtain ⟨hb, _, hp, hm⟩ := hg i old ho
  exact runDatum_measure moved out gen' old hb h0 hv (tidy_norm hp) hm

end SkaModel
end Formalization
