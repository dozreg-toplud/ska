import lemmas.Ska.FolLoopSound

/-!
# The call graph: the memo, recursive calls, patched products, convergence

Models of the arms of `nock-compilation.hoon` that answer a direct call in
`fol-loop` (the `resolve` loop of `+run`), arm by arm: `+knit-anno`,
`+patch-prod`, `+msg-anno`, `+msg-sock`, `+cape-size`, `+he-sock`, `+git:mi`,
`+recursive-call`, `+git-g`.  Maps are given as lists in the order of
`~(tap by ...)`, and the call graph as a function with the bunt of `datum` as
default (`+git-g`).

`Datum` is `+$datum` without `callees` and `area`, which record the graph and
the location of the code and feed nothing that the proofs read.

What convergence gives, and what it must give for `CodeOK`, is at the end of
the file (`Answers`, `answers_tabOK`, `entry_agree`).
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## Products -/

/-- `+knit-anno`. -/
def knitAnno (h t : Anno) : Anno := ⟨So.knit h.sock t.sock, Pi.cons h.src t.src⟩

/-- `+patch-prod`: the product of a function, with the provenance of its parts
in the function's subject, carried over to the subject sock `new`: a part
that comes from an axis of the subject is what `new` knows there; a part that
does not come from the subject stays.  `+pull:so` is called on an axis that is
not `0`, where it does not crash. -/
def patchProd (s : Sock) (src : Noun) (new : Sock) : Anno :=
  if src = A 0 then ⟨s, src⟩ else
  if s = Sock.void then ⟨s, src⟩ else
  match src with
  | Noun.atom a => ⟨(So.pull new a).getD Sock.void, src⟩
  | Noun.cell h t => knitAnno (patchProd (So.hed s) h new) (patchProd (So.tel s) t new)

/-- `+msg-sock`: the most specific generalization of two socks.  `none` is a
crash of the Hoon, on a cape that is a cell over atom data (`-.data`). -/
def msgSock (a b : Sock) : Option Sock :=
  if a = b then some a else
  match a, b with
  | Sock.void, b => some b
  | a, Sock.void => some a
  | Sock.mk (Cape.cell ah aT) (Noun.cell ad1 ad2), Sock.mk (Cape.cell bh bT) (Noun.cell bd1 bd2) =>
    (msgSock (Sock.mk ah ad1) (Sock.mk bh bd1)).bind fun h =>
    (msgSock (Sock.mk aT ad2) (Sock.mk bT bd2)).map fun t => So.knit h t
  | Sock.mk (Cape.cell _ _) _, Sock.mk (Cape.cell _ _) _ => none
  | Sock.mk _ _, Sock.mk _ _ => some Sock.dunno

/-- `+msg-anno`: the most specific generalization of two products, which the
entry of a function whose product changed already takes in place of
`+double-int` (to converge faster). -/
def msgAnno (a b : Anno) : Anno :=
  if a = b then a else
  match a, b with
  | ⟨Sock.void, _⟩, b => b
  | a, ⟨Sock.void, _⟩ => a
  | ⟨Sock.mk (Cape.cell ah aT) da, ra⟩, ⟨Sock.mk (Cape.cell bh bT) db, rb⟩ =>
    knitAnno
      (msgAnno ⟨So.hed (Sock.mk (Cape.cell ah aT) da), Pi.hed ra⟩ ⟨So.hed (Sock.mk (Cape.cell bh bT) db), Pi.hed rb⟩)
      (msgAnno ⟨So.tel (Sock.mk (Cape.cell ah aT) da), Pi.tel ra⟩ ⟨So.tel (Sock.mk (Cape.cell bh bT) db), Pi.tel rb⟩)
  | _, _ => Anno.dunno
termination_by Sock.msr a.sock + Sock.msr b.sock
decreasing_by
  · exact Nat.add_lt_add (msr_hed_lt (by simp) da) (msr_hed_lt (by simp) db)
  · exact Nat.add_lt_add (msr_tel_lt (by simp) da) (msr_tel_lt (by simp) db)

/-- The product an entry keeps after a run (`pm` in `+run`): the run's
product merged with the entry's, by `+msg-anno` if the product changed
already, else by `+double-int`. -/
def mergeProd (moved : Bool) (new old : Anno) : Anno :=
  if moved then msgAnno new old else doubleInt new old

theorem msgAnno_blank' : ∀ (k : Nat) (a b : Anno), Sock.msr a.sock + Sock.msr b.sock < k →
    a.sock.Blank → (msgAnno a b).sock.Blank := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk ha
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  obtain ⟨c, d, hs, hc⟩ := ha
  simp only at hs
  subst hs
  unfold msgAnno
  split
  · exact ⟨c, d, rfl, hc⟩
  · split
    · rename_i heq
      simp only [Anno.mk.injEq] at heq
      cases heq.1
    · exact ⟨c, d, rfl, hc⟩
    · rename_i ah aT da ra' bh bT db rb' heq1 heq2
      simp only [Anno.mk.injEq, Sock.mk.injEq] at heq1 heq2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq1
      obtain ⟨rfl, rfl⟩ := heq2
      simp only [Cape.isNo, Bool.and_eq_true] at hc
      simp only at hk
      exact knit_blank
        (ih _ _ (by have := msr_hed_lt (c := Cape.cell ah aT) (by simp) d
                    have := msr_hed_lt (c := Cape.cell bh bT) (by simp) db; simp only at hk ⊢; omega)
          (hed_blank ⟨_, _, rfl, by simp [Cape.isNo, hc.1, hc.2]⟩))
        (ih _ _ (by have := msr_tel_lt (c := Cape.cell ah aT) (by simp) d
                    have := msr_tel_lt (c := Cape.cell bh bT) (by simp) db; simp only at hk ⊢; omega)
          (tel_blank ⟨_, _, rfl, by simp [Cape.isNo, hc.1, hc.2]⟩))
    · exact dunno_blank

/-- **`+msg-anno` knows no more than the new product.** -/
theorem msgAnno_fits_left' : ∀ (k : Nat) (a b : Anno), Sock.msr a.sock + Sock.msr b.sock < k →
    ∀ n, Fits a.sock n → Fits (msgAnno a b).sock n := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk n hf
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  unfold msgAnno
  split
  · exact hf
  · split
    · rename_i heq
      simp only [Anno.mk.injEq] at heq
      rw [heq.1] at hf; exact absurd hf id
    · exact hf
    · rename_i ah aT da ra' bh bT db rb' heq1 heq2
      simp only [Anno.mk.injEq] at heq1 heq2
      obtain ⟨rfl, rfl⟩ := heq1
      obtain ⟨rfl, rfl⟩ := heq2
      simp only at hk hf
      have h1 := msr_hed_lt (c := Cape.cell ah aT) (by simp) da
      have h2 := msr_hed_lt (c := Cape.cell bh bT) (by simp) db
      have h3 := msr_tel_lt (c := Cape.cell ah aT) (by simp) da
      have h4 := msr_tel_lt (c := Cape.cell bh bT) (by simp) db
      cases n with
      | cell n1 n2 =>
        exact knit_fits (ih _ _ (by simp only; omega) _ (hed_fits hf))
          (ih _ _ (by simp only; omega) _ (tel_fits hf))
      | atom m =>
        obtain ⟨bh', bt'⟩ := hed_tel_blank_of_atom (k := m) hf
        exact (knit_blank (msgAnno_blank' _ _ _ (Nat.lt_succ_self _) bh')
          (msgAnno_blank' _ _ _ (Nat.lt_succ_self _) bt')).fits _
    · exact fits_dunno _

/-- **The product an entry keeps knows no more than the run's.**  So, at
convergence, where the kept product is the entry's own, it holds of every
product that the run's product holds of. -/
theorem mergeProd_fits (moved : Bool) (new old : Anno) {n : Noun} (h : Fits new.sock n) :
    Fits (mergeProd moved new old).sock n := by
  unfold mergeProd
  split
  · exact msgAnno_fits_left' _ new old (Nat.lt_succ_self _) n h
  · exact doubleInt_fits_left new old h

/-! ## The entries of the graph and the memo -/

/-- `+$datum` without `callees` and `area`. -/
structure Datum where
  nomm : Nomm
  less : Sock
  indi : Cape
  seek : Cape
  prod : Sock
  map : Noun

/-- `*datum`: a function in progress not analysed yet, which needs nothing
and returns `%void`. -/
def Datum.bunt : Datum := ⟨Nomm.n0 0, Sock.dunno, Cape.no, Cape.no, Sock.void, A 0⟩

/-- What `fol-loop` reads of a callee's entry. -/
def Datum.tab (d : Datum) : TabEntry := ⟨d.less, d.indi, d.seek, d.prod, d.map⟩

/-- An entry: the identity `[more fol]` and its datum. -/
structure Entry where
  more : Sock
  fol : Noun
  d : Datum

/-- `+git-g`. -/
def gitG (g : Sock × Noun → Option Datum) (i : Sock × Noun) : Datum := (g i).getD Datum.bunt

/-- The test of `+git:mi` and of `+recursive-call` on an entry: the subject
sock `s` provides the code that the function used, and knows no more than
the function's own subject where it found no code for a direct call. -/
def hitTest (e : Entry) (s : Sock) : Option Bool :=
  (So.huge e.d.less s).bind fun h1 =>
  if h1 then So.huge (Ca.app e.d.indi s) (Ca.app e.d.indi e.more) else some false

/-- The datum with its product patched for the subject sock `s`. -/
def patchDatum (d : Datum) (s : Sock) : Datum :=
  let p := patchProd d.prod d.map s
  { d with prod := p.sock, map := p.src }

/-- `+git:mi`, on the entries of the memo for one formula, in the order that
`~(tap by ...)` lists them.  The outer `none` is a crash. -/
def miGit : List Entry → Sock → Option (Option Entry)
  | [], _ => some none
  | e :: es, s =>
    match hitTest e s with
    | none => none
    | some true => some (some { e with d := patchDatum e.d s })
    | some false => miGit es s

/-- The loop of `+recursive-call`: `true` is `%rec`, `false` is `%he`.  The
homeomorphic embedding `+he-sock` is a parameter: it only chooses between
two answers that are both sound. -/
def recLoop (he : Sock → Sock → Bool) (heOn : Bool) (g : Sock × Noun → Option Datum)
    (kid : Sock × Noun) : List (Sock × Noun) → Option (Option (Bool × (Sock × Noun)))
  | [] => some none
  | i :: stk =>
    if kid.2 ≠ i.2 then recLoop he heOn g kid stk else
    match hitTest ⟨i.1, i.2, gitG g i⟩ kid.1 with
    | none => none
    | some true => some (some (true, i))
    | some false =>
      if heOn = true ∧ he kid.1 i.1 = true then
        (msgSock kid.1 i.1).map fun m => some (false, (m, kid.2))
      else recLoop he heOn g kid stk

/-- `+recursive-call`. -/
def recursiveCall (he : Sock → Sock → Bool) (threshold : Nat) (kid : Sock × Noun)
    (stk : List (Sock × Noun)) (g : Sock × Noun → Option Datum) :
    Option (Option (Bool × (Sock × Noun))) :=
  recLoop he (decide (threshold ≤ (stk.filter (fun i => i.2 = kid.2)).length)) g kid stk

/-! ## `+msg-sock` generalizes -/

theorem msgSock_blank_left' : ∀ (k : Nat) (a b m : Sock), nsize a.data < k → a.Blank →
    msgSock a b = some m → m.Blank := by
  intro k
  induction k with
  | zero => intro _ _ _ h; omega
  | succ k ih =>
  intro a b m hk ha hm
  obtain ⟨c, d, rfl, hc⟩ := ha
  unfold msgSock at hm
  split at hm
  · cases hm; exact ⟨c, d, rfl, hc⟩
  · split at hm
    · exact absurd ‹Sock.mk c d = Sock.void› (fun h => Sock.noConfusion h)
    · cases hm; exact ⟨c, d, rfl, hc⟩
    · rename_i ah aT ad1 ad2 bh bT bd1 bd2 heq _
      cases heq
      simp only [Cape.isNo, Bool.and_eq_true] at hc
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hm
      obtain ⟨h, hh, t, ht, rfl⟩ := hm
      simp only [Sock.data, nsize] at hk
      exact knit_blank (ih _ _ _ (by simp only [Sock.data]; omega) ⟨_, _, rfl, hc.1⟩ hh)
        (ih _ _ _ (by simp only [Sock.data]; omega) ⟨_, _, rfl, hc.2⟩ ht)
    · cases hm
    · cases hm; exact dunno_blank

theorem msgSock_blank_left {a b m : Sock} (ha : a.Blank) (hm : msgSock a b = some m) : m.Blank :=
  msgSock_blank_left' _ a b m (Nat.lt_succ_self _) ha hm

theorem msgSock_fits_left' : ∀ (k : Nat) (a b m : Sock) (n : Noun), nsize a.data < k → Fits a n →
    msgSock a b = some m → Fits m n := by
  intro k
  induction k with
  | zero => intro _ _ _ _ h; omega
  | succ k ih =>
  intro a b m n hk hf hm
  unfold msgSock at hm
  split at hm
  · cases hm; exact hf
  · split at hm
    · exact absurd hf id
    · cases hm; exact hf
    · rename_i ah aT ad1 ad2 bh bT bd1 bd2 _
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hm
      obtain ⟨h, hh, t, ht, rfl⟩ := hm
      simp only [Sock.data, nsize] at hk
      cases n with
      | cell n1 n2 =>
        exact knit_fits (ih (Sock.mk ah ad1) _ _ _ (by simp only [Sock.data]; omega) (hed_fits hf) hh)
          (ih (Sock.mk aT ad2) _ _ _ (by simp only [Sock.data]; omega) (tel_fits hf) ht)
      | atom k =>
        simp only [Fits, FitsCape] at hf
        rcases hf with hno | ⟨_, _, _, _, _, hn, _⟩
        · simp only [Bool.and_eq_true] at hno
          exact (knit_blank (msgSock_blank_left ⟨_, _, rfl, hno.1⟩ hh)
            (msgSock_blank_left ⟨_, _, rfl, hno.2⟩ ht)).fits _
        · cases hn
    · cases hm
    · cases hm; exact fits_dunno _

/-- **`+msg-sock` knows no more than its first argument.** -/
theorem msgSock_fits_left (a b m : Sock) (n : Noun) (hf : Fits a n) (hm : msgSock a b = some m) :
    Fits m n :=
  msgSock_fits_left' _ a b m n (Nat.lt_succ_self _) hf hm

/-! ## Generalization by forgetting -/

/-- **`S` generalizes `T` by forgetting**: `S` is `T`, or a sock whose cape
is `|`, or the knit of generalizations of the head and the tail of `T`.
Its facts are in `Stat.lean`; it is defined here for `Answers.hitGen`. -/
inductive GenLe : Sock → Sock → Prop where
  | refl (T : Sock) : GenLe T T
  | no (T : Sock) (d : Noun) : GenLe T (Sock.mk Cape.no d)
  | knit {T S1 S2 : Sock} : GenLe (So.hed T) S1 → GenLe (So.tel T) S2 → GenLe T (So.knit S1 S2)

/-- A generalization holds of every noun of the sock it generalizes, and is
blank if that sock is (`GenLe.fitsOpt` of `Stat.lean` in one piece). -/
theorem GenLe.fits_and {T S : Sock} (h : GenLe T S) : (T.Blank → S.Blank) ∧ ∀ y, Fits T y → Fits S y := by
  induction h with
  | refl T => exact ⟨id, fun _ h => h⟩
  | no T d => exact ⟨fun _ => ⟨Cape.no, d, rfl, rfl⟩, fun y _ => Sock.Blank.fits ⟨Cape.no, d, rfl, rfl⟩ y⟩
  | @knit T S1 S2 h1 h2 ih1 ih2 =>
    refine ⟨fun hT => knit_blank (ih1.1 (hed_blank hT)) (ih2.1 (tel_blank hT)), fun y hf => ?_⟩
    cases y with
    | cell a b => exact knit_fits (ih1.2 a (hed_fits hf)) (ih2.2 b (tel_fits hf))
    | atom k =>
      cases T with
      | void => exact absurd hf id
      | mk c d =>
        obtain ⟨bh, bt⟩ := hed_tel_blank_of_atom (k := k) hf
        exact Sock.Blank.fits (knit_blank (ih1.1 bh) (ih2.1 bt)) _

/-! ## What the table of a converged run is -/

/-- How the table of the last run of a function answers a call of the
formula `f` on the subject sock `s`, from the final graph `G`:

* `exact`: the entry of the identity `[s f]` (found in the graph, or made by
  `+analyze`);
* `hit`: an entry that passes the test of `+git:mi` and `+recursive-call`
  (`%rec`), with its product patched for `s`;
* `hitGen`: an entry that passes the test at a sock `s` that generalizes
  `s0`, with its product patched for `s0`.  This is the `%rec` branch after
  `%he` steps: `+recursive-call` tests the generalized sock, and the Hoon
  patches with the sock the loop began with (`sock.prod.s`);
* `gen`: the answer for an identity whose subject sock generalizes `s`
  (`%he`, with the subject `+msg-sock` makes). -/
inductive Answers (G : Entry → Prop) : Sock → Noun → TabEntry → Prop where
  | exact {e : Entry} : G e → Answers G e.more e.fol e.d.tab
  | hit {e : Entry} {s : Sock} : G e → hitTest e s = some true →
      Answers G s e.fol (patchDatum e.d s).tab
  | hitGen {e : Entry} {s s0 : Sock} : G e → hitTest e s = some true → GenLe s0 s →
      Answers G s0 e.fol (patchDatum e.d s0).tab
  | gen {s s' m : Sock} {f : Noun} {a : TabEntry} : msgSock s s' = some m → Answers G m f a →
      Answers G s f a

/-- Every subject of an entry's identity provides its code requirement:
`app:ca want more` for an entry made by a run (`app_fits`), the code
requirement of a memo entry from an earlier poke (`+huge:so`). -/
def LessOK (G : Entry → Prop) : Prop := ∀ e, G e → ∀ y, Fits e.more y → Fits e.d.less y

/-- The code table has a nomm for the bell of every entry. -/
def CodeHas (code : Bell → Option Nomm) (G : Entry → Prop) : Prop :=
  ∀ e, G e → ∃ nb, code ⟨e.d.less, e.fol⟩ = some nb

theorem answers_less {G : Entry → Prop} (hG : LessOK G) {s : Sock} {f : Noun} {a : TabEntry}
    (h : Answers G s f a) : ∀ y, Fits s y → Fits a.less y := by
  induction h with
  | exact he => exact hG _ he
  | hit _ ht =>
    rename_i e s _
    intro y hy
    simp only [hitTest, Option.bind_eq_some_iff] at ht
    obtain ⟨h1, hh, ht⟩ := ht
    cases h1 with
    | false => simp at ht
    | true => exact huge_sound hh hy
  | @hitGen e s s0 _ ht hg =>
    intro y hy
    simp only [hitTest, Option.bind_eq_some_iff] at ht
    obtain ⟨h1, hh, ht⟩ := ht
    cases h1 with
    | false => simp at ht
    | true => exact huge_sound hh (hg.fits_and.2 y hy)
  | gen hm _ ih => exact fun y hy => ih y (msgSock_fits_left _ _ _ _ hy hm)

theorem answers_code {G : Entry → Prop} {code : Bell → Option Nomm} (hc : CodeHas code G)
    {s : Sock} {f : Noun} {a : TabEntry} (h : Answers G s f a) : ∃ nb, code ⟨a.less, f⟩ = some nb := by
  induction h with
  | exact he => exact hc _ he
  | hit he _ => exact hc _ he
  | hitGen he _ _ => exact hc _ he
  | gen _ _ ih => exact ih

/-- **The table of a converged run is right on code requirements and code.**
If every answer of the table comes from the final graph, the graph's code
requirements hold of its identities' subjects, and the code table has every
entry's bell, then the table is `TabOK`, given that it is right on products
(`hprod`: what the fixed point must give, not proved here). -/
theorem answers_tabOK {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} {G : Entry → Prop}
    (hG : LessOK G) (hc : CodeHas code G) (hans : ∀ s f a, tab s f = some a → Answers G s f a)
    (hprod : ∀ s f d, tab s f = some d →
      ∀ y gul p, Fits s y → Mink lib gul [] y f (Tone.zero p) → Fits d.prod p) :
    TabOK lib code tab where
  less := fun s f a h => answers_less hG (hans s f a h)
  code := fun s f a h => answers_code hc (hans s f a h)
  prod := hprod

/-- **An entry of a converged graph agrees with `+mink` on its identity.**
For the last run of a function on its identity `[bus fol]`, with a table
whose answers come from the final graph: the nomm returns exactly what
`+mink` returns, on every subject of `bus`, given that the table is right on
products (`hprod`) and the code table satisfies the invariant (`hcode`). -/
theorem entry_agree {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} {G : Entry → Prop}
    (hG : LessOK G) (hc : CodeHas code G) (hans : ∀ s f a, tab s f = some a → Answers G s f a)
    (hprod : ∀ s f d, tab s f = some d →
      ∀ y gul p, Fits s y → Mink lib gul [] y f (Tone.zero p) → Fits d.prod p)
    (hcode : CodeOK lib code) {n : Nat} {bus : Sock} {fol : Noun} {out : FolOut} {gen' : Gen}
    (h : folLoopTop tab n bus fol = some (out, gen')) {x : Noun} (hx : Fits bus x) (gul : Noun)
    (t : Trace) (r : Tone) :
    Mink lib gul t x fol r ↔ ∃ m, nommF lib gul code m t x out.nomm = some r :=
  folLoop_agree (answers_tabOK hG hc hans hprod) hcode h hx gul t r

/-! ## What convergence must give for `CodeOK`

`CodeOK` asks of the nomm of every bell `[less fol]` that it satisfy `Annot`
on every subject of `less`.  An entry's nomm comes from the last run of
`fol-loop` on its identity `[more fol]`, and `folLoop_annot` gives `Annot` on
the subjects of `more` only; `less` is `app:ca want more`, which knows less.
So `CodeOK` at convergence is exactly `EntriesOK` below, and it needs the
relative soundness of `fol-loop`, `WantSound`, which is not proved: that the
analysis decides direct calls, inlining and memoization only on the parts of
the subject that `want` records, through the provenance of `+pi`. -/

/-- The code table holds the nomms of the graph's entries, under their bells. -/
def CodeIs (code : Bell → Option Nomm) (G : Entry → Prop) : Prop :=
  ∀ bl nb, code bl = some nb → ∃ e, G e ∧ bl = ⟨e.d.less, e.fol⟩ ∧ nb = e.d.nomm

/-- Every entry's nomm satisfies the invariant on its code requirement. -/
def EntriesOK (lib : Lib) (code : Bell → Option Nomm) (G : Entry → Prop) : Prop :=
  ∀ e, G e → Annot lib code (Fits e.d.less) e.fol e.d.nomm

theorem codeOK_of_entries {lib : Lib} {code : Bell → Option Nomm} {G : Entry → Prop}
    (hc : CodeIs code G) (he : EntriesOK lib code G) : CodeOK lib code := by
  intro bl nb h
  obtain ⟨e, hG, rfl, rfl⟩ := hc bl nb h
  exact he e hG

/-- **Not proved: the relative soundness of `fol-loop`.**  The nomm of a run
satisfies the invariant on every subject of its code requirement
`app:ca want bus`, not only on the subjects of `bus`. -/
def WantSound (lib : Lib) (code : Bell → Option Nomm) (tab : Tab) : Prop :=
  ∀ n bus fol out gen', folLoopTop tab n bus fol = some (out, gen') →
    Annot lib code (Fits (Ca.app gen'.want bus)) fol out.nomm

/-- An entry made by a converged run: its nomm is that of the last run of
`fol-loop` on its identity, with the table `tab`, and its code requirement
is the run's `want` united with some cape `w` (the cape of the entry's
previous code requirement, `+run` since 1813f09), applied to the subject
sock.  `entry_ok_of_run` is in `Converge.lean`, which has the monotonicity
of `+app:ca` in the cape (`fits_app_uni`). -/
def RunEntry (tab : Tab) (e : Entry) : Prop :=
  ∃ n out gen', folLoopTop tab n e.more e.fol = some (out, gen') ∧
    e.d.nomm = out.nomm ∧ (∃ w, e.d.less = Ca.app (Ca.uni gen'.want w) e.more)

/-- An entry made by a run fits `LessOK`. -/
theorem lessOK_of_run {tab : Tab} {e : Entry} (hr : RunEntry tab e) :
    ∀ y, Fits e.more y → Fits e.d.less y := by
  obtain ⟨_, _, _, _, _, _, hl⟩ := hr
  intro y hy
  rw [hl]
  exact app_fits _ _ _ hy

end SkaModel
end Formalization
