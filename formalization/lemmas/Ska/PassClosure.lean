import lemmas.Ska.PassDepth
import lemmas.Ska.PassMeasureA
import lemmas.Ska.FolWeight

/-!
# The closure invariant: finite formulas and leaves (track F, Gaps 16)

`passLoop_returns_ws` (`Ska/PassDepth.lean`) asks that every stack member be
`OkId Fs Ls`: its formula among a finite list `Fs`, its subject a shaped sock
whose leaves are among a finite list `Ls`.  Here the two lists are made
from two numbers of the poke, and the parts of the claim that do not need
an arm invariant are proved.

* **The bound.**  `NGood As B n`: `n` has at most `B` cells and atoms
  (`nsize`) and its atoms are among `As`.  `nounsUpTo As B` lists every such
  noun (`mem_nounsUpTo`).  For a poke, `B` is the largest `nsize` of the
  root formula, the data of the root subject sock and the nouns of the
  persistent memo, and `As` their atoms: the `&` regions the analysis can
  make are subnouns of those, of `%1` constants, and saf values, which are
  no bigger (`safV_size`) and have no other atoms (`safV_atoms`).
* **`OkId` from a tidy sock with good regions** (`okId_of_good`): an
  identity whose formula is `NGood` and whose subject sock is tidy with every
  `&` region `NGood` (`SockG`) is `OkId (nounsUpTo As B) (leafList As B)`.
* **The saf value of a formula** (`safV`): the constant a formula that
  `fol-loop` calls safe evaluates to, by the rules of `folStep` (`%1`, a
  cons of two safe sides, a `%spot` or `%mean` hint with safe hint and
  body).  **`folLoop_saf`**: whenever `fol-loop` returns `saf`, its product
  is `&` over `safV fol`, at every fuel and whatever `resolve` answers.  So a
  saf product is a function of the formula alone, which is what makes the
  `&` regions finitely many: the one source of `&` data that is not a part
  of an older one.

Not here: the arm invariant itself (every sock of `gen` and of the state is
tidy with `NGood` regions, every formula `fol-loop` analyses has `NGood`
saf values at every part), which needs the `&` regions of `+pull:so`,
`+darn:so`, `+knit:so`, `+double-int`, `+patch-prod`, `+msg-sock`,
`+app:ca` and the merge of `+run` (README Gaps 16).
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## 1. The bound and its finite list -/

/-- Every atom of the noun is among `As`. -/
def AtomsIn (As : List Nat) : Noun → Prop
  | Noun.atom k => k ∈ As
  | Noun.cell h t => AtomsIn As h ∧ AtomsIn As t

/-- At most `B` atoms and cells, atoms among `As`. -/
def NGood (As : List Nat) (B : Nat) (n : Noun) : Prop := nsize n ≤ B ∧ AtomsIn As n

/-- Every noun of `nsize` at most `B` with atoms among `As`. -/
def nounsUpTo (As : List Nat) : Nat → List Noun
  | 0 => []
  | B + 1 => As.map Noun.atom ++ (nounsUpTo As B).flatMap fun x => (nounsUpTo As B).map (Noun.cell x)

theorem mem_nounsUpTo (As : List Nat) : ∀ (B : Nat) (n : Noun), NGood As B n → n ∈ nounsUpTo As B
  | 0, Noun.atom _, h => absurd h.1 (by simp [nsize])
  | 0, Noun.cell _ _, h => absurd h.1 (by simp [nsize])
  | B + 1, Noun.atom k, h => List.mem_append_left _ (List.mem_map.mpr ⟨k, h.2, rfl⟩)
  | B + 1, Noun.cell x y, h => by
    have hs := h.1
    simp only [nsize] at hs
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, ?_, List.mem_map.mpr ⟨y, ?_, rfl⟩⟩)
    · exact mem_nounsUpTo As B x ⟨by omega, h.2.1⟩
    · exact mem_nounsUpTo As B y ⟨by omega, h.2.2⟩

/-! ## 2. Good regions, and `OkId` -/

/-- Every `&` region of the cape over the data satisfies `G`. -/
def RegG (G : Noun → Prop) : Cape → Noun → Prop
  | Cape.yes, d => G d
  | Cape.no, _ => True
  | Cape.cell a b, Noun.cell x y => RegG G a x ∧ RegG G b y
  | Cape.cell _ _, Noun.atom _ => True

/-- Every `&` region of the sock satisfies `G` (`%void` has none). -/
def SockG (G : Noun → Prop) : Sock → Prop
  | Sock.void => True
  | Sock.mk c d => RegG G c d

/-- The leaves of the socks of `OkId`: `|` over `0`, and `&` over a good noun. -/
def leafList (As : List Nat) (B : Nat) : List Sock :=
  Sock.mk Cape.no (A 0) :: (nounsUpTo As B).map (Sock.mk Cape.yes)

theorem shaped_of_tidyC : ∀ (c : Cape) (d : Noun), TidyC c d → Shaped c d
  | Cape.yes, _, _ => trivial
  | Cape.no, _, _ => trivial
  | Cape.cell _ _, Noun.atom _, h => h
  | Cape.cell a b, Noun.cell x y, h => ⟨shaped_of_tidyC a x h.2.1, shaped_of_tidyC b y h.2.2⟩

theorem leaves_of_tidyC {G : Noun → Prop} : ∀ (c : Cape) (d : Noun), TidyC c d → RegG G c d →
    ∀ a ∈ BT.leaves (capeBT c d), a = Sock.mk Cape.no (A 0) ∨ ∃ n, G n ∧ a = Sock.mk Cape.yes n
  | Cape.yes, d, _, hg, a, ha => by
    simp only [capeBT, BT.leaves, List.mem_singleton] at ha
    exact Or.inr ⟨d, hg, ha⟩
  | Cape.no, d, ht, _, a, ha => by
    simp only [capeBT, BT.leaves, List.mem_singleton] at ha
    exact Or.inl (by rw [ha]; simp only [TidyC] at ht; rw [ht])
  | Cape.cell _ _, Noun.atom _, ht, _, _, _ => absurd ht id
  | Cape.cell l r, Noun.cell x y, ht, hg, a, ha => by
    simp only [capeBT, BT.leaves, List.mem_append] at ha
    rcases ha with ha | ha
    · exact leaves_of_tidyC l x ht.2.1 hg.1 a ha
    · exact leaves_of_tidyC r y ht.2.2 hg.2 a ha

/-- **`OkId` from the closure invariant**: a formula `NGood` and a subject
sock that is tidy, not `%void`, with every `&` region `NGood`. -/
theorem okId_of_good {As : List Nat} {B : Nat} {i : Ident} (hf : NGood As B i.2) (hv : i.1 ≠ Sock.void)
    (ht : Tidy i.1) (hg : SockG (NGood As B) i.1) : OkId (nounsUpTo As B) (leafList As B) i := by
  refine ⟨mem_nounsUpTo As B _ hf, ?_⟩
  obtain ⟨s, f⟩ := i
  cases s with
  | void => exact absurd rfl hv
  | mk c d =>
    refine ⟨c, d, rfl, shaped_of_tidyC c d ht, fun a ha => ?_⟩
    rcases leaves_of_tidyC c d ht hg a ha with e | ⟨n, hn, e⟩
    · rw [e]; exact List.mem_cons_self
    · rw [e]; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨n, mem_nounsUpTo As B n hn, rfl⟩)

/-! ## 3. The saf value of a formula -/

/-- The constant that a formula `fol-loop` calls safe evaluates to, by the
rules of `folStep`: `%1`, a cons of safe sides (`consProd`), a `%spot` or
`%mean` hint with a safe hint formula and a safe body. -/
def safV : Noun → Option Noun
  | Noun.cell x@(Noun.cell _ _) q => (safV x).bind fun v => (safV q).map (Noun.cell v)
  | Noun.cell (Noun.atom 1) p => some p
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag) h@(Noun.cell _ _)) f) =>
    if tag = Tag.spot ∨ tag = Tag.mean then (safV h).bind fun _ => safV f else none
  | _ => none

theorem atomsIn_cell {As : List Nat} {x y : Noun} : AtomsIn As (Noun.cell x y) ↔ AtomsIn As x ∧ AtomsIn As y :=
  Iff.rfl

/-- `safV` is `none` off its three patterns. -/
theorem safV_other {x : Noun} (h1 : ∀ a b q, x = Noun.cell (Noun.cell a b) q → False)
    (h2 : ∀ p, x = Noun.cell (Noun.atom 1) p → False)
    (h3 : ∀ tag a b f, x = Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag) (Noun.cell a b)) f) → False) :
    safV x = none := by
  unfold safV
  split
  · exact absurd rfl (h1 _ _ _)
  · exact absurd rfl (h2 _)
  · exact absurd rfl (h3 _ _ _ _)
  · rfl

/-- A saf value is no bigger than its formula and has no other atoms. -/
theorem safV_bound (f : Noun) : ∀ v, safV f = some v →
    nsize v ≤ nsize f ∧ ∀ As, AtomsIn As f → AtomsIn As v := by
  induction f using safV.induct with
  | case1 a b q ih1 ih2 =>
    intro v h
    simp only [safV, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    obtain ⟨s1, a1⟩ := ih1 _ hx
    obtain ⟨s2, a2⟩ := ih2 _ hy
    exact ⟨by simp only [nsize] at s1 s2 ⊢; omega, fun As hA => ⟨a1 As hA.1, a2 As hA.2⟩⟩
  | case2 p =>
    intro v h
    simp only [safV, Option.some.injEq] at h
    subst h
    exact ⟨by simp only [nsize]; omega, fun As hA => hA.2⟩
  | case3 tag a b f ht _ ihf =>
    intro v h
    simp only [safV, ht, if_true, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, hf⟩ := h
    obtain ⟨s, at'⟩ := ihf _ hf
    exact ⟨by simp only [nsize] at s ⊢; omega, fun As hA => at' As hA.2.2⟩
  | case4 tag a b f ht =>
    intro v h
    simp only [safV, ht, if_false] at h
    cases h
  | case5 x h1 h2 h3 =>
    intro v h
    rw [safV_other h1 h2 h3] at h
    cases h

theorem safV_size {f v : Noun} (h : safV f = some v) : nsize v ≤ nsize f := (safV_bound f v h).1

theorem safV_atoms {As : List Nat} {f v : Noun} (h : safV f = some v) (hA : AtomsIn As f) : AtomsIn As v :=
  (safV_bound f v h).2 As hA

/-- What `folLoop_saf` says of one output: a saf product is `&` over the
saf value of the formula. -/
def SafP (fol : Noun) (out : FolOut) : Prop :=
  safV fol = some out.prod.sock.data ∧ out.prod.sock = Sock.mk Cape.yes out.prod.sock.data

theorem shape_op1C {fol p : Noun} (h : shape fol = Shape.op1 p) : fol = C (A 1) p := by
  unfold shape at h; split at h <;> cases h <;> rfl

/-- The `%2` case is never safe. -/
theorem callStep_saf {res : ResGo M R} {go : FolGoS M R} {seat mk : Option Noun} {bc df : Bool}
    {s f out : FolOut} {g g' : GenS M R} (h : callStep res go seat mk bc df s f g = some (out, g')) :
    out.saf = false := by
  unfold callStep at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
  · split at h
    · split at h
      · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, h, _⟩ := h; rw [← h]
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨_, _, h⟩ := h
        split at h
        · cases h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]

/-- One level of `fol-loop` keeps `SafP`, from the recursion. -/
theorem folStep_saf (env : Env R) {res : ResGo M R} {go : FolGoS M R}
    (IH : ∀ fol sub seat mk bc df gs out gs', go fol sub seat mk bc df gs = some (out, gs') →
      out.saf = true → SafP fol out)
    {fol : Noun} {sub : Anno} {seat mk : Option Noun} {bc df : Bool} {gs gs' : GenS M R} {out : FolOut}
    (h : folStep env res go fol sub seat mk bc df gs = some (out, gs')) (hs : out.saf = true) : SafP fol out := by
  cases e : shape fol with
  | cons a b q =>
    simp only [folStep, e, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨l, g1⟩, h1, ⟨r, g2⟩, h2, rfl, rfl⟩ := h
    rw [shape_cons e]
    unfold consProd at hs ⊢
    by_cases hc : l.saf = true ∧ r.saf = true ∧ l.prod.sock ≠ Sock.void ∧ r.prod.sock ≠ Sock.void
    · rw [if_pos hc]
      have e1 := (IH _ _ _ _ _ _ _ _ _ h1 hc.1).1
      have e2 := (IH _ _ _ _ _ _ _ _ _ h2 hc.2.1).1
      refine ⟨?_, rfl⟩
      simp only [Sock.data, safV, e1, e2, Option.bind_some, Option.map_some]
    · rw [if_neg hc] at hs; cases hs
  | op0 p =>
    simp only [folStep, e, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl, _⟩ := h; cases hs
  | op1 p =>
    simp only [folStep, e, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    rw [shape_op1C e]
    exact ⟨by simp [safV, Sock.data], rfl⟩
  | op2 a b q =>
    simp only [folStep, e, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, h3⟩ := h
    rw [callStep_saf h3] at hs; cases hs
  | op3 a b =>
    simp only [folStep, e, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl, _⟩ := h; cases hs
  | op4 a b =>
    simp only [folStep, e, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl, _⟩ := h; cases hs
  | op5 a b q =>
    simp only [folStep, e, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, _, _, rfl, _⟩ := h; cases hs
  | op6 a b q r =>
    simp only [folStep, e, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := h; cases hs
  | op7 a b q =>
    simp only [folStep, e, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, _, _, rfl, _⟩ := h; cases hs
  | op8 a b q =>
    simp only [folStep, e] at h
    have := (IH _ _ _ _ _ _ _ _ _ h hs).1
    simp [safV] at this
  | op9 p a b =>
    simp only [folStep, e] at h
    have := (IH _ _ _ _ _ _ _ _ _ h hs).1
    simp [safV] at this
  | op10 ax don r1 r2 =>
    simp only [folStep, e] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1] at hs; cases hs
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨_, _, _, _, _, _, rfl, _⟩ := h; cases hs
  | op11s p a b =>
    simp only [folStep, e] at h
    split at h
    · have := (IH _ _ _ _ _ _ _ _ _ h hs).1
      simp [safV] at this
    · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, rfl, _⟩ := h; cases hs
  | op11d tag h1 h2 f =>
    simp only [folStep, e, Option.bind_eq_some_iff] at h
    obtain ⟨⟨hh, g1⟩, hh1, h⟩ := h
    split at h
    · have := (IH _ _ _ _ _ _ _ _ _ h hs).1
      simp [safV] at this
    · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨arm, g2⟩, _, ⟨fr, g3⟩, h3, _, _, rfl, _⟩ := h
      simp only [decide_eq_true_eq] at hs
      obtain ⟨ht, hhs, hfs⟩ := hs
      have eh := (IH _ _ _ _ _ _ _ _ _ hh1 hhs).1
      obtain ⟨ef, ef2⟩ := IH _ _ _ _ _ _ _ _ _ h3 hfs
      rw [shape_op11d e]
      refine ⟨?_, ef2⟩
      simp only [safV, ht, if_true, eh, Option.bind_some, ef]
  | op11c x y h1 h2 f =>
    simp only [folStep, e] at h
    have := (IH _ _ _ _ _ _ _ _ _ h hs).1
    simp [safV, Tag.spot, Tag.mean] at this
  | op12 a b q =>
    simp only [folStep, e, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, _, _, rfl, _⟩ := h; cases hs
  | other =>
    simp only [folStep, e, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h; cases hs

/-- **A saf product of `fol-loop` is `&` over the saf value of its formula**,
at every fuel. -/
theorem folLoop_saf (env : Env R) (memoF : Memo M) : ∀ n fol sub seat mk bc df (gs : GenS M R) out gs',
    folLoop env memoF n fol sub seat mk bc df gs = some (out, gs') → out.saf = true → SafP fol out
  | 0, _, _, _, _, _, _, _, _, _, h, _ => by rw [folLoop_zero] at h; cases h
  | n + 1, _, _, _, _, _, _, _, _, _, h, hs => by
    rw [folLoop_succ] at h
    exact folStep_saf env (folLoop_saf env memoF n) h hs

/-! ## 4. The `&` regions of the sock operations of `fol-loop` -/

/-- `G` holds of the halves of every cell it holds of (`NGood` is). -/
def SubC (G : Noun → Prop) : Prop := ∀ x y, G (Noun.cell x y) → G x ∧ G y

theorem subC_nGood (As : List Nat) (B : Nat) : SubC (NGood As B) := fun x y h => by
  have hs := h.1; simp only [nsize] at hs
  exact ⟨⟨by omega, h.2.1⟩, ⟨by omega, h.2.2⟩⟩

section Regions

variable {G : Noun → Prop}

theorem sockG_dunno : SockG G Sock.dunno := trivial
theorem sockG_void : SockG G Sock.void := trivial

theorem sockG_knit {a b : Sock} (ha : SockG G a) (hb : SockG G b) : SockG G (So.knit a b) := by
  cases a with
  | void => trivial
  | mk l d1 =>
    cases b with
    | void => trivial
    | mk r d2 =>
      unfold So.knit
      simp only
      split
      · trivial
      · unfold Ca.con at *
        split
        · trivial
        · exact ⟨ha, hb⟩

theorem sockG_hed (hG : SubC G) {s : Sock} (h : SockG G s) : SockG G (So.hed s) := by
  rcases s with _ | ⟨c, d⟩
  · trivial
  · cases c <;> cases d <;> simp only [So.hed, SockG, RegG, Sock.dunno] at h ⊢
    all_goals first | trivial | exact (hG _ _ h).1 | exact h.1

theorem sockG_tel (hG : SubC G) {s : Sock} (h : SockG G s) : SockG G (So.tel s) := by
  rcases s with _ | ⟨c, d⟩
  · trivial
  · cases c <;> cases d <;> simp only [So.tel, SockG, RegG, Sock.dunno] at h ⊢
    all_goals first | trivial | exact (hG _ _ h).2 | exact h.2

theorem sockG_pullLoop (hG : SubC G) : ∀ (axe : Nat) (c : Cape) (d : Noun), RegG G c d →
    SockG G (So.pullLoop c d axe) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
  intro c d hc
  rw [So.pullLoop.eq_def]
  split
  · exact hc
  · split
    · trivial
    · split
      · trivial
      · rename_i dh dt _
        split
        · split
          · exact ih _ (mas_lt axe (by omega)) _ _ hc.1
          · exact ih _ (mas_lt axe (by omega)) _ _ hc.2
        · have hcy : c = Cape.yes := by
            cases c with
            | yes => rfl
            | no => contradiction
            | cell a b => exact ((by assumption : ∀ x y, Cape.cell a b = Cape.cell x y → False) a b rfl).elim
          subst hcy
          have h2 := hG _ _ hc
          split
          · exact ih _ (mas_lt axe (by omega)) _ _ h2.1
          · exact ih _ (mas_lt axe (by omega)) _ _ h2.2

theorem sockG_pull (hG : SubC G) {S s : Sock} {a : Nat} (h : SockG G S) (hp : So.pull S a = some s) :
    SockG G s := by
  unfold So.pull at hp
  split at hp
  · cases hp
  · split at hp
    · cases hp; trivial
    · cases hp; exact sockG_pullLoop hG a _ _ h

theorem sockG_darnUp : ∀ (acc : List (Nat × Sock)) (two : Sock), SockG G two →
    (∀ p ∈ acc, SockG G p.2) → SockG G (So.darnUp two acc)
  | [], two, h, _ => h
  | (n, s) :: acc, two, h, ha => by
    have hs : SockG G s := ha (n, s) (by simp)
    have ht : ∀ p ∈ acc, SockG G p.2 := fun p hp => ha p (by simp [hp])
    rw [darnUp_eq]
    split
    · exact sockG_darnUp _ _ (sockG_knit h hs) ht
    · exact sockG_darnUp _ _ (sockG_knit hs h) ht

theorem sockG_darnDown (hG : SubC G) : ∀ (ax : Nat) (one two : Sock) (acc : List (Nat × Sock)) (s : Sock),
    SockG G one → SockG G two → (∀ p ∈ acc, SockG G p.2) →
    So.darnDown one ax two acc = some s → SockG G s := by
  intro ax
  induction ax using Nat.strongRecOn with
  | _ ax ih =>
  intro one two acc s h1 h2 ha hd
  rw [So.darnDown] at hd
  split at hd
  · cases hd; exact sockG_darnUp acc two h2 ha
  · split at hd
    · cases hd
    · split at hd
      · exact ih (mas ax) (mas_lt ax (by omega)) _ _ _ _ (sockG_hed hG h1) h2
          (fun p hp => by
            simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact sockG_tel hG h1
            · exact ha p hp) hd
      · exact ih (mas ax) (mas_lt ax (by omega)) _ _ _ _ (sockG_tel hG h1) h2
          (fun p hp => by
            simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact sockG_hed hG h1
            · exact ha p hp) hd

/-- **`+darn:so` keeps good regions.** -/
theorem sockG_darn (hG : SubC G) {one two s : Sock} {ax : Nat} (h1 : SockG G one) (h2 : SockG G two)
    (hd : So.darn one ax two = some s) : SockG G s := by
  unfold So.darn at hd
  split at hd
  · cases hd; exact h2
  · split at hd
    · cases hd; trivial
    · split at hd
      · cases hd; trivial
      · exact sockG_darnDown hG ax one two [] s h1 h2 (by simp) hd

end Regions

end Ana
end SkaModel
end Formalization
