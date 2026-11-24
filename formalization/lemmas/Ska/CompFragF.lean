import lemmas.Ska.CompSevenA

/-!
# The fragment closed under `[7 p q]`: `FragI`

README Gaps 12.21.  `FragE` (`CompBondCall.lean`) with `[7 p q]` where `p`,
`q` or both call, in every `Annot` form, and the other parents of `FragE`
taking the new nomms as parts.

## The raw blocks

`tools/hoon/calldump3.hoon` (whole-subject version, subject unknown, before
`+optimize`), checked against `finishLUC` by the `#guard`s below.  The nomm
is the one the analysis gives (`%nomm` in the dump).

`[8 [2 [0 3] [0 2]] [4 [0 2]]]` (`%e8a`, the nomm `[7 [[2 [0 3] [0 2]] [0 1]]
[4 [0 2]]]`, subject `[[4 0 1] 5]`, product `7`): `0: v0 -> cel, hed -> v5,
tal -> v4, hop 4`; `4: nok v4 v5 -> v3, hop 3`; `3: mov v3 v2, hop 1`; `1: inc
v2 v1, don v1` (the body `[4 [0 2]]` asks only the head of the pushed pair,
so `[0 1]` asks nothing).  `[8 [0 3] [2 [0 2] [0 6]]]` (`%e8b`, `[7 [[0 3]
[0 1]] [2 [0 2] [0 6]]]`, product `6`): `0: v0 -> cel, hed -> v4, tal -> v3,
hop 3`; `3: nok v3 v4 -> v2`; `2: mov v2 v1`; `1: don v1`.

`[9 2 [0 1]]` (`%e9a`, `[7 [0 1] [2 [0 1] [0 2]]]`, subject `[[4 0 3] 5]`,
product `6`): `0: v0 -> v5, cel, hed -> v4, hop 4`; `4: mov v5 v3, hop 3`;
`3: nok v3 v4 -> v2`; `2`; `1`.  `[9 2 [2 [0 3] [0 2]]]` (`%e9b`, both parts
call, subject `[[1 [4 0 3] 5] 7]`, product `6`): `0: v0 -> cel, hed -> va,
tal -> v9, hop 6`; `6: nok v9 va -> v6, hop 5` (the core's call); `5: mov v6
v5, cel v5, hed v5 v8, mov v8 v4, hop 4`; `4: mov v5 v3, hop 3`; `3: nok v3
v4 -> v2` (the arm's call); `2`; `1`.

`[7 [7 [0 1] [2 [0 3] [0 2]]] [4 [0 1]]]` (`%s7n`, product `7`) has the
blocks of `[7 [2 [0 3] [0 2]] [4 [0 1]]]`.  `[[0 1] [7 [0 1] [2 [0 3] [0
2]]]]` (`%s7t`, a `[7 p q]` that calls as the tail of a cons, product
`[[[4 0 1] 5] 6]`): `0: v0 -> cel, hed -> v6, tal -> v5, hop 5`; `5: nok v5
v6 -> v4`; `4: mov v4 v3`; `3: mov v0 v2` (the head's bond, behind the
tail's call); `2: con v2 v3 -> v1`; `1: don v1`.

An inlined `[2 [0 1] [1 [2 [0 3] [0 2]]]]` (`%inl`) is compiled as a direct
call of the bell `[[%.n 0] [2 [0 3] [0 2]]]` (out of scope), not as `[7 p q]`.

## The fragment

`FragI t nm`: `t = true` when `nm` meets `EntNew` (it may be the tail of a
cons behind a head under the bond goal).  `[7 p q]` asks `NoEntF q` (`q`'s
run returns a need without entries) and is in the fragment when `p` is
(`sevenPU`, `sevenPF`, `EntNew` when `p` has it), when `p` is `[0 axe]` or
`[1 k]` and `q` is (`sevenJ`, `EntNew` from `q`'s), or when `p` is any
call-free nomm of `FragU` and `q` is in the fragment (`sevenU`, no `EntNew`).

* `FragI`, `fragI_hinted`, `fragI_not_pure`, `bareLitQ_fragI`, `FragUF`,
  `fragUE_fragUF`.
* `uokc_entNew_of_fragI`, `uokc_of_fragUF`, `finishLUC_contractUF`.
* Examples with both halves: `seven_exampleA` (`[7 [2 [0 3] [0 2]] [4 [0
  1]]]`), `seven_exampleB` (`[7 [[0 1] [0 1]] [2 [0 3] [0 2]]]`),
  `eight_exampleA` (`%e8a`), `eight_exampleB` (`%e8b`), `nine_exampleA`
  (`%e9a`), `nine_exampleB` (`%e9b`), `seven_exampleN` (`%s7n`),
  `seven_exampleT` (`%s7t`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-! ## The raw blocks -/

-- `%e8a`
#guard monoOutC envR (Nomm.n7 (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1))
    (Nomm.n4 (Nomm.n0 2))) 6 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 6, Pole.cel 6, Pole.hed 6 8, Pole.mov 8 5, Pole.tal 6 7, Pole.mov 7 4] (hp 4)),
    (1, bk [Pole.inc 2 1] (Termin.don 1)),
    (2, none),
    (3, bk [Pole.mov 3 2] (hp 1)),
    (4, bk [Pole.nok 4 5 3] (hp 3)),
    (5, none)])

-- `%e8b`
#guard monoOutC envR (Nomm.n7 (Nomm.cons (Nomm.n0 3) (Nomm.n0 1)) (Nomm.n2 (Nomm.n0 2) (Nomm.n0 6) Option.none)) 5 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 5, Pole.cel 5, Pole.hed 5 7, Pole.mov 7 4, Pole.tal 5 6, Pole.mov 6 3] (hp 3)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.mov 2 1] (hp 1)),
    (3, bk [Pole.nok 3 4 2] (hp 2)),
    (4, none)])

-- `%e9a`
#guard monoOutC envR (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none)) 6 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 5, Pole.cel 5, Pole.hed 5 7, Pole.mov 7 4] (hp 4)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.mov 2 1] (hp 1)),
    (3, bk [Pole.nok 3 4 2] (hp 2)),
    (4, bk [Pole.mov 5 3] (hp 3)),
    (5, none)])

-- `%e9b`
#guard monoOutC envR (Nomm.n7 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)
    (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none)) 8 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 11, Pole.cel 11, Pole.hed 11 13, Pole.mov 13 10, Pole.tal 11 12,
      Pole.mov 12 9] (hp 6)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.mov 2 1] (hp 1)),
    (3, bk [Pole.nok 3 4 2] (hp 2)),
    (4, bk [Pole.mov 5 3] (hp 3)),
    (5, bk [Pole.mov 6 5, Pole.cel 5, Pole.hed 5 8, Pole.mov 8 4] (hp 4)),
    (6, bk [Pole.nok 9 10 6] (hp 5)),
    (7, none)])

-- `%s7n`
#guard monoOutC envR (Nomm.n7 (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none))
    (Nomm.n4 (Nomm.n0 1))) 5 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 6, Pole.cel 6, Pole.hed 6 8, Pole.mov 8 5, Pole.tal 6 7, Pole.mov 7 4] (hp 3)),
    (1, bk [Pole.inc 2 1] (Termin.don 1)),
    (2, bk [Pole.mov 3 2] (hp 1)),
    (3, bk [Pole.nok 4 5 3] (hp 2)),
    (4, none)])

-- `%s7t`
#guard monoOutC envR (Nomm.cons (Nomm.n0 1) (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none))) 7 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 7, Pole.cel 7, Pole.hed 7 9, Pole.mov 9 6, Pole.tal 7 8, Pole.mov 8 5] (hp 5)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.con 2 3 1] (hp 1)),
    (3, bk [Pole.mov 0 2] (hp 2)),
    (4, bk [Pole.mov 4 3] (hp 3)),
    (5, bk [Pole.nok 5 6 4] (hp 4)),
    (6, none)])

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The fragment -/

/-- **The nomms that call, closed under `[7 p q]`**; `t = true` when the
nomm meets `EntNew`. -/
inductive FragI : Bool → Nomm → Prop
  | e {nm : Nomm} : FragE (S := S) nm → FragI true nm
  | weak {nm : Nomm} : FragI true nm → FragI false nm
  | indS {t : Bool} {p q : Nomm} : FragI t p → FragU (S := S) q → bareLitQ q = false →
      FragI true (Nomm.n2 p q Option.none)
  | indF {t : Bool} {p q : Nomm} : FragU (S := S) p → FragI t q → FragI true (Nomm.n2 p q Option.none)
  | indSF {t t' : Bool} {p q : Nomm} : FragI t p → FragI t' q → FragI true (Nomm.n2 p q Option.none)
  | consH {t : Bool} {p d : Nomm} : FragI t p → FragU (S := S) d → FragI true (Nomm.cons p d)
  | consT {p d : Nomm} : FragB (S := S) p → FragI true d → FragI true (Nomm.cons p d)
  | consI {b c d : Nomm} : FragU (S := S) b → FragU (S := S) c → bareLitQ c = false → FragI true d →
      FragI true (Nomm.cons (Nomm.n2 b c Option.none) d)
  | sevenPU {t : Bool} {p q : Nomm} : FragI t p → FragU (S := S) q → NoEntF q → FragI t (Nomm.n7 p q)
  | sevenPF {t t' : Bool} {p q : Nomm} : FragI t p → FragI t' q → NoEntF q → FragI t (Nomm.n7 p q)
  | sevenJ {p q : Nomm} : JNewQ p → FragI true q → NoEntF q → FragI true (Nomm.n7 p q)
  | sevenU {t : Bool} {p q : Nomm} : FragU (S := S) p → FragI t q → NoEntF q → FragI false (Nomm.n7 p q)

theorem fragI_hinted (cod : Bell → Option Bool) {t : Bool} {nm : Nomm} (h : FragI (S := S) t nm) :
    hinted cod nm = some true := by
  induction h with
  | e h => exact fragE_hinted cod h
  | weak _ ih => exact ih
  | indS _ _ _ _ => rfl
  | indF _ _ _ => rfl
  | indSF _ _ _ _ => rfl
  | consH _ _ ih => simp only [hinted, ih]; rfl
  | consT hp _ ih => simp only [hinted, hinted_pure cod _ (fragU_pure (fragB_fragU hp)), ih]; rfl
  | consI _ _ _ _ ih => simp only [hinted]; rfl
  | sevenPU _ _ _ ih => simp only [hinted, ih]; rfl
  | sevenPF _ _ _ ih _ => simp only [hinted, ih]; rfl
  | sevenJ hp _ _ ih => simp only [hinted, hinted_pure cod _ (fragU_pure (fragU_of_jNewQ (S := S) hp)), ih]; rfl
  | sevenU hp _ _ ih => simp only [hinted, hinted_pure cod _ (fragU_pure hp), ih]; rfl

theorem fragI_not_pure {t : Bool} {nm : Nomm} (h : FragI (S := S) t nm) : nm.pure = false := by
  cases e : nm.pure with
  | false => rfl
  | true =>
    have := fragI_hinted (fun _ => Option.none) h
    rw [hinted_pure _ _ e] at this
    cases this

theorem bareLitQ_fragI {t : Bool} {nm : Nomm} (h : FragI (S := S) t nm) : bareLitQ nm = false := by
  have := fragI_not_pure h
  cases nm <;> simp_all [bareLitQ, Nomm.pure]

theorem fragI_weak {t : Bool} {nm : Nomm} (h : FragI (S := S) t nm) : FragI (S := S) false nm := by
  cases t with
  | false => exact h
  | true => exact FragI.weak h

/-- **The fragment.** -/
def FragUF (S : Type) [HoonSet S] (nm : Nomm) : Prop := FragU (S := S) nm ∨ FragI (S := S) false nm

/-- **`FragUE` is inside `FragUF`.** -/
theorem fragUE_fragUF {nm : Nomm} (h : FragUE S nm) : FragUF S nm :=
  h.elim Or.inl (fun h' => Or.inr (FragI.weak (FragI.e h')))

/-! ## The joint induction -/

/-- **The joint induction over `FragI`**: every `Annot` of a nomm of `FragI
t` meets `UOKC`, and the nomm meets `EntNew` when `t = true`. -/
theorem uokc_entNew_of_fragI {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv)
    {t : Bool} {nm : Nomm} (hf : FragI (S := S) t nm) :
    ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f nm →
      UOKC (S := S) (Map := Map) lib env P f nm ∧ (t = true → EntNew (S := S) (Map := Map) env nm) := by
  induction hf with
  | e h => exact fun hA => ⟨(uokc_entNew_of_fragE hok env h hA).1, fun _ => (uokc_entNew_of_fragE hok env h hA).2⟩
  | weak _ ih => exact fun hA => ⟨(ih hA).1, fun e => by cases e⟩
  | indS _ hq hbl ih =>
    intro P f hA
    have R := uokc_indDA env (fun h => (ih h).1) (uokcU hok env hq) hbl hA rfl
    exact ⟨R.1, fun _ => R.2⟩
  | indF hp hq ih =>
    intro P f hA
    have R := uokc_indDA env (uokcU hok env hp) (fun h => (ih h).1) (bareLitQ_fragI hq) hA rfl
    exact ⟨R.1, fun _ => R.2⟩
  | indSF _ hq ihp ihq =>
    intro P f hA
    have R := uokc_indDA env (fun h => (ihp h).1) (fun h => (ihq h).1) (bareLitQ_fragI hq) hA rfl
    exact ⟨R.1, fun _ => R.2⟩
  | consH hp hd ih =>
    intro P f hA
    have nh : hinted env.cod _ = some false := hinted_pure env.cod _ (fragU_pure hd)
    have R := uokc_consDA hok env (fun h => (ih h).1)
      (fun h => ⟨uokcU hok env hd h, fun e => by rw [nh] at e; cases e⟩) (fun e => by rw [nh] at e; cases e)
      (by simp only [hinted, fragI_hinted env.cod hp, nh]; rfl) hA rfl
    exact ⟨R.1, fun _ => R.2⟩
  | consT hp hd ih =>
    intro P f hA
    have R := uokc_consDA hok env (uokcU hok env (fragB_fragU hp)) (fun h => ⟨(ih h).1, fun _ => (ih h).2 rfl⟩)
      (fun _ => hp)
      (by simp only [hinted, hinted_pure env.cod _ (fragU_pure (fragB_fragU hp)), fragI_hinted env.cod hd]; rfl)
      hA rfl
    exact ⟨R.1, fun _ => R.2⟩
  | consI hb hc hbl hd ih =>
    intro P f hA
    have R := uokc_consEA env (fun h => (uokc_indDA env (uokcU hok env hb) (uokcU hok env hc) hbl h rfl).1)
      (fun h _ => bondOKC_indA hok env hb hc hbl h rfl) (fun h => ⟨(ih h).1, fun _ => (ih h).2 rfl⟩)
      (by simp only [hinted, fragI_hinted env.cod hd]; rfl) hA rfl
    exact ⟨R.1, fun _ => R.2⟩
  | @sevenPU t p q hp hq hn ih =>
    intro P f hA
    have R := uokc_sevenA (Xq := True) hok env (fun h => ih h) (fun h => ⟨uokcU hok env hq h, trivial⟩)
      (fun e => by rw [fragI_not_pure hp] at e; cases e) (noEnt_of_noEntF env hn)
      (by simp only [hinted, fragI_hinted env.cod hp]; rfl) hA rfl
    exact ⟨R.1, fun ht => R.2 (fun xp _ => Or.inl (xp ht))⟩
  | @sevenPF t t' p q hp hq hn ihp ihq =>
    intro P f hA
    have R := uokc_sevenA hok env (fun h => ihp h) (fun h => ihq h)
      (fun e => by rw [fragI_not_pure hp] at e; cases e) (noEnt_of_noEntF env hn)
      (by simp only [hinted, fragI_hinted env.cod hp]; rfl) hA rfl
    exact ⟨R.1, fun ht => R.2 (fun xp _ => Or.inl (xp ht))⟩
  | @sevenJ p q hp hq hn ih =>
    intro P f hA
    have hpU := fragU_of_jNewQ (S := S) hp
    have R := uokc_sevenA (Xp := True) hok env (fun h => ⟨uokcU hok env hpU h, trivial⟩) (fun h => ih h)
      (fun _ => ⟨runU_uok lib hpU, trivial⟩) (noEnt_of_noEntF env hn)
      (by simp only [hinted, hinted_pure env.cod _ (fragU_pure hpU), fragI_hinted env.cod hq]; rfl) hA rfl
    exact ⟨R.1, fun _ => R.2 (fun _ xq => Or.inr ⟨jNew_of_jNewQ env hp, xq rfl⟩)⟩
  | @sevenU t p q hp hq hn ih =>
    intro P f hA
    have R := uokc_sevenA (Xp := True) hok env (fun h => ⟨uokcU hok env hp h, trivial⟩) (fun h => ih h)
      (fun _ => ⟨runU_uok lib hp, trivial⟩) (noEnt_of_noEntF env hn)
      (by simp only [hinted, hinted_pure env.cod _ (fragU_pure hp), fragI_hinted env.cod hq]; rfl) hA rfl
    exact ⟨R.1, fun e => by cases e⟩

/-- **Every `Annot` of a nomm of `FragUF` meets `UOKC`.** -/
theorem uokc_of_fragUF {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {nm : Nomm}
    (hf : FragUF S nm) {P : Noun → Prop} {f : Noun} (hA : Annot lib code P f nm) :
    UOKC (S := S) (Map := Map) lib env P f nm := by
  rcases hf with h | h
  · exact uokcU hok env h hA
  · exact (uokc_entNew_of_fragI hok env h hA).1

/-- **The contract on `FragUF`** (`finishLUC_contractG`). -/
theorem finishLUC_contractUF {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    {nm : Nomm} (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm) (hf : FragUF S nm)
    (hcount : sixCount nm ≤ 255) {env : CallEnv} {cd : Straight Map} (h : finishLUC (S := S) env nm = some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have H := finishLUC_contractG lib (uokc_of_fragUF (Map := Map) hok env hf hA) hcount h N
  refine ⟨H.1, fun s hs args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact H.2 s hs

/-! ## Examples -/

theorem fragI_ind00 {a b : Nat} : FragI (S := S) true (Nomm.n2 (Nomm.n0 a) (Nomm.n0 b) Option.none) :=
  FragI.e (FragE.d (FragD.ind (FragU.x (FragX.frag fun _ => trivial)) (FragU.x (FragX.frag fun _ => trivial)) rfl))

theorem noEntF_ind00 {a b : Nat} : NoEntF (Nomm.n2 (Nomm.n0 a) (Nomm.n0 b) Option.none) :=
  NoEntF.ind rfl rfl (NoEntF.pure rfl rfl)

/-- **`[7 [2 [0 3] [0 2]] [4 [0 1]]]` end to end** (`%s7a` of
`CompRunOKLC.lean`): the call is `p`, under `q`'s result goal `%next (this
v2)`. -/
theorem seven_exampleA {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hfol : bl.fol = n3 (A 7) (n3 (A 2) (slot 3) (slot 2)) (n2 (A 4) (slot 1))) {env : CallEnv}
    {cd : Straight Map}
    (h : finishLUC (S := S) env (Nomm.n7 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n4 (Nomm.n0 1))) =
      some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have hA : Annot lib code (SkaModel.Fits bl.less) bl.fol
      (Nomm.n7 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n4 (Nomm.n0 1))) := by
    rw [hfol]
    exact Annot.n7 (Annot.indirect Annot.n0 Annot.n0) (Annot.n4 Annot.n0)
  have hf : FragUF S (Nomm.n7 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n4 (Nomm.n0 1))) :=
    Or.inr (FragI.weak (FragI.sevenPU fragI_ind00 (FragU.four (FragU.x (FragX.frag fun _ => trivial)))
      (NoEntF.pure rfl rfl)))
  exact finishLUC_contractUF hok hA hf (by decide) h N

/-- **`[7 [[0 1] [0 1]] [2 [0 3] [0 2]]]` end to end** (`%s7b`): the call is
`q`, under `%done`, and the cons `p` runs under its result goal. -/
theorem seven_exampleB {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hfol : bl.fol = n3 (A 7) (C (slot 1) (slot 1)) (n3 (A 2) (slot 3) (slot 2))) {env : CallEnv}
    {cd : Straight Map}
    (h : finishLUC (S := S) env (Nomm.n7 (Nomm.cons (Nomm.n0 1) (Nomm.n0 1))
      (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) = some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have hA : Annot lib code (SkaModel.Fits bl.less) bl.fol
      (Nomm.n7 (Nomm.cons (Nomm.n0 1) (Nomm.n0 1)) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) := by
    rw [hfol]
    exact Annot.n7 (Annot.cons Annot.n0 Annot.n0) (Annot.indirect Annot.n0 Annot.n0)
  have hf : FragUF S (Nomm.n7 (Nomm.cons (Nomm.n0 1) (Nomm.n0 1)) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) :=
    Or.inr (FragI.sevenU (FragU.cons (FragU.x (FragX.frag fun _ => trivial)) (FragU.x (FragX.frag fun _ => trivial)))
      fragI_ind00 noEntF_ind00)
  exact finishLUC_contractUF hok hA hf (by decide) h N

/-- **`[8 [2 [0 3] [0 2]] [4 [0 2]]]` end to end** (`%e8a`, the `n8` form):
the call in the pushed pair. -/
theorem eight_exampleA {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hfol : bl.fol = n3 (A 8) (n3 (A 2) (slot 3) (slot 2)) (n2 (A 4) (slot 2))) {env : CallEnv}
    {cd : Straight Map}
    (h : finishLUC (S := S) env (Nomm.n7 (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1))
      (Nomm.n4 (Nomm.n0 2))) = some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have hA : Annot lib code (SkaModel.Fits bl.less) bl.fol
      (Nomm.n7 (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1)) (Nomm.n4 (Nomm.n0 2))) := by
    rw [hfol]
    exact Annot.n8 (Annot.indirect Annot.n0 Annot.n0) (Annot.n4 Annot.n0)
  have hf : FragUF S (Nomm.n7 (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1))
      (Nomm.n4 (Nomm.n0 2))) :=
    Or.inr (FragI.weak (FragI.sevenPU (FragI.consH fragI_ind00 (FragU.x (FragX.frag fun _ => trivial)))
      (FragU.four (FragU.x (FragX.frag fun _ => trivial))) (NoEntF.pure rfl rfl)))
  exact finishLUC_contractUF hok hA hf (by decide) h N

/-- **`[8 [0 3] [2 [0 2] [0 6]]]` end to end** (`%e8b`, the `n8` form): the
call in the body. -/
theorem eight_exampleB {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hfol : bl.fol = n3 (A 8) (slot 3) (n3 (A 2) (slot 2) (slot 6))) {env : CallEnv}
    {cd : Straight Map}
    (h : finishLUC (S := S) env (Nomm.n7 (Nomm.cons (Nomm.n0 3) (Nomm.n0 1))
      (Nomm.n2 (Nomm.n0 2) (Nomm.n0 6) Option.none)) = some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have hA : Annot lib code (SkaModel.Fits bl.less) bl.fol
      (Nomm.n7 (Nomm.cons (Nomm.n0 3) (Nomm.n0 1)) (Nomm.n2 (Nomm.n0 2) (Nomm.n0 6) Option.none)) := by
    rw [hfol]
    exact Annot.n8 Annot.n0 (Annot.indirect Annot.n0 Annot.n0)
  have hf : FragUF S (Nomm.n7 (Nomm.cons (Nomm.n0 3) (Nomm.n0 1)) (Nomm.n2 (Nomm.n0 2) (Nomm.n0 6) Option.none)) :=
    Or.inr (FragI.sevenU (FragU.cons (FragU.x (FragX.frag fun _ => trivial)) (FragU.x (FragX.frag fun _ => trivial)))
      fragI_ind00 noEntF_ind00)
  exact finishLUC_contractUF hok hA hf (by decide) h N

/-- **`[9 2 [0 1]]` end to end** (`%e9a`, the `n9` form): the arm's call. -/
theorem nine_exampleA {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hfol : bl.fol = n3 (A 9) (A 2) (slot 1)) {env : CallEnv} {cd : Straight Map}
    (h : finishLUC (S := S) env (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none)) = some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have hA : Annot lib code (SkaModel.Fits bl.less) bl.fol
      (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none)) := by
    rw [hfol]
    exact Annot.n9 Annot.n0 (Annot.indirect Annot.n0 Annot.n0)
  have hf : FragUF S (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none)) :=
    Or.inr (FragI.weak (FragI.sevenJ JNewQ.n0 fragI_ind00 noEntF_ind00))
  exact finishLUC_contractUF hok hA hf (by decide) h N

/-- **`[9 2 [2 [0 3] [0 2]]]` end to end** (`%e9b`, the `n9` form): both the
core's formula and the arm call. -/
theorem nine_exampleB {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hfol : bl.fol = n3 (A 9) (A 2) (n3 (A 2) (slot 3) (slot 2))) {env : CallEnv} {cd : Straight Map}
    (h : finishLUC (S := S) env (Nomm.n7 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)
      (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none)) = some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have hA : Annot lib code (SkaModel.Fits bl.less) bl.fol
      (Nomm.n7 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none)) := by
    rw [hfol]
    exact Annot.n9 (Annot.indirect Annot.n0 Annot.n0) (Annot.indirect Annot.n0 Annot.n0)
  have hf : FragUF S (Nomm.n7 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)
      (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none)) :=
    Or.inr (FragI.weak (FragI.sevenPF fragI_ind00 (fragI_ind00 (S := S)) noEntF_ind00))
  exact finishLUC_contractUF hok hA hf (by decide) h N

/-- **`[7 [7 [0 1] [2 [0 3] [0 2]]] [4 [0 1]]]` end to end** (`%s7n`): a
`[7 p q]` whose `p` is a `[7 p q]` that calls. -/
theorem seven_exampleN {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hfol : bl.fol = n3 (A 7) (n3 (A 7) (slot 1) (n3 (A 2) (slot 3) (slot 2))) (n2 (A 4) (slot 1)))
    {env : CallEnv} {cd : Straight Map}
    (h : finishLUC (S := S) env (Nomm.n7 (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none))
      (Nomm.n4 (Nomm.n0 1))) = some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have hA : Annot lib code (SkaModel.Fits bl.less) bl.fol
      (Nomm.n7 (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) (Nomm.n4 (Nomm.n0 1))) := by
    rw [hfol]
    exact Annot.n7 (Annot.n7 Annot.n0 (Annot.indirect Annot.n0 Annot.n0)) (Annot.n4 Annot.n0)
  have hf : FragUF S (Nomm.n7 (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none))
      (Nomm.n4 (Nomm.n0 1))) :=
    Or.inr (FragI.weak (FragI.sevenPU (FragI.sevenJ JNewQ.n0 fragI_ind00 noEntF_ind00)
      (FragU.four (FragU.x (FragX.frag fun _ => trivial))) (NoEntF.pure rfl rfl)))
  exact finishLUC_contractUF hok hA hf (by decide) h N

/-- **`[[0 1] [7 [0 1] [2 [0 3] [0 2]]]]` end to end** (`%s7t`): a `[7 p q]`
that calls as the tail of a cons (its `EntNew`, the head under the bond
goal). -/
theorem seven_exampleT {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hfol : bl.fol = C (slot 1) (n3 (A 7) (slot 1) (n3 (A 2) (slot 3) (slot 2)))) {env : CallEnv}
    {cd : Straight Map}
    (h : finishLUC (S := S) env (Nomm.cons (Nomm.n0 1)
      (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none))) = some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have hA : Annot lib code (SkaModel.Fits bl.less) bl.fol
      (Nomm.cons (Nomm.n0 1) (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none))) := by
    rw [hfol]
    exact Annot.cons Annot.n0 (Annot.n7 Annot.n0 (Annot.indirect Annot.n0 Annot.n0))
  have hf : FragUF S (Nomm.cons (Nomm.n0 1) (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none))) :=
    Or.inr (FragI.weak (FragI.consT (FragB.n0 (by decide)) (FragI.sevenJ JNewQ.n0 fragI_ind00 noEntF_ind00)))
  exact finishLUC_contractUF hok hA hf (by decide) h N

end Comp
end SkaModel
end Formalization
