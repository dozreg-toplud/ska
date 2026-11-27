import lemmas.Compiler.CompLeapLazyGate
import lemmas.Compiler.CompRunSixNext

/-!
# `+leap` of the door of `+comp` on every lazy need

`+leap` (door arm `441179`, `lpxBat`, the same noun as track A's `lp6Bat`)
on `[laz q r]`:

    ?:  &(?=(~ fork.laz) ?=(~ bond.laz))  ~
    =/  pas  (pass-both q r)
    =/  lab  [*sure fork.laz bond.laz]
    =|  bys
    |-  ?~  pas  ?~(bys ~ `[[sure.laz fork.lab bond.lab] bys])
    =/  [by rec]  (lazy-leap p.i.pas s.i.pas lab)
    ?:  (lazy-empty by)  $(pas t.pas)
    $(pas t.pas, lab rec, bys [by bys])

`+pass-both` is K arm `94` (`pbt_gate`: a list of parts with no axis `0`),
`+lazy-leap` door arm `442366` (`lzl_gate`, on a lazy need whose looks are
not `0`, which `lzl_lall` keeps for `rec`), `+lazy-empty` door arm `54`
(`le_gate`).  The trap is `lpxL1` (`lpx_loop`, by induction on the parts:
`leapLoop`).  The model `leap` takes the same branches in the same order: no
departure.

`lpx_gate`: `+leap` is `leap` on every lazy need whose looks are not `0` and
nomms with no `%10` at axis `0`, in every door core whose context has `K` at
`7`.  `lp6_leap` states it on `lp6Bat` and `compCore`, the form of `hLp` in
`comp_run_n6_k`; `lp6_leap_none` is that `hLp`, from `hlp`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.Ana

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- The noun of what `+leap` returns. -/
noncomputable def leapN : Option (Lazy CSet × List (Lazy CSet)) → Noun :=
  unitNoun fun x => C x.1.toNoun (listN (x.2.map Lazy.toNoun))

theorem lN_nil : lN [] = A 0 := rfl

theorem lN_cons (p s : Nat) (l : List (Nat × Nat)) : lN ((p, s) :: l) = C (C (A p) (A s)) (lN l) := rfl

theorem listN_lazy_cons (b : Lazy CSet) (l : List (Lazy CSet)) :
    listN ((b :: l).map Lazy.toNoun) = C b.toNoun (listN (l.map Lazy.toNoun)) := rfl

/-- **The loop of `+leap`** (`lpxL1`) is `leapLoop`, on lists of parts with no
axis `0` and lazy needs whose looks are not `0`. -/
theorem lpx_loop (hc : CompIn ctx) (hl : CompLib ctx) (G B X Y : Noun) (sur : Sure CSet) :
    ∀ (pas : List (Nat × Nat)) (lab : Lazy CSet) (bys : List (Lazy CSet)), PosL pas → LAll CrLok lab →
    nock (C lpxL1 (C (listN (bys.map Lazy.toNoun)) (C lab.toNoun (C (lN pas)
      (C B (C (C (C sur.toNoun Y) X) (C comp.door (C G ctx)))))))) lpxL1
      = (leapLoop sur pas lab bys).map leapN := by
  have hz := lzl_at
  have he := comp_le_at
  intro pas
  induction pas with
  | nil =>
    intro lab bys _ _
    obtain ⟨ls, lf, lb⟩ := lab
    rw [lN_nil, lazy_toNoun_mk]
    generalize comp.door = Dr at hz he ⊢
    nock_open lpxL1
    cases bys with
    | nil => simp [nock_exec, leapLoop, leapN, unitNoun]
    | cons b bs =>
      rw [listN_lazy_cons]
      simp [nock_exec, leapLoop, leapN, unitNoun, lazy_toNoun_mk, Lazy.fork, Lazy.bond]
  | cons e rest ih =>
    intro lab bys hpos hlab
    obtain ⟨p, s⟩ := e
    have hp : p ≠ 0 := (hpos (p, s) List.mem_cons_self).1
    have hs : s ≠ 0 := (hpos (p, s) List.mem_cons_self).2
    have hrest : PosL rest := fun x hx => hpos x (List.mem_cons_of_mem _ hx)
    have hg := lzl_gate hc hl G hlab hp hs
    rw [lN_cons]
    cases e1 : lazyLeap p s lab with
    | none =>
      rw [e1] at hg
      generalize comp.door = Dr at hz he hg ⊢
      nock_open lpxL1
      simp [nock_exec, hz, lzl_arm, hg, leapLoop, e1]
    | some br =>
      obtain ⟨b, r⟩ := br
      rw [e1] at hg
      simp only [Option.map_some] at hg
      have hle := le_gate b (C comp.door (C G ctx))
      have ih1 := ih lab bys hrest hlab
      have ih2 := ih r (b :: bys) hrest (lzl_lall hp hs hlab e1).2
      rw [listN_lazy_cons] at ih2
      generalize comp.door = Dr at hz he hg hle ih1 ih2 ⊢
      nock_open lpxL1
      cases eb : Lazy.lazyEmpty b with
      | true =>
        rw [eb] at hle
        simp [nock_exec, hz, lzl_arm, hg, he, comp_le_arm, hle, loob, ih1, leapLoop, e1, eb]
      | false =>
        rw [eb] at hle
        simp [nock_exec, hz, lzl_arm, hg, he, comp_le_arm, hle, loob, ih2, leapLoop, e1, eb]

/-- The battery of `+leap` is track A's `lp6Bat`. -/
theorem lp6_lpx : lp6Bat = lpxBat := by kernel_rfl

/-- **`+leap`** is `leap` on every lazy need whose looks are not `0` and
nomms with no `%10` at axis `0`, crashes included, in every door core whose
context has `K` at `7`. -/
theorem lpx_gate (h7 : slot? 7 ctx = some compK) (G : Noun) (laz : Lazy CSet) (q r : Nomm)
    (hl : LAll CrLok laz) (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r) :
    nock (C lpxBat (C (C laz.toNoun (C q.toNoun r.toNoun)) (C comp.door (C G ctx)))) lpxBat
      = (leap laz q r).map leapN := by
  obtain ⟨hc, hcl, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨pas, hpb, hpos, hpn⟩ := pbt_gate passIn_compK q r hq hr
  obtain ⟨sur, fk, bd⟩ := laz
  have hlab : LAll CrLok (Lazy.mk Sure.bunt fk bd) :=
    ⟨fun y hy => absurd hy (HoonSet.mem_empty y), hl.2.1, hl.2.2⟩
  have hb : (Lazy.mk (Sure.bunt : Sure CSet) fk bd).toNoun
      = C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (listN (fk.map forkE)) (listN (bd.map bondE))) := by
    rw [lazy_toNoun_mk]; simp [Sure.toNoun, Sure.bunt, Need.toNoun, Tag.none, HoonSet.toNoun_empty]
  have hlp := lpx_loop hc hcl G lpxBat (C q.toNoun r.toNoun) (C (listN (fk.map forkE)) (listN (bd.map bondE)))
    sur pas (Lazy.mk Sure.bunt fk bd) [] hpos hlab
  rw [hb, List.map_nil, show listN ([] : List Noun) = A 0 from rfl] at hlp
  have hpa := pbt_at
  rw [lazy_toNoun_mk]
  generalize comp.door = Dr at hlp ⊢
  have tF := lz_test forkE fk
  have tB := lz_test bondE bd
  conv => lhs; arg 2; unfold lpxBat
  rcases tF with ⟨t1, t2, t3⟩ | ⟨t1, t2, t3⟩ <;> rcases tB with ⟨t4, t5, t6⟩ | ⟨t4, t5, t6⟩
  · subst t1; subst t4
    simp [nock_exec, leap, leapN, unitNoun, Lazy.fork, Lazy.bond]
  all_goals
    first | replace t1 := eq_false t1 | replace t1 := eq_true t1
    first | replace t4 := eq_false t4 | replace t4 := eq_true t4
    simp [nock_exec, leap, Lazy.fork, Lazy.bond, Lazy.sure, t1, t2, t3, t4, t5, t6, List.isEmpty_iff, h7,
      hpa, pbt_arm, hpn, hpb, hlp]

/-- **`+leap`** on `lp6Bat` and the door core of a state (`compCore`), the
form of the hypothesis `hLp` of `comp_run_n6_k`: the model `leap laz q r`
and the Nock of `lp6Bat` on the same inputs. -/
theorem lp6_leap (h7 : slot? 7 ctx = some compK) (laz : Lazy CSet) (q r : Nomm) (hl : LAll CrLok laz)
    (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r) (g : Gen (TreapMap mugF)) (x : GenRest) :
    nock (C lp6Bat (C (C laz.toNoun (C q.toNoun r.toNoun)) (compCore g x ctx))) lp6Bat
      = (leap laz q r).map leapN := by
  rw [lp6_lpx]; exact lpx_gate h7 _ laz q r hl hq hr

/-- **The hypothesis `hLp` of `comp_run_n6_k`** from `hlp`: where the model's
`+leap` is `~`, so is the Nock's. -/
theorem lp6_leap_none (h7 : slot? 7 ctx = some compK) {laz : Lazy CSet} {q r : Nomm} (hl : LAll CrLok laz)
    (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r) (g : Gen (TreapMap mugF))
    (hlp : leap laz q r = some Option.none) : ∀ x : GenRest, x.NoSoft →
    nock (C lp6Bat (C (C laz.toNoun (C q.toNoun r.toNoun)) (compCore g x ctx))) lp6Bat = some (A 0) := by
  intro x _
  rw [lp6_leap h7 laz q r hl hq hr g x, hlp]; rfl

end Compiler
end Formalization
