import lemmas.Compiler.RegisterFast
import lemmas.Compiler.SkaPoke
import lemmas.Compiler.FrameCall

/-!
# Every return of `+register-fast` is `[miss regs]` with a flag `miss`

The gate's battery has 18230 distinct cells (2 million as a tree, because
the traps of its prints quote types), so it is not run symbolically.  The
abstract interpreter of `FrameCall.lean` is run on it by the kernel instead,
from the base `S = [battery [[clue prod reg] ana]]` (shape `sub []`), with:

1. the resolver `rfK`, which knows the battery (paths under `[false]`) and
   `ana` (paths under `[true, true]`), so that a formula pulled from `ana` is
   a known noun;
2. three followed formulas (`rfFol`): the battery of `print-ska`
   (`[9 97710 0 255]`, axis `254` of `ana`), the arm `same` of layer 2 that it
   pulls (`[8 [1 0] [1 0 6] 0 1]`), and the battery `[0 6]` of the gate that
   `same` builds.  So `%-  (print-ska n |.(...))  gen` returns the shape of
   `gen`, and the trap of the print is never run;
3. two summaries, one for each loop, `past-loop` (`rfL1`, the battery at
   axis `1123630016355293` of the gate's battery) and `sock-loop` (`rfL2`, at
   axis `4602388546991284221`): on a core of the shape that the gate builds
   for the loop (`rfPre1`, `rfPre2`, with `gen` as `[%.n reg]`, that is
   `[1 reg]`, at its axis), every run returns `[0 *]` or `[1 *]`.

The kernel checks the two summaries (`rf_summ_ok`) and the run of the gate
(`rf_main_ok`: 287 shapes, each `[0 *]` or `[1 *]`), and `absNockS_sound`
turns them into `registerFastShape`.  With it `RegisterFastIs` holds for
every `Env Noun` whose `registerFast` is the pill's decoded run
(`registerFastIs_pill`), and the analysis part of `+ska-poke` is linked with
no hypothesis on `+register-fast` (`ska_poke_ana_iff_pill`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana Frame FrameCall

/-- The nouns of the base that the run may read as formulas: the battery and
`ana`. -/
def rfK : List Bool → Option Noun
  | false :: rest => slotAtPath register_fast.battery rest
  | true :: true :: rest => slotAtPath ana rest
  | _ => none

/-- The arm `same` of layer 2, `|*(* +<)`. -/
def rfSameF : Noun := C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) (C (A 0) (A 6))) (C (A 0) (A 1))))

/-- The battery of the gate `print-ska`. -/
def rfPsBat : Noun := C (A 9) (C (A 97710) (C (A 0) (A 255)))

/-- The formulas whose calls the run follows. -/
def rfFol (g : Noun) : Bool := g == C (A 0) (A 6) || g == rfSameF || g == rfPsBat

/-- The batteries of `past-loop` and `sock-loop`. -/
def rfL1 : Noun := (slot? 1123630016355293 register_fast.battery).getD (A 0)
def rfL2 : Noun := (slot? 4602388546991284221 register_fast.battery).getD (A 0)

/-- `gen` as the gate builds it, `[%.n reg]`. -/
def rfGen : Ab := .cell (.lit (A 1)) (.sub [true, false, true, true])

/-- The core of `past-loop`: its battery, `past`, `fore`, `batt`, `axis`, the
parent, `label`, the clue (all unknown), `prod`, `gen`, and the gate. -/
def rfPre1 : Ab :=
  let u : Ab := .unk
  .cell (.lit rfL1) (.cell u (.cell u (.cell u (.cell u (.cell u (.cell u
    (.cell (.sub [true, false, false, true]) (.cell rfGen (.sub [])))))))))

/-- The core of `sock-loop`: its battery, `socks`, `pax`, over the core of
`past-loop`. -/
def rfPre2 : Ab := .cell (.lit rfL2) (.cell .unk (.cell (.cell .unk .unk) rfPre1))

/-- What every run of the gate and of the two loops returns. -/
def rfPost : List Ab := [.cell (.lit (A 0)) .unk, .cell (.lit (A 1)) .unk]

def rfSm : List Summ := [⟨rfPre1, .lit rfL1, rfPost⟩, ⟨rfPre2, .lit rfL2, rfPost⟩]

def rfOK (r : Ab) : Bool := rfPost.any fun p => le r p

theorem rf_summ_ok : rfSm.all (summOK rfK rfFol rfSm 1000) = true := by kernel_rfl

theorem rf_main_ok :
    (absNockS rfK rfFol rfSm 1000 (.sub []) register_fast.battery).all rfOK = true := by
  kernel_rfl

theorem rfK_ok (s : Noun) : KOK (C register_fast.battery (C s ana)) rfK := by
  intro q n hq
  match q, hq with
  | false :: rest, hq => simpa [rfK, slotAtPath] using hq
  | true :: true :: rest, hq => simpa [rfK, slotAtPath] using hq

/-- **`RegisterFastShape`**: every return of the pill's `+register-fast` is
`[miss regs]` with a flag `miss`. -/
theorem registerFastShape : RegisterFastShape := by
  intro h f r x hx
  have he := nock_eq_some_iff.1 hx
  obtain ⟨s, hs, gs⟩ := absNockS_sound (rfK_ok (C h.toNoun (C f.toNoun r))) rf_summ_ok he 1000 (.sub [])
    (by simp [Ab.Gam, slotAtPath])
  have hok := List.all_eq_true.1 rf_main_ok s hs
  obtain ⟨p, hp, lp⟩ := List.any_eq_true.1 hok
  have gp := le_sound lp gs
  simp only [rfPost, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · obtain ⟨a, b, rfl, ga, -⟩ := gp
    simp only [Ab.Gam] at ga; subst ga
    exact ⟨true, b, rfl⟩
  · obtain ⟨a, b, rfl, ga, -⟩ := gp
    simp only [Ab.Gam] at ga; subst ga
    exact ⟨false, b, rfl⟩

/-- `RegisterFastIs` for every `Env Noun` whose `registerFast` is the pill's
decoded run, with no hypothesis left. -/
theorem registerFastIs_pill (env : Env Noun) (he : env.registerFast = registerFastP) :
    RegisterFastIs (fun x : Noun => x) env :=
  registerFastIs_of registerFastShape env he

/-- **The analysis part of `+ska-poke`** for registrations kept as nouns, with
`+register-fast` the pill's own decoded run: `ska_poke_ana_iff` with no
semantic hypothesis left on `+register-fast`. -/
theorem ska_poke_ana_iff_pill (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP)
    (root : Ident) (memo : Memo FinMap) (reg r1 r2 r3 r4 jRest lonRest hotN : Noun)
    (hregs : reg = C r1 (C r2 (C r3 (C r4 (A 0))))) (y : Noun) :
    nock (spT0 ana root r1 r2 r3 r4 jRest (memoNoun memo) lonRest hotN) spX = some y ↔
      ∃ n gr r, Ana.skaCallgraph env n root memo reg = some gr ∧
        Ana.skaPoke env n root memo reg = some r ∧
        nock (spAfter (fun x : Noun => x) root r1 r2 r3 r4 jRest lonRest hotN gr r) spRest
          = some y :=
  ska_poke_ana_iff (fun x : Noun => x) env hhe hth hsoft (registerFastIs_pill env hrf) root memo
    reg r1 r2 r3 r4 jRest lonRest hotN hregs y

end Compiler
end Formalization
