import lemmas.Compiler.FolLoopLink
import lemmas.Compiler.GitMi
import lemmas.Compiler.FolLoopFacts

/-!
The case `[%2 p=^ q=*]` of the trap `fol-loop` against `Ana.callStep`
(`fol_loop_op2`), and so one level of the trap on every formula
(`fol_loop_step_all`).

After the two calls for `p` and `q` the battery takes the void branch, the
indirect branch (`indi` and `seek` widened through `+uni:ca` and
`+distribute`), the inline branch (a call of the trap to itself, through
`GoIs`, with `+inlineable` at axis `763` of `ana` and `+safe-fol-fol`), or
kicks the trap `nock-2-direct-non-inlined` (`fol_loop.direct`) on
`[fol-new [f [s subject]]]` (`dirSubj`).  That trap runs the loop
`resolve` on `[id-there trap]` and then widens `want`, `indi`, `seek` and puts
`[seat id-there]` into `callees` with `+put:in` (`fol_loop_direct`).

The loop `resolve` is the parameter `res`, tied to the pill by `ResIs`: run
from the trap with `id-there` set to `[sock.prod.s fol-new]`, the loop returns
`res` of that identity.  `CalleePutIs` says that `+put:in` on the noun of a
set of callee entries is the noun of `Treap.ins`; it is a statement about
nouns only (no Nock), left open here.

Found while reading the loop: `resolve` asks `+git:mi` with `fol-new` and
`sock.prod.s` of the trap, not with the current `id-there`.  After a `%he`
generalization (`resolve(id-there +.u.par)`) the memo is still asked for the
original subject sock, while `Ana.resolveStep` asks with the generalized one.
So `ResIs` holds of `Ana.resolve` only on runs with no `%he` before a memo
lookup; on the first turn of the loop the two agree.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

/-- The noun of a result of `resolve`: `[[identity datum] gen]`. -/
noncomputable def resOutNoun (regsNoun : R → Noun) (r : (Ident × FDatum FinMap) × GenS FinMap R) : Noun :=
  C (entryNoun r.1) (r.2.toNoun regsNoun)

/-- The subject of the trap `nock-2-direct-non-inlined`. -/
noncomputable def dirSubj (regsNoun : R → Noun) (rest fol : Noun) (sub : Anno) (seat mk : Option Noun)
    (bc df : Bool) (gen : GenS FinMap R) (fn fN sN : Noun) : Noun :=
  C fol_loop.direct (C fn (C fN (C sN (folSubj regsNoun rest fol sub seat mk bc df gen))))

/-- The loop `resolve`, entered from the trap with `id-there` `[sock.prod.s fol-new]`,
computes `res`. -/
def ResIs (regsNoun : R → Noun) (rest : Noun) (res : ResGo FinMap R) : Prop :=
  ∀ (s f : FolOut) (fa fb fol : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool)
    (gen : GenS FinMap R),
    nock (C fol_loop.resolve (C (identNoun (s.prod.sock, C fa fb))
        (dirSubj regsNoun rest fol sub seat mk bc df gen (C fa fb) f.toNoun s.toNoun)))
        fol_loop.resolve
      = (res (s.prod.sock, C fa fb) gen).map (resOutNoun regsNoun)

/-- `+put:in` on the noun of a set of callee entries. -/
def CalleePutIs : Prop :=
  ∀ (m : FinMap CalleeEntry Unit) (k : CalleeEntry),
    putInF mugF k.toNoun (Treap.setNoun m) = some (Treap.setNoun (Treap.ins m k))

theorem rest_layer2 {rest : Noun} (h : slot? 511 rest = some ana) :
    slot? 2097151 rest = some layer2 := by
  have h' : slot? 511 rest = slot? 1 ana := by rw [h]; rfl
  have := slot_spine (by omega) (by omega) h' 12
  simp only [show 2 ^ 12 * (511 + 1) - 1 = 2097151 from rfl,
    show 2 ^ 12 * (1 + 1) - 1 = 8191 from rfl] at this
  rw [this]; exact ana_layer2

set_option maxHeartbeats 1000000 in
/-- The trap `nock-2-direct-non-inlined`: `resolve`, the `?>` that the code
requirement is a cell, and the widening of `gen`. -/
theorem fol_loop_direct (regsNoun : R → Noun) (res : ResGo FinMap R) (rest : Noun)
    (hana : slot? 511 rest = some ana) (hres : ResIs regsNoun rest res) (hput : CalleePutIs)
    (s f : FolOut) (fa fb fol : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool)
    (gen : GenS FinMap R) :
    nock (dirSubj regsNoun rest fol sub seat mk bc df gen (C fa fb) f.toNoun s.toNoun) fol_loop.direct
      = ((res (s.prod.sock, C fa fb) gen).bind fun r =>
          match r.1.2.less with
          | Sock.void => none
          | Sock.mk lc _ =>
            some (⟨Nomm.n2 s.nomm f.nomm (some (⟨r.1.2.less, C fa fb⟩, mk)),
                ⟨r.1.2.prod, Pi.compose r.1.2.map s.prod.src⟩, false⟩,
              { r.2 with
                want := Ca.uni r.2.want (Ca.uni (distribute Cape.yes f.prod.src)
                  (distribute lc s.prod.src)),
                indi := Ca.uni r.2.indi (distribute r.1.2.indi s.prod.src),
                seek := Ca.uni r.2.seek (distribute r.1.2.seek s.prod.src),
                callees := Treap.ins r.2.callees ⟨seat, r.1.1⟩ })).map (folOutNoun regsNoun) := by
  have hr := hres s f fa fb fol sub seat mk bc df gen
  have hl2 := rest_layer2 hana
  have hlib := rest_lib hana
  unfold dirSubj at hr ⊢
  unfold folSubj at hr ⊢
  obtain ⟨ms, ⟨ss, srcs⟩, fs⟩ := s
  obtain ⟨mf, ⟨sf, srcf⟩, ff⟩ := f
  simp only [FolOut.toNoun, Anno.toNoun, identNoun] at hr ⊢
  generalize flag df = n1 at hr ⊢
  generalize flag bc = n2 at hr ⊢
  generalize hn3 : unitNoun id mk = n3 at hr ⊢
  generalize hn4 : unitNoun id seat = n4 at hr ⊢
  generalize GenS.toNoun regsNoun gen = n5 at hr ⊢
  generalize sub.toNoun = n6 at hr ⊢
  generalize ss.toNoun = nss at hr ⊢
  generalize sf.toNoun = nsf at hr ⊢
  generalize hms : ms.toNoun = nms at hr ⊢
  generalize hmf : mf.toNoun = nmf at hr ⊢
  generalize flag fs = nfs at hr ⊢
  generalize flag ff = nff at hr ⊢
  nock_open fol_loop.direct
  cases e : res (ss, C fa fb) gen with
  | none =>
    rw [e] at hr
    simp [nock_exec, hr]
  | some r =>
    rw [e] at hr
    obtain ⟨⟨i, d⟩, g⟩ := r
    simp only [Option.map_some, resOutNoun, entryNoun] at hr
    have hp : putInF mugF (C (unitNoun id seat) (identNoun i)) (Treap.setNoun g.callees)
        = some (Treap.setNoun (Treap.ins g.callees ⟨seat, i⟩)) := hput _ ⟨seat, i⟩
    have hpg := put_in_gate layer2 gorIn_morIn_layer2 _ _ _ hp
    rw [hn4] at hpg
    obtain ⟨cl, nd, less, di, dk, dp, dm, da⟩ := d
    simp only [FDatum.toNoun, identNoun, GenS.toNoun] at hr hpg ⊢
    generalize hgs : g.st.toNoun regsNoun = ngs at hr ⊢
    generalize hgb : flag g.back = ngb at hr ⊢
    generalize hga : unitNoun (fun x => x) g.area = nga at hr ⊢
    generalize Treap.setNoun cl = ncl at hr ⊢
    generalize nd.toNoun = nnd at hr ⊢
    generalize hdp : dp.toNoun = ndp at hr ⊢
    generalize unitNoun (fun x => x) da = nda at hr ⊢
    cases less with
    | void =>
      simp [nock_exec, hr, sock_void_toNoun]
    | mk lc ld =>
      have hu1 := distribute_pill Cape.yes srcf
      rw [cape_yes_toNoun] at hu1
      have hu2 := distribute_pill lc srcs
      have hu3 := distribute_pill di srcs
      have hu4 := distribute_pill dk srcs
      have hc1 := ca_uni_pill (distribute Cape.yes srcf) (distribute lc srcs)
      have hc2 := ca_uni_pill g.want (Ca.uni (distribute Cape.yes srcf) (distribute lc srcs))
      have hc3 := ca_uni_pill g.indi (distribute di srcs)
      have hc4 := ca_uni_pill g.seek (distribute dk srcs)
      have hcp := pi_compose_pill dm srcs
      simp [nock_exec, hr, sock_mk_toNoun, hl2, hlib, hpg, hu1, hu2, hu3, hu4, hc1, hc2, hc3, hc4, hcp,
        in.arm_at, in_arm, in.put.arm_at, put_in_arm, ca.lib.arm_at, ca_lib_arm, ca.uni.arm_at,
        ca_uni_arm, distribute.arm_at, distribute_arm, pi.lib.arm_at, pi_lib_arm, pi.compose.arm_at,
        pi_compose_arm, folOutNoun, FolOut.toNoun, Anno.toNoun, Nomm.toNoun, GenS.toNoun, hgs, flag]
      subst hms hmf hn3 hdp hga hgb
      simp [unitNoun, flag, Bell.toNoun, sock_mk_toNoun]

theorem rest_1023 {rest : Noun} (h : slot? 511 rest = some ana) :
    ∃ x, slot? 262143 rest = some x := by
  have h' : slot? 511 rest = slot? 1 ana := by rw [h]; rfl
  have := slot_spine (by omega) (by omega) h' 9
  simp only [show 2 ^ 9 * (511 + 1) - 1 = 262143 from rfl,
    show 2 ^ 9 * (1 + 1) - 1 = 1023 from rfl] at this
  rw [this]
  have hs := ana_1023_some
  cases e : slot? 1023 ana with
  | none => rw [e] at hs; cases hs
  | some x => exact ⟨x, rfl⟩

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `[%2 p=^ q=*]`: a call, through the inline branch, the trap
`nock-2-direct-non-inlined` (given `ResIs`), or an indirect call. -/
theorem fol_loop_op2 (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIs regsNoun rest go)
    (hana : slot? 511 rest = some ana) (hres : ResIs regsNoun rest res) (hput : CalleePutIs)
    (a b q : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nock (folSubj regsNoun rest (C (A 2) (C (C a b) q)) sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go (C (A 2) (C (C a b) q)) sub seat mk bc df gen).map
          (folOutNoun regsNoun) := by
  have h := hgo (C a b) sub seat mk bc df gen
  have hlib := rest_lib hana
  have hl2 := rest_layer2 hana
  obtain ⟨x1023, hx⟩ := rest_1023 hana
  unfold folSubj at h ⊢
  nock_open fol_loop.battery
  cases e : go (C a b) sub seat mk bc df gen with
  | none =>
    rw [e] at h
    simp [nock_exec, Ana.folStep, shape, e, h]
  | some r =>
    rw [e] at h
    obtain ⟨o, g⟩ := r
    have h2 := hgo q sub seat mk bc df g
    unfold folSubj at h2
    simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h
    generalize hn1 : flag df = n1 at h h2 ⊢
    generalize hn2 : flag bc = n2 at h h2 ⊢
    generalize hn3 : unitNoun id mk = n3 at h h2 ⊢
    generalize hn4 : unitNoun id seat = n4 at h h2 ⊢
    generalize GenS.toNoun regsNoun gen = n5 at h ⊢
    generalize hn6 : sub.toNoun = n6 at h h2 ⊢
    cases e2 : go q sub seat mk bc df g with
    | none =>
      rw [e2] at h2
      simp [nock_exec, Ana.folStep, shape, e, h, e2, h2]
    | some r2 =>
      rw [e2] at h2
      obtain ⟨o2, g2⟩ := r2
      simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h2
      obtain ⟨m1, ⟨s1, src1⟩, f1⟩ := o
      obtain ⟨m2, ⟨s2, src2⟩, f2⟩ := o2
      simp only [Anno.toNoun] at h h2
      generalize hm1 : m1.toNoun = nm1 at h h2 ⊢
      generalize hm2 : m2.toNoun = nm2 at h h2 ⊢
      generalize hf1 : flag f1 = nf1 at h h2 ⊢
      generalize hf2 : flag f2 = nf2 at h h2 ⊢
      generalize GenS.toNoun regsNoun g = n7 at h h2 ⊢
      rcases s1 with _ | ⟨c1, d1⟩
      · simp only [sock_void_toNoun] at h
        simp [nock_exec, Ana.folStep, shape, Ana.callStep, e, h, e2, h2, Tag.void, folOutNoun, FolOut.toNoun,
          Nomm.toNoun, Anno.toNoun, sock_void_toNoun, hm1, hm2, flag, unitNoun]
      rcases s2 with _ | ⟨c2, d2⟩
      · simp only [sock_void_toNoun, sock_mk_toNoun] at h h2
        simp [nock_exec, Ana.folStep, shape, Ana.callStep, e, h, e2, h2, Tag.void, folOutNoun, FolOut.toNoun,
          Nomm.toNoun, Anno.toNoun, sock_void_toNoun, hm1, hm2, flag, unitNoun]
      simp only [sock_mk_toNoun] at h h2
      simp only [GenS.toNoun] at h2
      generalize hcal : Treap.setNoun g2.callees = ncal at h2 ⊢
      generalize hare : unitNoun (fun x => x) g2.area = nare at h2 ⊢
      generalize hbk : flag g2.back = nbk at h2 ⊢
      generalize hst : SkaState.toNoun regsNoun g2.st = nst at h2 ⊢
      have hu := distribute_pill Cape.yes src2
      rw [cape_yes_toNoun] at hu
      have hci := ca_uni_pill g2.indi (distribute Cape.yes src2)
      have hcs := ca_uni_pill g2.seek (distribute Cape.yes src2)
      have hcw := ca_uni_pill g2.want (distribute Cape.yes src2)
      rcases c2 with _ | _ | ⟨p2, q2⟩ <;> rcases d2 with x2 | ⟨fa, fb⟩ <;> cases bc <;>
        simp [flag] at hn2 <;> subst hn2
      all_goals first
        | (simp [nock_exec, Ana.folStep, shape, Ana.callStep, e, h, e2, h2, Tag.void, hlib,
            ca.lib.arm_at, ca_lib_arm, ca.uni.arm_at, ca_uni_arm, distribute.arm_at, distribute_arm,
            hu, hci, hcs, folOutNoun, FolOut.toNoun, Nomm.toNoun, Anno.toNoun, Anno.dunno, Sock.dunno,
            Sock.toNoun, Cape.toNoun, GenS.toNoun, hm1, hm2, hcal, hare, hbk, hst, flag, unitNoun] <;>
            (subst hare hbk; simp [unitNoun, flag]); done)
        | skip
      subst hn1 hn3
      have hi := inlineable_gate' ana (C fa fb)
      have hsf := safe_fol_fol_pill m2
      rw [hm2] at hsf
      have hf0 : flag false = A 1 := rfl
      have hf1' : flag true = A 0 := rfl
      have hu0 : unitNoun id (none : Option Noun) = A 0 := rfl
      have hus : ∀ x : Noun, unitNoun id (some x) = C (A 0) x := fun _ => rfl
      have hd := fol_loop_direct regsNoun res rest hana hres hput ⟨m1, ⟨Sock.mk c1 d1, src1⟩, f1⟩
        ⟨m2, ⟨Sock.mk Cape.yes (C fa fb), src2⟩, f2⟩ fa fb (C (A 2) (C (C a b) q)) sub seat mk false df g2
      unfold dirSubj folSubj at hd
      rw [hn6] at hd
      cases ei : inlineable (C fa fb) <;> cases es : safeFolFol m2 <;> cases df <;>
        rcases mk with _ | kx <;> rw [ei] at hi <;> rw [es] at hsf
      all_goals first
        | (simp only [FolOut.toNoun, Anno.toNoun, sock_mk_toNoun, GenS.toNoun, hcal, hare, hbk, hst, hm1,
             hm2, hf1, hf2, hn4, cape_yes_toNoun, hf0, hf1', hu0, hus] at hd
           simp only [hf0, hf1', hu0, hus] at h h2
           simp [nock_exec, Ana.folStep, shape, Ana.callStep, e, h, e2, h2, Tag.void, hlib,
            hana, hx, hd, hi, hsf, ei, es, inlineable.arm_at_ana, inlineable_arm, safe_fol_fol.arm_at,
            safe_fol_fol_arm, flag, unitNoun, Hoon.loob, cape_yes_toNoun]
           try rfl
           done)
        | skip
      case some.some.mk.mk.yes.cell.false.true.true.false.none =>
        simp only [hf0, hf1', hu0, hus] at h h2
        have h3 := hgo (C fa fb) ⟨Sock.mk c1 d1, src1⟩ seat none false false
          { g2 with want := Ca.uni g2.want (distribute Cape.yes src2) }
        unfold folSubj at h3
        simp only [Anno.toNoun, sock_mk_toNoun, GenS.toNoun, hcal, hare, hbk, hst, hn4, hf0, hu0] at h3
        cases e3 : go (C fa fb) ⟨Sock.mk c1 d1, src1⟩ seat none false false
            { g2 with want := Ca.uni g2.want (distribute Cape.yes src2) } with
        | none =>
          rw [e3] at h3
          simp [nock_exec, Ana.folStep, shape, Ana.callStep, e, h, e2, h2, h3, e3, Tag.void, hlib,
            hana, hi, hsf, ei, es, inlineable.arm_at_ana, inlineable_arm, safe_fol_fol.arm_at,
            safe_fol_fol_arm, flag, unitNoun, Hoon.loob, cape_yes_toNoun, ca.lib.arm_at, ca_lib_arm,
            ca.uni.arm_at, ca_uni_arm, distribute.arm_at, distribute_arm, hu, hcw]
        | some r3 =>
          rw [e3] at h3
          obtain ⟨⟨m3, p3, f3⟩, g3⟩ := r3
          simp only [Option.map_some, folOutNoun, FolOut.toNoun] at h3
          generalize hg3 : GenS.toNoun regsNoun g3 = ng3 at h3
          generalize hp3 : p3.toNoun = np3 at h3
          generalize hfl3 : flag f3 = nf3 at h3
          generalize hm3 : m3.toNoun = nm3 at h3
          simp [nock_exec, Ana.folStep, shape, Ana.callStep, e, h, e2, h2, h3, e3, Tag.void, hlib,
            hana, hi, hsf, ei, es, inlineable.arm_at_ana, inlineable_arm, safe_fol_fol.arm_at,
            safe_fol_fol_arm, flag, unitNoun, Hoon.loob, cape_yes_toNoun, ca.lib.arm_at, ca_lib_arm,
            ca.uni.arm_at, ca_uni_arm, distribute.arm_at, distribute_arm, hu, hcw, folOutNoun,
            FolOut.toNoun, Nomm.toNoun, hm1, hm3, hp3, hg3]

/-- One level of the trap is `Ana.folStep` on every formula, given its calls
to itself (`GoIs`), the loop `resolve` (`ResIs`), `+put:in` on callee sets
(`CalleePutIs`), `ana` at axis `511` of the rest of `+run`'s subject, and
`+soft-spot` and `+register-fast` as `env` says. -/
theorem fol_loop_step_all (regsNoun : R → Noun) (env : Env R) (res : ResGo FinMap R)
    (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIs regsNoun rest go)
    (hana : slot? 511 rest = some ana) (hsoft : SoftSpotIs env) (hreg : RegisterFastIs regsNoun env)
    (hres : ResIs regsNoun rest res) (hput : CalleePutIs)
    (fol : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nock (folSubj regsNoun rest fol sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go fol sub seat mk bc df gen).map (folOutNoun regsNoun) := by
  rcases shape_fol fol with hs | hs
  · exact fol_loop_step regsNoun env res go rest hgo hana hsoft hreg fol
      (fun a b q h => by rw [hs] at h; cases h) sub seat mk bc df gen
  · generalize hsh : shape fol = sh at hs
    subst hs
    by_cases h2 : ∃ a b q, sh = Shape.op2 a b q
    · obtain ⟨a, b, q, rfl⟩ := h2
      exact fol_loop_op2 regsNoun env res go rest hgo hana hres hput a b q sub seat mk bc df gen
    · have hn : ∀ a b q, shape sh.fol ≠ Shape.op2 a b q := fun a b q h => h2 ⟨a, b, q, hsh ▸ h⟩
      exact fol_loop_step regsNoun env res go rest hgo hana hsoft hreg _ hn sub seat mk bc df gen

end Compiler
end Formalization
