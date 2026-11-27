import lemmas.Ska.CompNaryTopDN
import lemmas.Ska.CompNaryTopSelf

/-!
# Tables of bells that call each other directly

README Gaps 18.15 (d) and step 4.  With the n-ary class `CallTreeDN`
(`CompNaryTopDN.lean`, generated) and the whole-subject class `CallTreeD`,
both with a direct call anywhere a member of track C's class may sit:

* `finishLFC_contractCallTreeDN`, `finishLFC_bellContractCallTreeDN`: the
  n-ary contract (`x = false`) of every member of `CallTreeDN`.
* `NeedsRead env T b`: the need `+callee-need` reads for `b` is the need of
  the table's n-ary entry of `b`, and the whole-subject entry exists.  This is
  the fixed point `+compile-scc-in` must deliver (Gaps 12 (a) to (d)): track
  I's `final_keeps` says that the entry the final pass puts for a member has
  the need its callers read (`map-local`), which is this statement with
  `env.need = map-local` and `T b false` the final entry.
* `tableOK_classes`: a table whose every n-ary entry is the code
  `finishLFC` of a member of `CallTreeDN`, and every whole-subject entry the
  code `finishLUCM` of a member of `CallTreeD`, each at the table's own needs
  and on the subjects of its bell, meets `TableOK`.  The needs equations the
  members' direct calls take are what `NeedsRead` gives (`NeedsRead.needs`).
* The walker: `walkF axe = [[0 3] [2 [[0 2] [0 7]] [0 axe]]]` on a subject
  `[hd x]` conses `x` onto the callee's product on `[hd x.tail]`, the callee
  fetched from the subject at `axe`, and crashes when `x` is an atom.  So a
  recursion through it ends, with a crash, after as many calls as `x` has
  cells along its tail.  `callTreeDN_walk` / `callTreeD_walk`: its nomm is in
  both classes for any callee with the same head `hd` and the need `[~ this]`.
* Closed theorems: `closed_selfWalk` (a self-recursive bell, `F = walkF 2`
  with `hd = F`) and `closed_pairWalk` (a mutually recursive pair, `A = walkF
  5`, `B = walkF 4` with `hd = [A B]`): on the table of their entries, each
  entry's code gives an answer at some number of levels exactly when `+mink`
  does, and the answers stand for each other (`ToneRel`), on every subject of
  the bell.  The hypotheses left are `NeedsRead` of each bell.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The n-ary contract of `CallTreeDN` and the table -/

/-- **The n-ary contract of `CallTreeDN`**: the n-ary code of every member
meets both halves of the contract for its formula, on every subject of `P`
with the cape's axes, entered with its split, for the class's needs. -/
theorem finishLFC_contractCallTreeDN (lib : Lib) {env : CallEnv} {N : Needs} {P : Noun → Prop} {x : Bool} {f : Noun}
    {nm : Nomm} (h : CallTreeDN lib env N P x f nm) {ord : NeedOrd} {less : Cape}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c : Straight Map}
    (hc : finishLFC (S := S) (Map := Map) env nm ord less bake = some c) :
    ∀ s, P s → CapeAxes less s → ∀ args, SkaModel.split c.need s = some args →
      ContractFwd lib N s f args c ∧ ContractBwd lib N s f args c :=
  finishLFC_contractGB lib N (fun hr => callTreeDN_done (S := S) (Map := Map) lib env h (by simp [gen0]) rfl
    upBelow_gen0 clear_gen0 condBelow_gen0 hr) hbake hc

/-- **The n-ary bell contract of `CallTreeDN`** (`x = false`), when nothing
is baked and the bell's cape has no `[| |]`. -/
theorem finishLFC_bellContractCallTreeDN {lib : Lib} {env : CallEnv} {N : Needs} {bl : Bell} {x : Bool} {nm : Nomm}
    (h : CallTreeDN lib env N (SkaModel.Fits bl.less) x bl.fol nm) {cape : Cape} {data : Noun}
    (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c : Straight Map}
    (hc : finishLFC (S := S) (Map := Map) env nm ord cape bake = some c) : BellContract lib N bl false c :=
  finishLFC_bellContractGB N (fun hr => callTreeDN_done (S := S) (Map := Map) lib env h (by simp [gen0]) rfl
    upBelow_gen0 clear_gen0 condBelow_gen0 hr) hbl hn hbake hc

/-- **The needs hypothesis of a table**: the need `+callee-need` reads for
`b` (`env.need b`) is the need of the table's n-ary entry for `b`, and the
whole-subject entry exists.  For the table `+compile-scc-in` produces for an
SCC, with `env.need` its `map-local`, this is what track I's `final_keeps`
gives (README Gaps 12, 18.15). -/
def NeedsRead (env : CallEnv) (T : Table Map) (b : Bell) : Prop :=
  ∃ cN cW, T b false = some cN ∧ T b true = some cW ∧ env.need b = some cN.need

/-- **What `NeedsRead` gives the direct calls of the classes**: the need read,
the n-ary entry's need in the table's needs, and some whole-subject need. -/
theorem NeedsRead.needs {env : CallEnv} {T : Table Map} {b : Bell} (h : NeedsRead env T b) :
    ∃ bNed ndT, env.need b = some bNed ∧ Table.needs T b false = some bNed ∧ Table.needs T b true = some ndT := by
  obtain ⟨cN, cW, h1, h2, h3⟩ := h
  exact ⟨cN.need, cW.need, h3, by simp [Table.needs, h1], by simp [Table.needs, h2]⟩

/-- **A table of members of the classes meets `TableOK`**: every n-ary entry
is the code `finishLFC` (nothing baked) of a member of `CallTreeDN`, and every
whole-subject entry the code `finishLUCM` of a member of `CallTreeD`, each at
the table's own needs, on the subjects of its bell, for its bell's formula,
with a cape that has no `[| |]`.  The members may call any bell of the table
(or outside it) directly: what their direct calls ask of the needs is in the
class, and `NeedsRead` of each callee gives it. -/
theorem tableOK_classes (lib : Lib) {T : Table Map}
    (hN : ∀ b c, T b false = some c → ∃ (env : CallEnv) (nm : Nomm) (x : Bool) (cape : Cape) (data : Noun)
      (ord : NeedOrd), b.less = Sock.mk cape data ∧ CapeNorm cape ∧
      CallTreeDN lib env (Table.needs T) (SkaModel.Fits b.less) x b.fol nm ∧
      finishLFC (S := S) env nm ord cape (fun ned => (ned, [])) = some c)
    (hW : ∀ b c, T b true = some c → ∃ (env : CallEnv) (nm : Nomm) (x : Bool),
      CallTreeD lib env (Table.needs T) (SkaModel.Fits b.less) x b.fol nm ∧ finishLUCM (S := S) env nm = some c) :
    TableOK lib T := by
  intro b m c hc
  cases m with
  | false =>
    obtain ⟨env, nm, x, cape, data, ord, hbl, hn, h, hf⟩ := hN b c hc
    exact finishLFC_bellContractCallTreeDN h hbl hn (fun _ => rfl) hf
  | true =>
    obtain ⟨env, nm, x, h, hf⟩ := hW b c hc
    exact (finishLUCM_bellContractCallTreeD h hf).2

/-- **A closed theorem for an entry of such a table**: on every subject of
its bell (split by the n-ary entry's need), the entry's code gives an answer
at some number of levels of the table's oracle exactly when `+mink` gives
one, and the two answers stand for each other. -/
theorem closed_entry (lib : Lib) {T : Table Map} (hT : TableOK lib T) {b : Bell} {m : Bool} {c : Straight Map}
    (hc : T b m = some c) {s : Noun} (hs : SkaModel.Fits b.less s) {args : List Noun}
    (ha : (if m then some [s] else SkaModel.split c.need s) = some args) (gul : Noun) :
    (∀ n r, minkF lib gul n [] s b.fol = some r →
      ∃ ton, execEntry lib (tableOracle lib T n) () c args [] gul = some (ton, ()) ∧
        ToneRel lib (Table.needs T) ton r) ∧
    (∀ k ton, execEntry lib (tableOracle lib T k) () c args [] gul = some (ton, ()) →
      ∃ r, Mink lib gul [] s b.fol r ∧ ToneRel lib (Table.needs T) ton r) :=
  have H := hT b m c hc s hs args ha
  table_closed lib hT (Needs.le_refl _) H.1 H.2 gul

/-! ## The walker -/

/-- `[[0 3] [2 [[0 2] [0 7]] [0 axe]]]`. -/
def walkF (axe : Nat) : Noun := C (slot 3) (n3 (A 2) (C (slot 2) (slot 7)) (slot axe))

/-- Its nomm: the call of `bl` (fetched at `axe`) on `[hd x.tail]`. -/
def walkNomm (axe : Nat) (bl : Bell) : Nomm :=
  Nomm.cons (Nomm.n0 3) (Nomm.n2 (Nomm.cons (Nomm.n0 2) (Nomm.n0 7)) (Nomm.n0 axe) (some (bl, Option.none)))

/-- The subjects `[hd *]`. -/
def walkSock (hd : Noun) : Sock := Sock.mk (Cape.cell Cape.yes Cape.no) (C hd (A 0))

/-- The need of the walker's n-ary entry: `[~ this]`. -/
def walkNeed : NeedOrd := NeedOrd.pair NeedOrd.none NeedOrd.this

theorem fits_walk {hd s : Noun} (h : SkaModel.Fits (walkSock hd) s) : ∃ x, s = C hd x := by
  simp only [walkSock, SkaModel.Fits, FitsCape] at h
  rcases h with h | ⟨dh, dt, nh, nt, e1, rfl, h1, -⟩
  · simp [Cape.isNo] at h
  · simp only [Noun.cell.injEq] at e1
    obtain ⟨rfl, rfl⟩ := e1
    exact ⟨nt, by rw [h1]⟩

theorem walk_fits (hd x : Noun) : SkaModel.Fits (walkSock hd) (C hd x) :=
  Or.inr ⟨hd, A 0, hd, x, rfl, rfl, rfl, trivial⟩

theorem splitsLess_walk {bl : Bell} {hd : Noun} (hl : bl.less = walkSock hd) : SplitsLess bl walkNeed :=
  fun s hs => by
    rw [hl] at hs
    obtain ⟨x, rfl⟩ := fits_walk hs
    exact ⟨[x], rfl⟩

/-- The products of `[[0 2] [0 7]]` on `[hd x]` are `[hd x.tail]`. -/
theorem walk_hAp {lib : Lib} {hd : Noun} {bl : Bell} (hl : bl.less = walkSock hd) :
    ∀ x gul y, SkaModel.Fits (walkSock hd) x → Mink lib gul [] x (C (slot 2) (slot 7)) (Tone.zero y) →
      SkaModel.Fits bl.less y := by
  intro x gul y hx ⟨n, hm⟩
  obtain ⟨w, rfl⟩ := fits_walk hx
  obtain ⟨n', -, rh, h2, H⟩ := minkF_consG ⟨_, _, rfl⟩ hm
  have e2 : rh = Tone.zero hd := by
    cases n' with
    | zero => simp [minkF] at h2
    | succ k => rw [minkF_succ_eq] at h2; simp only [minkStep_axis2, Option.some.injEq] at h2; exact h2.symm
  subst e2
  rcases H with ⟨hne, -⟩ | ⟨x1, e1, rt, -, H⟩
  · exact absurd rfl (hne hd)
  · cases e1
    rcases H with ⟨hne2, e⟩ | ⟨y2, -, e⟩
    · exact absurd e.symm (hne2 y)
    · cases e; rw [hl]; exact walk_fits hd y2

/-- **The walker's formula part** `[0 axe]`, when the subject's head holds
the callee's formula there. -/
theorem qDirect_walk {lib : Lib} {hd : Noun} {axe : Nat} {bl : Bell}
    (hslot : ∀ x gul go t, minkStep lib gul go t (C hd x) (slot axe) = some (Tone.zero bl.fol)) :
    QDirect lib (SkaModel.Fits (walkSock hd)) (Nomm.n0 axe) (slot axe) bl := by
  refine ⟨rfl, rfl, fun {s gul n tm rc} hs hm => ?_, fun {s gul tm} hs => ?_⟩
  · obtain ⟨x, rfl⟩ := fits_walk hs
    cases n with
    | zero => simp [minkF] at hm
    | succ k => rw [minkF_succ_eq, hslot] at hm; exact (Option.some.inj hm).symm
  · obtain ⟨x, rfl⟩ := fits_walk hs
    exact ⟨1, by rw [minkF_succ_eq, hslot]⟩

/-- **The walker is in `CallTreeDN`** at any needs where the callee's need is
read as `[~ this]`, for a callee `bl'` with the same head `hd` found at
`axe`, not a jet, impure, hinted, no soft call. -/
theorem callTreeDN_walk (lib : Lib) {env : CallEnv} {N : Needs} {hd : Noun} {bl bl' : Bell} {axe : Nat}
    (hl : bl.less = walkSock hd) (hl' : bl'.less = walkSock hd)
    (hslot : ∀ x gul go t, minkStep lib gul go t (C hd x) (slot axe) = some (Tone.zero bl'.fol))
    (hring : env.ring bl' = Option.none) (hpure : env.pure bl' = false) (hcod : env.cod bl' = some false)
    (hsof : ∀ m, env.sof m (Nomm.cons (Nomm.n0 2) (Nomm.n0 7)) (Nomm.n0 axe) bl' walkNeed = false)
    (hned : env.need bl' = some walkNeed) (hNf : N bl' false = some walkNeed) :
    CallTreeDN lib env N (SkaModel.Fits bl.less) true (walkF axe) (walkNomm axe bl') := by
  rw [hl]
  exact CallTreeDN.cons (CallTreeDN.n0 3) (CallTreeDN.direct (CallTreeDN.cons (CallTreeDN.n0 2) (CallTreeDN.n0 7))
    hring hned hNf ⟨splitsLess_walk hl', hsof⟩ hpure hcod (qDirect_walk hslot) (walk_hAp hl'))

/-- **The walker is in `CallTreeD`** (the whole-subject class), likewise,
when the callee has a whole-subject entry. -/
theorem callTreeD_walk (lib : Lib) {env : CallEnv} {N : Needs} {hd : Noun} {bl bl' : Bell} {axe : Nat}
    (hl : bl.less = walkSock hd) (hl' : bl'.less = walkSock hd)
    (hslot : ∀ x gul go t, minkStep lib gul go t (C hd x) (slot axe) = some (Tone.zero bl'.fol))
    (hring : env.ring bl' = Option.none) (hpure : env.pure bl' = false) (hcod : env.cod bl' = some false)
    {ndT : NeedOrd} (hned : env.need bl' = some walkNeed) (hNf : N bl' false = some walkNeed)
    (hNt : N bl' true = some ndT) :
    CallTreeD lib env N (SkaModel.Fits bl.less) true (walkF axe) (walkNomm axe bl') := by
  rw [hl]
  exact CallTreeD.cons (CallTreeD.n0 3) (CallTreeD.direct (CallTreeD.cons (CallTreeD.n0 2) (CallTreeD.n0 7))
    hring hned hNf hNt hpure hcod (qDirect_walk hslot) (walk_hAp hl'))

end Comp
end SkaModel
end Formalization
