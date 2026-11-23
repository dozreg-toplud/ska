import lemmas.Compiler.EvalRend
import lemmas.Hoon.CellCrash

/-!
# `+eval-mook` on nouns that are no tone

`Reach` of `core/Statement.lean` runs `+eval-mook` on any noun, the model only
on tones.  On a noun that is not `[%2 *]` the pill's `+eval-mook` returns the
noun and the core unchanged (`eval_mook_not2`), which it also does on the tone
`[%0 0]`; so `MookOther` of `Assembly.lean` reduces to the nouns `[%2 x]`
(`MookOtherTwo`, `mookOther_of_two`).

That case holds whenever the interpreter's other theorems apply
(`mookOtherTwo_of`, under the hypotheses of `eval_mook_ge`):

1. The trace is a list: `+lent` crashes on any other noun (`eval_mook_two_bad`).
2. Every frame that the loop renders has an atom for its tag.  An atom frame
   crashes when `+eval-rend` reads its tag (`eval_rend_atom`).  A frame whose
   tag is a cell is no `%meac` or `%meaf`, so `+eval-rend` hands it to `+mook`,
   whose `rend` computes `(rip 3 tag)`, and `+rip` of a cell never returns
   (`rip_gate_cell` of `Hoon/CellCrash.lean`); so `+eval-rend` crashes
   (`eval_rend_cell_tag`).  A frame with an atom tag that renders leaves a core
   that keeps `CorIn` (`eval_rend_corIn`, from `eval_rend_ge` and
   `eval_rend_le`), so the argument goes on to the next frame (`loopN_some`).
3. The witness is the tone of `toFrame` of the frames: the same length, the
   same frames where they are rendered, and anything where `+eval-mook` skips
   them.  The loop reads neither the tone nor the length (`loopN_indep`), and
   the cord of the `%lose` frame is `Lib.skipMsg` of the length on every tone
   (`EvalMookMsgIs`).  So the witness returns exactly what the noun returned.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

/-- On a noun that is not `[%2 *]`, `+eval-mook` returns the noun and the
compiler's core.  It reads nothing from its context. -/
theorem eval_mook_not2 (cr ton : Noun) (h : ∀ x, ton ≠ C (A 2) x) :
    nock (C eval_mook.battery (C ton (icore cr))) eval_mook.battery = some (C ton cr) := by
  nock_open eval_mook.battery
  rcases ton with a | ⟨hd, tl⟩
  · simp [nock_exec, icore]
  · rcases hd with b | ⟨h₁, h₂⟩
    · have hb : ¬ (2 = b) := fun e => h tl (by rw [← e])
      simp [nock_exec, icore, hb]
    · simp [nock_exec, icore]

/-- What is left of `MookOther` of `Assembly.lean`: the nouns `[%2 x]`. -/
def MookOtherTwo : Prop :=
  ∀ cr, CorIn cr → ∀ tr x,
    nock (C eval_mook.battery (C (C (A 2) tr) (icore cr))) eval_mook.battery = some x →
    ∃ (t : Tone) (y z cr' : Noun), x = C y cr' ∧
      nock (mookS cr t) eval_mook.battery = some (C z cr')

/-- `MookOther` of `Assembly.lean`, from its case `[%2 x]`. -/
theorem mookOther_of_two (h2 : MookOtherTwo) :
    ∀ cr, CorIn cr → ∀ ton x,
      nock (C eval_mook.battery (C ton (icore cr))) eval_mook.battery = some x →
      ∃ (t : Tone) (y z cr' : Noun), x = C y cr' ∧
        nock (mookS cr t) eval_mook.battery = some (C z cr') := by
  intro cr hc ton x hx
  by_cases h : ∃ tr, ton = C (A 2) tr
  · obtain ⟨tr, rfl⟩ := h
    exact h2 cr hc tr x hx
  · have h' : ∀ tr, ton ≠ C (A 2) tr := fun tr e => h ⟨tr, e⟩
    rw [eval_mook_not2 cr ton h', Option.some.injEq] at hx
    subst hx
    refine ⟨Tone.zero (A 0), ton, C (A 0) (A 0), cr, rfl, ?_⟩
    have := eval_mook_not2 cr (C (A 0) (A 0)) (fun x e => by simp at e)
    simpa [mookS, Tone.toNoun] using this

/-! ## A frame whose tag is a cell

`rend` of `+mook` sends a tag that it does not list to `(rip 3 tag)`, and
`+rip` of a cell does not return (`rip_gate_cell`).  So `+mook` crashes on a
trace with such a frame, and `+eval-rend` too. -/

theorem rend_cell_tag (mug : Noun → Nat) (ctx l2 : Noun)
    (hl2 : slot? mook.layer2.axis ctx = some l2) (hr : RendIn mug ctx l2) (u v dat ton : Noun) :
    rendSlam (C (C u v) dat) ton ctx = none := by
  obtain ⟨_, hrip, hend, hrsh, _⟩ := hr
  unfold rendSlam
  nock_open mook.rend.battery
  simp only [nock_exec, reduceCtorEq, if_false]
  nock_open mook.rend.other
  simp [nock_exec, hl2, hrip, rip_arm, rip_gate_cell l2 ⟨hend, hrsh⟩ (A 3) 3 1 (BiteIs.atom 3) u v]

/-- `+skip` keeps a trace of at most 1024 frames, whatever its frames are. -/
theorem mook_skip_short (ctx : Noun) (hc : MookIn ctx) (l : List Noun) (hl : l.length ≤ 1024) :
    nock (mookCore (C (A 2) (listN l)) ctx) mook.skip = some (listN l) := by
  obtain ⟨_, _, _, l2, hl2, _, _, hlent, _, _, _, _, hb⟩ := hc
  obtain ⟨bat, l1, rfl, hgth, hsub⟩ := hb.elim
  have hl1 := slot_layer1 hl2
  have hlen : ¬ 1024 < l.length := by omega
  nock_open mook.skip
  simp [nock_exec, hl2, hl1, hlent, hgth, lent_arm, lent_gate, gth_arm, gth_gate _ hgth.2, hlen]

/-- `+mook` on a trace of one frame whose tag is a cell crashes. -/
theorem mook_cell_tag (mug : Noun → Nat) (ctx l2 : Noun) (hc : MookIn ctx)
    (hl2 : slot? mook.layer2.axis ctx = some l2) (hr : RendIn mug ctx l2) (u v dat : Noun) :
    nock (mookGate (C (A 2) (C (C (C u v) dat) (A 0))) ctx) mook.battery = none := by
  have hskip := mook_skip_short ctx hc [C (C u v) dat] (by simp)
  simp only [listN_cons, listN_nil] at hskip
  have hrc := rend_cell_tag mug ctx l2 hl2 hr u v dat (C (A 2) (C (C (C u v) dat) (A 0)))
  obtain ⟨_, _, _, l2', hl2', hturn, hhomo, _⟩ := hc
  rw [hl2] at hl2'
  cases hl2'
  have ht := turn_gate_mapM l2 hhomo mook.rend.battery (C (A 0) (A 0))
    (mookCore (C (A 2) (C (C (C u v) dat) (A 0))) ctx)
    (fun n => rendSlam n (C (A 2) (C (C (C u v) dat) (A 0))) ctx) [C (C u v) dat] (fun _ _ => rfl)
  simp only [listN_cons, listN_nil, List.mapM_cons, List.mapM_nil, hrc] at ht
  have hgate : nock (mookGate (C (A 2) (C (C (C u v) dat) (A 0))) ctx) mook.battery
      = nock (mookCore (C (A 2) (C (C (C u v) dat) (A 0))) ctx) mook.buc := by
    nock_open mook.battery
    simp [nock_exec]
  rw [hgate]
  nock_open mook.buc
  simp [nock_exec, hl2, hturn, turn_arm, hskip, ht]

/-- `+eval-rend` on a frame whose tag is a cell crashes: it is no `%meac` or
`%meaf`, and `+mook` crashes on it. -/
theorem eval_rend_cell_tag (cr : Noun) (hc : CorIn cr) (u v dat : Noun) :
    nock (C eval_rend.battery (C (C (C u v) dat) (icore cr))) eval_rend.battery = none := by
  have hl4 : slot? (read.layer2.axis / 4) (icore cr) = some layer4 := hc.2.1
  simp only [read.layer2.axis, icore, Nat.reduceDiv, nock_exec] at hl4
  have hm := mook_cell_tag mugF layer4 layer2 mookIn_layer4 mook.layer2.arm_at rendIn_layer4 u v dat
  simp only [mookGate] at hm
  nock_open eval_rend.battery
  simp [nock_exec, hl4, mook.arm_at, mook_arm, hm]

/-- `+eval-rend` on an atom crashes: it reads the tag, the head of its sample. -/
theorem eval_rend_atom (cr : Noun) (a : Nat) :
    nock (C eval_rend.battery (C (A a) (icore cr))) eval_rend.battery = none := by
  nock_open eval_rend.battery
  simp [nock_exec]

/-! ## The loop of `+eval-mook` on any nouns -/

/-- The subject of the loop of `+eval-mook`, with the frames left as nouns. -/
abbrev loopN (out l : List Noun) (yel ton cr : Noun) : Noun :=
  C eval_mook.loop2 (C (listN out) (C (listN l) (C yel (C eval_mook.battery (C ton (icore cr))))))

theorem loopN_nil (out : List Noun) (yel ton cr : Noun) :
    nock (loopN out [] yel ton cr) eval_mook.loop2 = some (C (C (A 2) (listN out)) cr) := by
  nock_open eval_mook.loop2
  simp [nock_exec]

set_option maxHeartbeats 4000000 in
/-- One frame of the loop: `+eval-rend` on it, then the loop on the rest with
the core that `+eval-rend` returns. -/
theorem loopN_cons (out : List Noun) (f : Noun) (l : List Noun) (yel ton cr : Noun) :
    nock (loopN out (f :: l) yel ton cr) eval_mook.loop2 =
      (nock (C eval_rend.battery (C f (icore cr))) eval_rend.battery).bind fun r =>
        match r with
        | Noun.cell t cr' => nock (loopN (t :: out) l yel ton cr') eval_mook.loop2
        | Noun.atom _ => none := by
  have harm := eval_rend.arm_at cr
  simp only [eval_rend.axis] at harm
  cases e : nock (C eval_rend.battery (C f (icore cr))) eval_rend.battery with
  | none =>
    simp only [icore] at e
    nock_open eval_mook.loop2
    simp [nock_exec, harm, eval_rend.arm, e]
  | some r =>
    simp only [icore] at e
    rcases r with a | ⟨t, cr'⟩
    · nock_open eval_mook.loop2
      simp [nock_exec, harm, eval_rend.arm, e]
    · simp only [Option.bind_some]
      nock_open eval_mook.loop2
      simp [nock_exec, harm, eval_rend.arm, e]
      rfl

/-- The loop reads neither the length `yel` nor the tone `ton` it carries. -/
theorem loopN_indep : ∀ (l out : List Noun) (yel ton yel' ton' cr : Noun),
    nock (loopN out l yel ton cr) eval_mook.loop2 = nock (loopN out l yel' ton' cr) eval_mook.loop2 := by
  intro l
  induction l with
  | nil => intro out yel ton yel' ton' cr; rw [loopN_nil, loopN_nil]
  | cons f l ih =>
    intro out yel ton yel' ton' cr
    rw [loopN_cons, loopN_cons]
    cases nock (C eval_rend.battery (C f (icore cr))) eval_rend.battery with
    | none => rfl
    | some r =>
      rcases r with a | ⟨t, cr'⟩
      · rfl
      · exact ih (t :: out) yel ton yel' ton' cr'

/-! ## `+eval-mook` on `[%2 tr]` -/

/-- The frames that `+eval-mook` renders: the trace, or for more than 1024
frames its first 512, a `%lose` frame with the cord `msg`, and its last 512. -/
def cutN (msg : Noun) (l : List Noun) : List Noun :=
  if 1024 < l.length then l.take 512 ++ C (A Tag.lose) msg :: l.drop (l.length - 512) else l

set_option maxHeartbeats 8000000 in
/-- On a trace that is a list, `+eval-mook` runs its loop on the frames that
it keeps, from the last. -/
theorem eval_mook_two_loop (lib : Lib) (hmsg : EvalMookMsgIs lib) (cr : Noun) (hc : CorIn cr)
    (frs : List Noun) :
    nock (C eval_mook.battery (C (C (A 2) (listN frs)) (icore cr))) eval_mook.battery =
      nock (loopN [] (cutN (lib.skipMsg (frs.length - 1024)) frs).reverse (A frs.length)
        (C (A 2) (listN frs)) cr) eval_mook.loop2 := by
  have hl2 : slot? read.layer2.axis (icore cr) = some layer2 := hc.1
  have hl1 := slot_tail_of hc.1 layer2_layer1
  simp only [read.layer2.axis, icore, Nat.reduceMul, Nat.reduceAdd, nock_exec] at hl2 hl1
  obtain ⟨_, hsub, _, _, _, _, hgth, _⟩ := Hoon.arith_layer1
  have hdec : Below DecIn layer2 := hsub.2
  have hmsg' := hmsg frs.length (C (A 2) (listN frs)) cr hc
  simp only [icore] at hmsg'
  nock_open eval_mook.battery
  by_cases hlen : 1024 < frs.length
  · have hmsg'' := hmsg' hlen
    simp [mookMsgF, nock_exec] at hmsg''
    simp [nock_exec, hl2, hl1, lent.arm_at, weld.arm_at, scag.arm_at, slag.arm_at, flop.arm_at,
      hgth, hsub, lent_arm, lent_gate, gth_arm, gth_gate _ hgth.2, weld_arm, weld_gate, scag_arm,
      scag_gate _ hdec, slag_arm, slag_gate _ hdec, sub_arm,
      sub_gate _ hsub.2 512 frs.length (by omega), hlen, hmsg'', flop_arm,
      flop_gate _ homoIn_layer2, appendN_cons_listN, cutN, Tag.lose]
    rfl
  · simp [nock_exec, hl2, hl1, lent.arm_at, flop.arm_at, hgth, lent_arm, lent_gate, gth_arm,
      gth_gate _ hgth.2, hlen, flop_arm, flop_gate _ homoIn_layer2, cutN]
    rfl

/-- On a trace that is no list, `+eval-mook` crashes in `+lent`. -/
theorem eval_mook_two_bad (cr : Noun) (hc : CorIn cr) (tr : Noun) (h : ∀ l, tr ≠ listN l) :
    nock (C eval_mook.battery (C (C (A 2) tr) (icore cr))) eval_mook.battery = none := by
  have hl2 : slot? read.layer2.axis (icore cr) = some layer2 := hc.1
  simp only [read.layer2.axis, icore, nock_exec] at hl2
  nock_open eval_mook.battery
  simp [nock_exec, hl2, lent.arm_at, lent_arm, lent_gate_bad _ _ h]

/-! ## `MookOtherTwo` -/

section
variable (lib : Lib) (hslam : SlamIsNock lib)
  (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
  (hpk : ∀ cr, CorIn cr → PokeIs pk cr) (hrb : RendBaseIs lib layer4)
  (hst : SoftTankIs lib layer4) (hm : SkipMsgIs lib layer4) (hlist : ListMoldIs)
  (hbad : ∀ cr, CorIn cr → PokeDireBad cr)

include hslam hpk hrb hst hm hlist hbad in
/-- What `+eval-rend` returns on a frame with an atom for its tag is a tank
and a core that keeps what the interpreter reads: the model renders the frame
(`eval_rend_ge`), and what the model renders, the pill renders with such a
core (`eval_rend_le`). -/
theorem eval_rend_corIn (cr : Noun) (hc : CorIn cr) (n : Nat) (d y : Noun)
    (h : nock (rendS cr n d) eval_rend.battery = some y) :
    ∃ t cr', y = C t cr' ∧ CorIn cr' := by
  obtain ⟨⟨t, cr'⟩, m1, hm1⟩ :=
    eval_rend_ge lib hslam pk hpk hrb hst hm hlist cr hc (hbad cr hc) (n, d) y h
  obtain ⟨hR, hc'⟩ :=
    eval_rend_le lib hslam pk hpk hrb hst hm hlist cr hc m1 (n, d) _ (hm1 m1 (Nat.le_refl _))
  rw [h, Option.some.injEq] at hR
  exact ⟨t, cr', hR, hc'⟩

include hslam hpk hrb hst hm hlist hbad in
/-- When the loop returns, every frame it rendered has an atom for its tag
(the others crash: `eval_rend_atom`, `eval_rend_cell_tag`), and it returns a
cell. -/
theorem loopN_some : ∀ (l out : List Noun) (yel ton cr x : Noun), CorIn cr →
    nock (loopN out l yel ton cr) eval_mook.loop2 = some x →
    (∀ f ∈ l, ∃ n d, f = C (A n) d) ∧ ∃ y cr', x = C y cr' := by
  intro l
  induction l with
  | nil =>
    intro out yel ton cr x _ h
    rw [loopN_nil, Option.some.injEq] at h
    exact ⟨by simp, _, _, h.symm⟩
  | cons f l ih =>
    intro out yel ton cr x hc h
    rw [loopN_cons] at h
    cases e : nock (C eval_rend.battery (C f (icore cr))) eval_rend.battery with
    | none => rw [e] at h; simp at h
    | some r =>
      rcases f with a | ⟨tg, d⟩
      · rw [eval_rend_atom] at e; cases e
      rcases tg with n | ⟨u, v⟩
      · obtain ⟨t, cr', rfl, hc'⟩ :=
          eval_rend_corIn lib hslam pk hpk hrb hst hm hlist hbad cr hc n d r e
        simp only [e, Option.bind_some] at h
        obtain ⟨h1, h2⟩ := ih (t :: out) yel ton cr' x hc' h
        refine ⟨?_, h2⟩
        intro f hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact ⟨n, d, rfl⟩
        · exact h1 f hf
      · rw [eval_rend_cell_tag cr hc u v d] at e; cases e

end

/-- A frame of a tone for each noun: the noun itself when its head is an
atom, `[0 0]` otherwise. -/
def toFrame : Noun → Frame
  | Noun.cell (Noun.atom n) d => (n, d)
  | _ => (0, A 0)

theorem cutN_map (msg : Noun) (φ : Noun → Noun) (hφ : φ (C (A Tag.lose) msg) = C (A Tag.lose) msg)
    (l : List Noun) : cutN msg (l.map φ) = (cutN msg l).map φ := by
  unfold cutN
  by_cases h : 1024 < l.length
  · simp [h, List.map_take, List.map_drop, hφ]
  · simp [h]

theorem map_fix {φ : Noun → Noun} : ∀ (l : List Noun), (∀ f ∈ l, φ f = f) → l.map φ = l
  | [], _ => rfl
  | f :: l, h => by
    simp only [List.map_cons, h f (List.mem_cons_self ..),
      map_fix l (fun g hg => h g (List.mem_cons_of_mem _ hg))]

/-- `MookOtherTwo`: what `+eval-mook` returns on `[%2 tr]`, it returns on a
tone with the same core.  The trace is a list (`eval_mook_two_bad`), every
frame it renders has an atom for its tag (`loopN_some`), so the tone of
`toFrame` of its frames has the same length, renders the same frames, and
differs from it only in the frames that are skipped; the loop does not read
the tone (`loopN_indep`), and the cord of the `%lose` frame depends only on
the length (`EvalMookMsgIs`). -/
theorem mookOtherTwo_of (lib : Lib) (hslam : SlamIsNock lib)
    (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
    (hpk : ∀ cr, CorIn cr → PokeIs pk cr) (hrb : RendBaseIs lib layer4)
    (hst : SoftTankIs lib layer4) (hm : SkipMsgIs lib layer4) (hlist : ListMoldIs)
    (hbad : ∀ cr, CorIn cr → PokeDireBad cr) (hmsg : EvalMookMsgIs lib) : MookOtherTwo := by
  intro cr hc tr x hx
  obtain ⟨frs, rfl⟩ : ∃ frs, tr = listN frs := by
    by_cases hl : ∃ frs, tr = listN frs
    · exact hl
    · exfalso
      rw [eval_mook_two_bad cr hc tr (fun l e => hl ⟨l, e⟩)] at hx
      cases hx
  rw [eval_mook_two_loop lib hmsg cr hc frs] at hx
  obtain ⟨htag, y, cr', rfl⟩ :=
    loopN_some lib hslam pk hpk hrb hst hm hlist hbad _ [] _ _ cr _ hc hx
  refine ⟨Tone.two (frs.map toFrame), y, y, cr', rfl, ?_⟩
  have ht : (Tone.two (frs.map toFrame)).toNoun =
      C (A 2) (listN (frs.map fun f => (toFrame f).toNoun)) := by
    simp [Tone.toNoun, listNoun_eq_listN, List.map_map, Function.comp_def]
  have hfix : (cutN (lib.skipMsg (frs.length - 1024)) frs).map (fun f => (toFrame f).toNoun) =
      cutN (lib.skipMsg (frs.length - 1024)) frs := by
    apply map_fix
    intro f hf
    obtain ⟨n, d, rfl⟩ := htag f (List.mem_reverse.2 hf)
    rfl
  simp only [mookS]
  rw [ht, eval_mook_two_loop lib hmsg cr hc, List.length_map,
    cutN_map _ (fun f => (toFrame f).toNoun) rfl frs, hfix,
    loopN_indep _ _ _ _ (A frs.length) (C (A 2) (listN frs))]
  exact hx

end Compiler
end Formalization
