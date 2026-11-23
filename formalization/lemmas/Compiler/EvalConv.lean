import lemmas.Compiler.EvalCall

/-!
# What the pill's `+eval-top` returns, the model returns

The converse of `eval_top_of_model`.  The pill's run is cut by the depth of
its calls (`iterN`), and the induction follows the calls of the three gates
that call each other: `+eval-top`, `+eval-blob` and `+eval-pole` (`InR`).

A run at depth `k + 1` is a run of `nockW (hyb k)`: the calls of the three
gates go to `iterN k`, where the hypothesis of the induction applies, and
every other call to `nock`, where the theorems about the other arms apply.
One gate of `+eval-blob` is let through: the gate `hop` that `+eval-blob`
builds to jump to a block, whose battery `hopB` calls `+eval-blob` again.  It
runs inline, with `hyb0 k`.

The model's side is "from some level on" (`Ev`): the model's `k` is both the
depth of the interpreter's calls and the fuel of `+mink`, and the value comes
from the other direction (`interp_le`) and the determinism of Nock.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

/-- The batteries whose calls the induction follows. -/
def InR (f : Noun) : Prop := f = eval_top.battery ∨ f = eval_blob.battery ∨ f = eval_pole.battery

instance : DecidablePred InR := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The battery of the gate `hop` of `+eval-blob`: `+got:by` of the block,
then `+eval-blob` on it. -/
def hopB : Noun :=
  (C (A 9) (C (A 2) (C (A 10) (C (C (A 110) (C (A 0) (A 12))) (C (A 10) (C (C (A 26) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 2011))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2))))))))) (C (A 0) (A 7))))))))

/-- Calls of the three gates at most `k` deep, other calls in full. -/
def hyb0 (k : Nat) (s f : Noun) : Option Noun := if InR f then iterN k s f else nock s f

/-- `hyb0`, with the gate `hop` run inline. -/
def hyb (k : Nat) (s f : Noun) : Option Noun :=
  if InR f then iterN k s f else if f = hopB then nockW (hyb0 k) s f else nock s f

theorem hyb0_le (k : Nat) (s f : Noun) : Below? (hyb0 k s f) (nock s f) := by
  unfold hyb0; split
  · exact iterN_sound k s f
  · exact Below?.refl _

theorem hyb_le (k : Nat) (s f : Noun) : Below? (hyb k s f) (nock s f) := by
  unfold hyb; split
  · exact iterN_sound k s f
  · split
    · rw [nock_eq_nockW]; exact nockW_mono (hyb0_le k) s f
    · exact Below?.refl _

theorem iterN_le_hyb0 (k : Nat) (s f : Noun) : Below? (iterN k s f) (hyb0 k s f) := by
  unfold hyb0; split
  · exact Below?.refl _
  · exact iterN_sound k s f

theorem iterN_le_hyb (k : Nat) (s f : Noun) : Below? (iterN k s f) (hyb k s f) := by
  unfold hyb; split
  · exact Below?.refl _
  · split
    · cases k with
      | zero => intro x h; simp [iterN] at h
      | succ j =>
        rw [iterN_succ]
        exact nockW_mono (fun s f x h => iterN_le_hyb0 (j + 1) s f x (iterN_mono_succ j s f x h)) s f
    · exact iterN_sound k s f

/-- A run at depth `k + 1` is a run of `nockW (hyb k)`. -/
theorem iterN_succ_hyb {k : Nat} {s f x : Noun} (h : iterN (k + 1) s f = some x) :
    nockW (hyb k) s f = some x :=
  nockW_mono (iterN_le_hyb k) s f x h

theorem hyb_top (k : Nat) (s : Noun) : hyb k s eval_top.battery = iterN k s eval_top.battery :=
  if_pos (Or.inl rfl)
theorem hyb_blob (k : Nat) (s : Noun) : hyb k s eval_blob.battery = iterN k s eval_blob.battery :=
  if_pos (Or.inr (Or.inl rfl))
theorem hyb_pole (k : Nat) (s : Noun) : hyb k s eval_pole.battery = iterN k s eval_pole.battery :=
  if_pos (Or.inr (Or.inr rfl))
theorem hyb0_top (k : Nat) (s : Noun) : hyb0 k s eval_top.battery = iterN k s eval_top.battery :=
  if_pos (Or.inl rfl)
theorem hyb0_blob (k : Nat) (s : Noun) : hyb0 k s eval_blob.battery = iterN k s eval_blob.battery :=
  if_pos (Or.inr (Or.inl rfl))
theorem hyb0_pole (k : Nat) (s : Noun) : hyb0 k s eval_pole.battery = iterN k s eval_pole.battery :=
  if_pos (Or.inr (Or.inr rfl))

theorem hyb_hop {k : Nat} {s f : Noun} (h : f = hopB) : hyb k s f = nockW (hyb0 k) s f := by
  subst h; unfold hyb; rw [if_neg (by decide), if_pos rfl]

/-- A noun cut at depth `n`: two nouns whose cuts differ differ, and a cut is
cheap to compare where a battery is not. -/
def trunc : Nat → Noun → Noun
  | 0, _ => A 0
  | _ + 1, Noun.atom a => A a
  | n + 1, Noun.cell x y => C (trunc n x) (trunc n y)

/-- A formula that is none of the routed ones, seen from its cut at depth 8. -/
def Far (f : Noun) : Prop :=
  trunc 8 f ≠ trunc 8 eval_top.battery ∧ trunc 8 f ≠ trunc 8 eval_blob.battery ∧
    trunc 8 f ≠ trunc 8 eval_pole.battery ∧ trunc 8 f ≠ trunc 8 hopB

instance : DecidablePred Far := fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem Far.out {f : Noun} (h : Far f) : ¬ InR f ∧ ¬ f = hopB := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, fun e => h4 (e ▸ rfl)⟩
  rintro (e | e | e) <;> subst e <;> simp_all

theorem hyb_out {k : Nat} {s f : Noun} (h : Far f) : hyb k s f = nock s f := by
  unfold hyb; rw [if_neg h.out.1, if_neg h.out.2]

theorem hyb0_out {k : Nat} {s f : Noun} (h : Far f) : hyb0 k s f = nock s f := if_neg h.out.1

/-! ## From some level on -/

/-- `g m` is `some a` for every `m` from some `m0` on. -/
def Ev {α : Type} (g : Nat → Option α) (a : α) : Prop := ∃ m0, ∀ m, m0 ≤ m → g m = some a

theorem Ev.at {α : Type} {g : Nat → Option α} {a : α} (h : Ev g a) : ∃ m, g m = some a :=
  let ⟨m0, hm⟩ := h; ⟨m0, hm m0 (Nat.le_refl _)⟩

section
variable (lib : Lib) (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))

/-- What the pill's `+eval-top` returns at depth `k`, the model returns from
some level on. -/
def TopGe (k : Nat) : Prop :=
  ∀ cr, CorIn cr → ∀ s f scry x, iterN k (topS cr s f scry) eval_top.battery = some x →
    ∃ r, Ev (fun m => (SkaModel.interp lib pk m).nok cr s f scry) r

/-- The same for `+eval-blob`. -/
def BlobGe (k : Nat) : Prop :=
  ∀ cr, CorIn cr → ∀ regs trace b s params scry x,
    iterN k (blobS cr regs trace b s params scry) eval_blob.battery = some x →
    ∃ r, Ev (fun m => execBlob lib (SkaModel.interp lib pk m) s scry cr regs trace b params) r

/-- The same for `+eval-pole`. -/
def PoleGe (k : Nat) : Prop :=
  ∀ cr, CorIn cr → ∀ pole regs trace scry x,
    iterN k (poleS cr pole regs trace scry) eval_pole.battery = some x →
    ∃ r, Ev (fun m => execPole lib (SkaModel.interp lib pk m) scry cr pole regs trace) r

theorem topGe_zero : TopGe lib pk 0 := fun _ _ _ _ _ _ h => by simp [iterN] at h
theorem blobGe_zero : BlobGe lib pk 0 := fun _ _ _ _ _ _ _ _ _ h => by simp [iterN] at h
theorem poleGe_zero : PoleGe lib pk 0 := fun _ _ _ _ _ _ _ h => by simp [iterN] at h

theorem blobGe_mono {k k' : Nat} (hk : k ≤ k') (h : BlobGe lib pk k') : BlobGe lib pk k :=
  fun cr hc regs trace b s params scry x e =>
    h cr hc regs trace b s params scry x (iterN_mono hk _ _ x e)

end

/-! ## The poke under a call function below `nock` -/

/-- `pokeN` with its two calls made by `c`. -/
def pokeW (c : Noun → Noun → Option Noun) (cr ovo : Noun) : Option Noun :=
  ((slot? Ska.axPoke cr).bind fun a => c cr a).bind fun g =>
    (edit? 6 ovo g).bind fun g' => (slot? 2 g').bind fun f => c g' f

theorem pokeW_le {c : Noun → Noun → Option Noun} (hc : ∀ s f, Below? (c s f) (nock s f))
    (cr ovo : Noun) : Below? (pokeW c cr ovo) (pokeN cr ovo) :=
  Below?.bind (Below?.bind (Below?.refl _) fun a => hc cr a) fun _ =>
    Below?.bind (Below?.refl _) fun g' => Below?.bind (Below?.refl _) fun f => hc g' f

/-- Under `hyb k`, the poke crashes or returns what the model `pk` says. -/
theorem pokeW_cases {pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun)}
    {cr : Noun} (hpk : PokeIs pk cr) (k : Nat) (ov : Ovum) (hov : ¬ Ska.Hot ov.toNoun) :
    pokeW (hyb k) cr ov.toNoun = none ∨
      ∃ p cr', pk cr ov = some (p, cr') ∧ pokeW (hyb k) cr ov.toNoun = some (C p.toNoun cr') := by
  cases e : pokeW (hyb k) cr ov.toNoun with
  | none => exact Or.inl rfl
  | some y =>
    right
    have h1 := pokeW_le (hyb_le k) cr ov.toNoun y e
    rw [hpk.1 ov hov] at h1
    obtain ⟨⟨p, cr'⟩, e1, rfl⟩ := Option.map_eq_some_iff.1 h1
    exact ⟨p, cr', e1, rfl⟩

/-! ## The values, from the other direction -/

section
variable (lib : Lib) (hslam : SlamIsNock lib)
  (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
  (hpk : ∀ cr, CorIn cr → PokeIs pk cr)
include hslam hpk

theorem interp_call_le (m : Nat) : CallLe lib pk (SkaModel.interp lib pk m) := by
  cases m with
  | zero => intro _ _ _ _ _ _ _ h; simp [SkaModel.interp] at h
  | succ m =>
    exact fun _ _ _ _ _ _ _ h => ⟨SkaModel.interp lib pk m, (interp_le lib hslam pk hpk m).1, h⟩

theorem top_val {k : Nat} {cr s f scry x : Noun} {r : Tone × Noun} (hc : CorIn cr)
    (hr : Ev (fun m => (SkaModel.interp lib pk m).nok cr s f scry) r)
    (h : iterN k (topS cr s f scry) eval_top.battery = some x) : x = resN r ∧ CorIn r.2 := by
  obtain ⟨m, hm⟩ := hr.at
  obtain ⟨h1, h2⟩ := (interp_le lib hslam pk hpk m).2 cr hc s f scry r hm
  have h3 := iterN_sound k _ _ x h
  rw [h1] at h3
  exact ⟨(Option.some.inj h3).symm, h2⟩

theorem blob_val {k : Nat} {cr : Noun} {regs : TreapMap mugF (Option Noun)} {trace : Trace} {b : Blob}
    {s : Straight (TreapMap mugF)} {params : List (Option Nat)} {scry x : Noun} {r : Tone × Noun}
    (hc : CorIn cr)
    (hr : Ev (fun m => execBlob lib (SkaModel.interp lib pk m) s scry cr regs trace b params) r)
    (h : iterN k (blobS cr regs trace b s params scry) eval_blob.battery = some x) :
    x = resN r ∧ CorIn r.2 := by
  obtain ⟨m, hm⟩ := hr.at
  obtain ⟨h1, h2⟩ := (interp_le lib hslam pk hpk m).1 cr hc regs trace b s params scry r hm
  have h3 := iterN_sound k _ _ x h
  rw [h1] at h3
  exact ⟨(Option.some.inj h3).symm, h2⟩

theorem pole_val {k : Nat} {cr : Noun} {pole : Pole} {regs : TreapMap mugF (Option Noun)} {trace : Trace}
    {scry x : Noun} {r : Tone × TreapMap mugF (Option Noun) × Trace × Noun} (hc : CorIn cr)
    (hr : Ev (fun m => execPole lib (SkaModel.interp lib pk m) scry cr pole regs trace) r)
    (h : iterN k (poleS cr pole regs trace scry) eval_pole.battery = some x) :
    x = poleOutS r ∧ CorIn r.2.2.2 := by
  obtain ⟨m, hm⟩ := hr.at
  obtain ⟨h1, h2⟩ := eval_pole_le cr hc lib hslam pk (hpk cr hc) _ (interp_call_le lib hslam pk hpk m)
    (interp_le lib hslam pk hpk m).2 scry pole regs trace r hm
  have h3 := iterN_sound k _ _ x h
  rw [h1] at h3
  exact ⟨(Option.some.inj h3).symm, h2⟩

end

/-- The ends of `+eval-top`, run on a hypothesis under `hyb k`. -/
macro "top_simp_at" h:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (conv at $h:ident => { lhs; arg 3; unfold eval_top.battery }
   simp (disch := decide) [nock_exec, hyb_top, hyb_blob, hyb_pole, hyb_hop, hyb_out, hyb0_top, hyb0_blob,
     hyb0_pole, hyb0_out, $ts,*] at $h:ident))

/-- The same, on a hypothesis whose formula is already open. -/
macro "hyb_simp_at" h:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (disch := decide) [nock_exec, hyb_top, hyb_blob, hyb_pole, hyb_hop, hyb_out, hyb0_top, hyb0_blob,
     hyb0_pole, hyb0_out, $ts,*] at $h:ident)

theorem needOrd_this {n : NeedOrd} (h : ¬ n = NeedOrd.this) :
    ¬ C (A Tag.this) (A 0) = n.toNoun := by
  cases n with
  | pair p q => cases p <;> simp [NeedOrd.toNoun]
  | both _ _ => simp [NeedOrd.toNoun, Tag.this, Tag.both]
  | this => exact absurd rfl h
  | none => simp [NeedOrd.toNoun, Tag.this, Tag.none]

/-- `+eval-pole`, run on a hypothesis under `hyb k`. -/
macro "pole_simp_at" h:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (conv at $h:ident => { lhs; arg 3; unfold eval_pole.battery }
   simp (disch := decide) [nock_exec, hyb_top, hyb_blob, hyb_pole, hyb_hop, hyb_out, hyb0_top, hyb0_blob,
     hyb0_pole, hyb0_out, Pole.toNoun,
     Tag.caf, Tag.cal, Tag.nok, Tag.imm, Tag.mov, Tag.inc, Tag.con, Tag.hed, Tag.tal, Tag.cel,
     Tag.lob, Tag.equ, Tag.hsp, Tag.hse, Tag.hdp, Tag.hde, Tag.hmp, Tag.hme, Tag.hcp, Tag.hce,
     Tag.spy, Tag.cam, Tag.csl, Tag.csf, Tag.csm, $ts,*] at $h:ident))

/-- Something from some level on, from a constant value that is not `none`. -/
theorem ev_of {α : Type} {g : Nat → Option α} {v : Option α} (m0 : Nat)
    (h : ∀ m, m0 ≤ m → g m = v) (hv : v ≠ none) : ∃ a, Ev g a := by
  obtain ⟨a, rfl⟩ := Option.ne_none_iff_exists'.1 hv
  exact ⟨a, m0, h⟩

/-- `+eval-blob`, run on a hypothesis under `hyb k`. -/
macro "blob_simp_at" h:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (conv at $h:ident => { lhs; arg 3; unfold eval_blob.battery }
   simp (disch := decide) [nock_exec, hyb_top, hyb_blob, hyb_pole, hyb_hop, hyb_out, hyb0_top,
     hyb0_blob, hyb0_pole, hyb0_out, Tag.lti, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp,
     Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, argsN, listNoun, $ts,*] at $h:ident))

/-- The model of a block that ends in a jump, from the model of the jump. -/
theorem ev_jump {lib : Lib} {O : Nat → Oracle Noun} {s : Straight (TreapMap mugF)} {scry cr : Noun}
    {regs : TreapMap mugF (Option Noun)} {trace : Trace} {fin : Termin} (j : Jmp)
    (hx : ∀ m, execBlob lib (O m) s scry cr regs trace ⟨[], [], fin⟩ [] =
      (HoonMap.get s.blocks j.there).bind fun b' => execBlob lib (O m) s scry cr regs trace b' j.args)
    {b' : Blob} (e : HoonMap.get s.blocks j.there = some b') {r : Tone × Noun}
    (hr : Ev (fun m => execBlob lib (O m) s scry cr regs trace b' j.args) r) :
    ∃ r, Ev (fun m => execBlob lib (O m) s scry cr regs trace ⟨[], [], fin⟩ []) r :=
  let ⟨m0, hm⟩ := hr
  ⟨r, m0, fun m hm' => (hx m).trans (by rw [e, Option.bind_some]; exact hm m hm')⟩

/-- The model at level `m + 1` from level `m`. -/
theorem Ev.succ {α : Type} {g : Nat → Option α} {a : α} (h : ∃ m0, ∀ m, m0 ≤ m → g (m + 1) = some a) :
    Ev g a := by
  obtain ⟨m0, hm⟩ := h
  refine ⟨m0 + 1, fun m hm' => ?_⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact hm m' (by omega)

section
variable (lib : Lib) (hslam : SlamIsNock lib)
  (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
  (hpk : ∀ cr, CorIn cr → PokeIs pk cr)
include hslam hpk

set_option maxHeartbeats 16000000 in
/-- `+eval-top` at depth `k + 1`: an atom formula, a `%bare` one by `+mink`, and
any other by the poke and `+eval-blob` at depth `k`. -/
theorem top_step (k : Nat) (hB : BlobGe lib pk k) : TopGe lib pk (k + 1) := by
  intro cr hc s f scry x h
  have h' := iterN_succ_hyb h
  have hl4 : slot? (read.layer2.axis / 4) (icore cr) = some layer4 := hc.2.1
  simp only [read.layer2.axis, icore, Nat.reduceDiv, nock_exec] at hl4
  rcases f with fa | ⟨fh, ft⟩
  · exact ⟨(Tone.two [], cr), Ev.succ ⟨0, fun m _ => by simp [SkaModel.interp, topBody]⟩⟩
  rcases isBare_cases (C fh ft) with ⟨rest, e⟩ | hb
  · simp only [Noun.cell.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    by_cases hM : ∃ t, Mink lib scry [] s (C (A 11) (C (A Tag.bare) rest)) t
    · obtain ⟨t, n, hn⟩ := hM
      refine ⟨(t, cr), Ev.succ ⟨n, fun m hm => ?_⟩⟩
      simp [SkaModel.interp, topBody, isBare, minkF_le lib scry hm _ _ _ _ hn]
    · exfalso
      have hn : nock (C mink.battery (C (C (C s (C (A 11) (C (A Tag.bare) rest))) scry) layer4))
          mink.battery = none := by
        cases e : nock (C mink.battery (C (C (C s (C (A 11) (C (A Tag.bare) rest))) scry) layer4))
          mink.battery with
        | none => rfl
        | some y =>
          obtain ⟨t, -, ht⟩ := (mink_pill_iff lib hslam _ _ _ y).1 e
          exact absurd ⟨t, ht⟩ hM
      simp only [Tag.bare] at hn
      top_simp_at h' [hl4, mink.arm_at, mink_arm, hn, Tag.bare]
  · have hdisp : ¬ A 11 = fh ∨ (fh = A 11 ∧ ∃ t, ft = A t) ∨
        (fh = A 11 ∧ ∃ th tt, ft = C th tt ∧ ¬ A Tag.bare = th) := by
      by_cases h11 : fh = A 11
      · subst h11
        rcases ft with t | ⟨th, tt⟩
        · exact Or.inr (Or.inl ⟨rfl, t, rfl⟩)
        · refine Or.inr (Or.inr ⟨rfl, th, tt, rfl, fun e => ?_⟩)
          subst e; simp [isBare] at hb
      · exact Or.inl fun e => h11 e.symm
    rcases pokeW_cases (hpk cr hc) k (Ovum.full s (C fh ft)) (nh_full _ _) with hw | ⟨p, cr', e1, hw⟩
    · exfalso
      simp only [pokeW, Ska.axPoke, Ovum.toNoun, Tag.full] at hw
      rcases hdisp with hd | ⟨rfl, t, rfl⟩ | ⟨rfl, th, tt, rfl, hd⟩
      · top_simp_at h' [hw, hd]
      · top_simp_at h' [hw]
      · simp only [Tag.bare] at hd
        top_simp_at h' [hw, hd]
    · simp only [pokeW, Ska.axPoke, Ovum.toNoun, Tag.full] at hw
      have hc' := (hpk cr hc).2 _ _ e1 (nh_full _ _)
      have hl2 : slot? read.layer2.axis (icore cr') = some layer2 := hc'.1
      simp only [read.layer2.axis, icore, nock_exec] at hl2
      have hnd : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
        ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
      have hreg : HoonMap.toNoun (unitNoun id) (regsOf [s] : TreapMap mugF (Option Noun))
          = C (C (A 0) (C (A 0) s)) (C (A 0) (A 0)) := rfl
      rcases hdisp with hd | ⟨rfl, t, rfl⟩ | ⟨rfl, th, tt, rfl, hd⟩
      all_goals (try simp only [Tag.bare] at hd)
      all_goals first | top_simp_at h' [hw, hd] | top_simp_at h' [hw]
      all_goals
        rcases p with _ | ⟨b, c, new⟩ | ps
        · hyb_simp_at h' []
        rotate_left
        · hyb_simp_at h' [Tag.ir, Tag.drop]
        by_cases h1 : c.nargs = 1
        rotate_left
        · have h1' : ¬ 1 = c.nargs := fun e => h1 e.symm
          hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, Straight.toNoun, h1']
        by_cases h2 : c.need = NeedOrd.this
        rotate_left
        · have h2' := needOrd_this h2
          simp only [Tag.this] at h2'
          hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, Straight.toNoun, h1, h2']
        have hg := getF_hoonMap Blob.toNoun c.blocks 0
        cases e2 : HoonMap.get c.blocks 0 with
        | none =>
          rw [e2] at hg
          simp only [unitNoun] at hg
          hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, Straight.toNoun, h1, h2, NeedOrd.toNoun,
            Tag.this, hl2, by.arm_at, by_arm, by.got.arm_at, got_arm, got_gate_nil layer2 hnd _ _ hg]
        | some b0 =>
        rw [e2] at hg
        obtain ⟨par0, body0, fin0⟩ := b0
        simp only [unitNoun, Blob.toNoun] at hg
        by_cases hp0 : par0 = []
        rotate_left
        · obtain ⟨q, qs, rfl⟩ := List.exists_cons_of_ne_nil hp0
          hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, Straight.toNoun, h1, h2, NeedOrd.toNoun,
            Tag.this, hl2, by.arm_at, by_arm, by.got.arm_at, got_arm, got_gate layer2 hnd _ _ _ hg,
            listNoun]
        subst hp0
        cases eB : iterN k (blobS cr' (regsOf [s]) [] ⟨[], body0, fin0⟩ c [] scry)
          eval_blob.battery with
        | none =>
          simp only [blobS, icore, Straight.toNoun, argsN, listNoun, hreg, Blob.toNoun, h1, h2,
            NeedOrd.toNoun, Tag.this] at eB
          hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, Straight.toNoun, h1, h2, NeedOrd.toNoun,
            Tag.this, hl2, by.arm_at, by_arm, by.got.arm_at, got_arm, got_gate layer2 hnd _ _ _ hg,
            eval_blob.arm, eB, hreg, listNoun]
        | some y =>
          obtain ⟨r, m0, hm⟩ := hB cr' hc' _ _ _ _ _ _ _ eB
          refine ⟨r, Ev.succ ⟨m0, fun m hm' => ?_⟩⟩
          simp [SkaModel.interp, topBody, hb, e1, h1, h2, e2, hm m hm']

set_option maxHeartbeats 16000000 in
/-- `+eval-pole` at depth `k + 1`: the ops that stay in the function from
`nock`, `%nok` by `+eval-top` at depth `k`, the calls by the poke and
`+eval-blob` at depth `k`, and `%caf`, `%cam`, `%csf`, `%csm` by `+eval-pole`
at depth `k` on the plain call. -/
theorem pole_step (k : Nat) (hB : BlobGe lib pk k) (hT : TopGe lib pk k) (hP : PoleGe lib pk k) :
    PoleGe lib pk (k + 1) := by
  intro cr hc pole regs trace scry x h
  have h' := iterN_succ_hyb h
  have hcor : slot? 3 (icore cr) = some cr := by simp [nock_exec]
  have hpi := evalPoleIn_icore hc
  have hl2 : slot? read.layer2.axis (icore cr) = some layer2 := hc.1
  have loc : ∀ (_ : nock (poleS cr pole regs trace scry) eval_pole.battery
      = (localPole lib scry pole regs trace).map (poleOut cr)),
      (∀ m, execPole lib (SkaModel.interp lib pk m) scry cr pole regs trace =
        (localPole lib scry pole regs trace).map (fun r => (r.1, r.2.1, r.2.2, cr))) →
      ∃ r, Ev (fun m => execPole lib (SkaModel.interp lib pk m) scry cr pole regs trace) r := by
    intro e hx
    have h1 := iterN_sound _ _ _ x h
    rw [e] at h1
    obtain ⟨r', h2, -⟩ := Option.map_eq_some_iff.1 h1
    exact ⟨_, 0, fun m _ => (hx m).trans (by rw [h2]; rfl)⟩
  -- the plain call that `%caf`, `%cam`, `%csf`, `%csm` run
  have plain : ∀ pole', (∀ m, execPole lib (SkaModel.interp lib pk m) scry cr pole regs trace =
        execPole lib (SkaModel.interp lib pk m) scry cr pole' regs trace) →
      iterN k (poleS cr pole' regs trace scry) eval_pole.battery = some x →
      ∃ r, Ev (fun m => execPole lib (SkaModel.interp lib pk m) scry cr pole regs trace) r := by
    intro pole' hx e
    obtain ⟨r, m0, hm⟩ := hP cr hc pole' regs trace scry x e
    exact ⟨r, m0, fun m hm' => (hx m).trans (hm m hm')⟩
  cases pole with
  | caf a v d n =>
    refine plain (Pole.cal a v d) (fun m => rfl) ?_
    pole_simp_at h' []
    simpa [poleS, icore, Pole.toNoun, Tag.cal] using h'
  | cam a v d n =>
    refine plain (Pole.cal a v d) (fun m => rfl) ?_
    pole_simp_at h' []
    simpa [poleS, icore, Pole.toNoun, Tag.cal] using h'
  | csf a sr d n =>
    refine plain (Pole.csl a sr d) (fun m => rfl) ?_
    pole_simp_at h' []
    simpa [poleS, icore, Pole.toNoun, Tag.csl] using h'
  | csm a sr d n =>
    refine plain (Pole.csl a sr d) (fun m => rfl) ?_
    pole_simp_at h' []
    simpa [poleS, icore, Pole.toNoun, Tag.csl] using h'
  | hmp a v f =>
    exact loc (eval_pole_hmp (icore cr) cr hcor hpi layer2 hl2 turn.arm_at homoIn_layer2 lib scry a v f
      regs trace) fun m => rfl
  | spy e p d =>
    exact loc (eval_pole_spy (icore cr) cr hcor hpi lib hslam scry e p d regs trace) fun m => rfl
  | nok u f d =>
    obtain ⟨_, hrd, _, hrc⟩ := hpi
    have hld := eval_pole_load (icore cr) hrd hrc regs
    have htarm := eval_top.arm_at cr
    simp only [eval_top.axis] at htarm
    cases e1 : SkaModel.read u regs with
    | none => exfalso; pole_simp_at h' [hld, e1, htarm]
    | some vu =>
    cases e2 : SkaModel.read f regs with
    | none => exfalso; pole_simp_at h' [hld, e1, e2, htarm]
    | some vf =>
    cases e3 : iterN k (topS cr vu vf scry) eval_top.battery with
    | none =>
      exfalso
      simp only [topS, icore] at e3
      pole_simp_at h' [hld, e1, e2, htarm, e3]
    | some y =>
      obtain ⟨⟨ton, cr'⟩, m0, hm⟩ := hT cr hc vu vf scry y e3
      apply ev_of m0
      · intro m hm'
        simp only [execPole, e1, e2, Option.bind_some, hm m hm']
        exact rfl
      · cases ton <;> simp
  | cal a v d =>
    rcases pokeW_cases (hpk cr hc) k (Ovum.dire a false) (nh_dire _ _) with hw | ⟨p, cr', e1, hw⟩
    · exfalso
      simp only [pokeW, Ska.axPoke, Ovum.toNoun, flag, Bool.false_eq_true, if_false, Tag.dire] at hw
      pole_simp_at h' [Tag.dire, hw]
    simp only [pokeW, Ska.axPoke, Ovum.toNoun, flag, Bool.false_eq_true, if_false, Tag.dire] at hw
    pole_simp_at h' [Tag.dire, hw]
    have hc' := (hpk cr hc).2 _ _ e1 (nh_dire _ _)
    have hl2' : slot? read.layer2.axis (icore cr') = some layer2 := hc'.1
    simp only [read.layer2.axis, icore, nock_exec] at hl2'
    have hnd : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
      ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
    rcases p with _ | ⟨b, c, new⟩ | ps
    · hyb_simp_at h' []
    rotate_left
    · hyb_simp_at h' [Tag.ir, Tag.drop]
    have hloop := eval_pole_loop cr' hc' (SkaModel.Prod.toNoun (SkaModel.Prod.ir b c new)) a.toNoun d
      regs (listNoun Frame.toNoun trace) scry v 0 HoonMap.empty
    simp only [SkaModel.Prod.toNoun, Tag.ir, Tag.cal, icore, HoonMap.toNoun_empty, Straight.toNoun]
      at hloop
    cases e2 : v.mapM (SkaModel.read · regs) with
    | none =>
      rw [e2] at hloop
      hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, hloop, Straight.toNoun]
    | some vs =>
    rw [e2] at hloop
    simp only [Option.map_some] at hloop
    rw [show regsFrom 0 vs HoonMap.empty = regsOf vs from rfl] at hloop
    have hg := getF_hoonMap Blob.toNoun c.blocks 0
    cases e3 : HoonMap.get c.blocks 0 with
    | none =>
      rw [e3] at hg
      hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, hloop, Straight.toNoun, hl2', by.arm_at, by_arm,
        by.got.arm_at, got_arm, got_gate_nil layer2 hnd _ _ hg]
    | some b0 =>
    rw [e3] at hg
    cases eB : iterN k (blobS cr' (regsOf vs) trace b0 c [] scry) eval_blob.battery with
    | none =>
      simp only [blobS, icore, Straight.toNoun, argsN, listNoun] at eB
      hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, hloop, Straight.toNoun, hl2', by.arm_at, by_arm,
        by.got.arm_at, got_arm, got_gate layer2 hnd _ _ _ hg, unitNoun, eval_blob.arm, eB, argsN,
        listNoun]
    | some y =>
      obtain ⟨⟨ton, cr''⟩, m0, hm⟩ := hB cr' hc' _ _ _ _ _ _ _ eB
      apply ev_of (m0 + 1)
      · intro m hm'
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        simp only [execPole, e2, Option.bind_some, SkaModel.interp, callBody, e1, execEntry, e3,
          hm m' (by omega)]
        exact rfl
      · cases ton <;> simp [afterCall]
  | csl a sr d =>
    rcases pokeW_cases (hpk cr hc) k (Ovum.dire a true) (nh_dire _ _) with hw | ⟨p, cr', e1, hw⟩
    · exfalso
      simp only [pokeW, Ska.axPoke, Ovum.toNoun, flag, if_true, Tag.dire] at hw
      pole_simp_at h' [Tag.dire, hw]
    simp only [pokeW, Ska.axPoke, Ovum.toNoun, flag, if_true, Tag.dire] at hw
    pole_simp_at h' [Tag.dire, hw]
    have hc' := (hpk cr hc).2 _ _ e1 (nh_dire _ _)
    have hl2' : slot? read.layer2.axis (icore cr') = some layer2 := hc'.1
    simp only [read.layer2.axis, icore, nock_exec] at hl2'
    have hnd : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
      ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
    obtain ⟨_, hrd', _, hrc'⟩ := evalPoleIn_icore hc'
    have hld := eval_pole_load (icore cr') hrd' hrc' regs
    rcases p with _ | ⟨b, c, new⟩ | ps
    · hyb_simp_at h' []
    rotate_left
    · hyb_simp_at h' [Tag.ir, Tag.drop]
    cases e2 : SkaModel.read sr regs with
    | none =>
      hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, hld, e2, Straight.toNoun]
    | some vs0 =>
    have hreg : HoonMap.toNoun (unitNoun id) (regsOf [vs0] : TreapMap mugF (Option Noun))
        = C (C (A 0) (C (A 0) vs0)) (C (A 0) (A 0)) := rfl
    have hg := getF_hoonMap Blob.toNoun c.blocks 0
    cases e3 : HoonMap.get c.blocks 0 with
    | none =>
      rw [e3] at hg
      hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, hld, e2, hreg, Straight.toNoun, hl2', by.arm_at,
        by_arm, by.got.arm_at, got_arm, got_gate_nil layer2 hnd _ _ hg]
    | some b0 =>
    rw [e3] at hg
    cases eB : iterN k (blobS cr' (regsOf [vs0]) trace b0 c [] scry) eval_blob.battery with
    | none =>
      simp only [blobS, icore, Straight.toNoun, argsN, listNoun, hreg] at eB
      hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, hld, e2, hreg, Straight.toNoun, hl2', by.arm_at,
        by_arm, by.got.arm_at, got_arm, got_gate layer2 hnd _ _ _ hg, unitNoun, eval_blob.arm, eB,
        argsN, listNoun]
    | some y =>
      obtain ⟨⟨ton, cr''⟩, m0, hm⟩ := hB cr' hc' _ _ _ _ _ _ _ eB
      apply ev_of (m0 + 1)
      · intro m hm'
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        simp only [execPole, e2, Option.bind_some, SkaModel.interp, callBody, e1, execEntry, e3,
          hm m' (by omega)]
        exact rfl
      · cases ton <;> simp [afterCall]
  | _ =>
    exact loc (eval_pole_local (icore cr) cr hcor hpi lib scry _ (by simp [PlainLocal]) regs trace)
      fun m => rfl


set_option hygiene false in
/-- A jump of `+eval-blob` to `j`, through the gate `hop`: `+got:by` of the
block, which crashes on a block that is not there, then `+eval-blob` at depth
`k`.  The facts `ts` decide the branch, for the pill and for the model. -/
macro "jump_tac" j:term "," ts:Lean.Parser.Tactic.simpLemma,* : tactic => `(tactic| (
  have hg := getF_hoonMap Blob.toNoun s.blocks ($j).there
  cases e5 : HoonMap.get s.blocks ($j).there with
  | none =>
    exfalso; rw [e5] at hg; simp only [unitNoun] at hg
    blob_simp_at h' [Blob.toNoun, Termin.toNoun, Jmp.toNoun, hrd, read_arm, hrm, hl2, hl1, by.arm_at,
      by_arm, by.got.arm_at, got_arm, got_gate_nil layer2 hnd _ _ hg, $ts,*]
  | some b' =>
    rw [e5] at hg; simp only [unitNoun] at hg
    generalize hbn : b'.toNoun = bn at hg
    cases eB : iterN k (blobS cr regs trace b' s ($j).args scry) eval_blob.battery with
    | none =>
      exfalso
      simp only [blobS, hbn, argsN] at eB
      blob_simp_at h' [Blob.toNoun, Termin.toNoun, Jmp.toNoun, hrd, read_arm, hrm, hl2, hl1,
        by.arm_at, by_arm, by.got.arm_at, got_arm, got_gate layer2 hnd _ _ _ hg, eB, $ts,*]
    | some y =>
      obtain ⟨r, hr⟩ := hB cr hc regs trace b' s ($j).args scry y eB
      exact ev_jump $j (fun m => by rw [execBlob]; simp [$ts,*]) e5 hr))

set_option hygiene false in
/-- A register read at the end of a block that crashes. -/
macro "read_crash" ts:Lean.Parser.Tactic.simpLemma,* : tactic => `(tactic| (
  exfalso
  blob_simp_at h' [Blob.toNoun, Termin.toNoun, Jmp.toNoun, hrd, read_arm, hrm, $ts,*]))

set_option maxHeartbeats 16000000 in
/-- `+eval-blob` at depth `k + 1`: the passing of the parameters, the ops by
`+eval-pole` at depth `k`, the jumps through the gate `hop` and the calls at
the end by `+eval-blob` at depth `k`. -/
theorem blob_step (k : Nat) (hP : PoleGe lib pk k) (hB : BlobGe lib pk k) :
    BlobGe lib pk (k + 1) := by
  intro cr hc regs trace b s params scry x h
  have h' := iterN_succ_hyb h
  have hpi := evalPoleIn_icore hc
  obtain ⟨hmv, hrd, hst, hrc⟩ := hpi
  have hrm := read_model (icore cr) hrc
  have hl1 := slot_tail_of hc.1 layer2_layer1
  have hl2 : slot? read.layer2.axis (icore cr) = some layer2 := hc.1
  have hep := eval_pass_gate (icore cr) ⟨hmv, hrc, layer2, hc.1, levy.arm_at, lien.arm_at⟩
  simp only [read.layer2.axis, icore, Nat.reduceMul, Nat.reduceAdd] at hl1
  simp only [nock_exec] at hl1
  simp only [read.layer2.axis, icore, nock_exec] at hl2
  simp only [read.axis, icore, nock_exec] at hrd
  have hlth := arith_layer1.2.2.2.1
  have hnd : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  obtain ⟨bpar, bbody, bfin⟩ := b
  by_cases hp : params ≠ [] ∨ bpar ≠ []
  · have hp2 := hep params bpar regs
    cases e1 : evalPass params bpar regs with
    | none =>
      exfalso
      rw [e1] at hp2
      rcases params with _ | ⟨p0, ps⟩ <;> rcases bpar with _ | ⟨q0, qs⟩
      · simp at hp
      all_goals
        simp only [argsN, parN, listNoun, Option.map_none] at hp2
        blob_simp_at h' [Blob.toNoun, hp2, eval_pass_arm]
    | some regs' =>
    rw [e1, Option.map_some] at hp2
    cases eB : iterN k (blobS cr regs' trace ⟨[], bbody, bfin⟩ s [] scry) eval_blob.battery with
    | none =>
      exfalso
      simp only [blobS, Blob.toNoun, argsN, listNoun] at eB
      rcases params with _ | ⟨p0, ps⟩ <;> rcases bpar with _ | ⟨q0, qs⟩
      · simp at hp
      all_goals
        simp only [argsN, parN, listNoun] at hp2
        blob_simp_at h' [Blob.toNoun, hp2, eval_pass_arm, eB]
    | some y =>
      obtain ⟨r, m0, hm⟩ := hB cr hc regs' trace _ s [] scry y eB
      refine ⟨r, m0, fun m hm' => ?_⟩
      dsimp only
      rw [execBlob, if_pos hp]
      simp [e1, hm m hm']
  have hp' : params = [] ∧ bpar = [] := by simpa using hp
  obtain ⟨rfl, rfl⟩ := hp'
  cases bbody with
  | cons p rest =>
    cases eP : iterN k (poleS cr p regs trace scry) eval_pole.battery with
    | none =>
      exfalso
      simp only [poleS] at eP
      blob_simp_at h' [Blob.toNoun, eP, eval_pole.arm]
    | some y =>
    obtain ⟨r1, hr1⟩ := hP cr hc p regs trace scry y eP
    obtain ⟨rfl, hc1⟩ := pole_val lib hslam pk hpk hc hr1 eP
    obtain ⟨m1, hm1⟩ := hr1
    obtain ⟨ton, regs', trace', cr'⟩ := r1
    simp only [poleS, poleOutS] at eP
    cases ton with
    | zero q =>
      cases eB : iterN k (blobS cr' regs' trace' ⟨[], rest, bfin⟩ s [] scry) eval_blob.battery with
      | none =>
        exfalso
        simp only [blobS, Blob.toNoun, argsN, listNoun] at eB
        blob_simp_at h' [Blob.toNoun, eP, eval_pole.arm, Tone.toNoun, eB]
      | some y2 =>
        obtain ⟨r, m0, hm⟩ := hB cr' hc1 regs' trace' _ s [] scry y2 eB
        refine ⟨r, max m0 m1, fun m hm' => ?_⟩
        dsimp only
        rw [execBlob]
        simp [hm1 m (by omega), hm m (by omega)]
    | one q =>
      refine ⟨(Tone.one q, cr'), m1, fun m hm' => ?_⟩
      dsimp only
      rw [execBlob]
      simp [hm1 m hm']
    | two q =>
      refine ⟨(Tone.two q, cr'), m1, fun m hm' => ?_⟩
      dsimp only
      rw [execBlob]
      simp [hm1 m hm']
  | nil =>
  cases bfin with
  | bom o => exact ⟨(Tone.two trace, cr), 0, fun m _ => by dsimp only; rw [execBlob]; simp⟩
  | hop t => jump_tac t,
  | don sr =>
    cases e1 : SkaModel.read sr regs with
    | none => read_crash e1
    | some v => exact ⟨(Tone.zero v, cr), 0, fun m _ => by dsimp only; rw [execBlob]; simp [e1]⟩
  | lti n sr z o =>
    cases e1 : SkaModel.read sr regs with
    | none => read_crash e1
    | some v =>
    rcases v with a | ⟨v1, v2⟩
    · by_cases hlt : a < n
      · jump_tac z, e1, hlt, lth.arm_at, lth_arm, lth_gate layer1 hlth.2
      · jump_tac o, e1, hlt, lth.arm_at, lth_arm, lth_gate layer1 hlth.2
    · jump_tac o, e1
  | clq sr z o =>
    cases e1 : SkaModel.read sr regs with
    | none => read_crash e1
    | some v =>
    rcases v with a | ⟨v1, v2⟩
    · jump_tac o, e1
    · jump_tac z, e1
  | eqq l rr z o =>
    cases e1 : SkaModel.read l regs with
    | none => read_crash e1
    | some v =>
    cases e2 : SkaModel.read rr regs with
    | none => read_crash e1, e2
    | some w =>
    by_cases hxy : v = w
    · subst hxy
      jump_tac z, e1, e2
    · jump_tac o, e1, e2, hxy
  | brz sr z o =>
    cases e1 : SkaModel.read sr regs with
    | none => read_crash e1
    | some v =>
    by_cases hv : v = A 0
    · subst hv
      jump_tac z, e1
    · have hv' : ¬ A 0 = v := fun e => hv e.symm
      jump_tac o, e1, hv, hv'
  | brn sr z o =>
    cases e1 : SkaModel.read sr regs with
    | none => read_crash e1
    | some v =>
    rcases v with (_ | _ | j) | ⟨v1, v2⟩
    · jump_tac z, e1
    · jump_tac o, e1
    · exact ⟨(Tone.two trace, cr), 0, fun m _ => by dsimp only; rw [execBlob]; simp [e1]⟩
    · exact ⟨(Tone.two trace, cr), 0, fun m _ => by dsimp only; rw [execBlob]; simp [e1]⟩
  | jmf a v n =>
    blob_simp_at h' [Blob.toNoun, Termin.toNoun]
    obtain ⟨r, m0, hm⟩ := hB cr hc regs trace ⟨[], [], Termin.jmp a v⟩ s [] scry x
      (by simpa [blobS, Blob.toNoun, Termin.toNoun, Tag.jmp, argsN, listNoun] using h')
    refine ⟨r, m0, fun m hm' => (Eq.trans ?_ (hm m hm'))⟩
    dsimp only
    conv => { lhs; rw [execBlob] }
    conv => { rhs; rw [execBlob] }
    simp
  | jsf a sr n =>
    blob_simp_at h' [Blob.toNoun, Termin.toNoun]
    obtain ⟨r, m0, hm⟩ := hB cr hc regs trace ⟨[], [], Termin.jsp a sr⟩ s [] scry x
      (by simpa [blobS, Blob.toNoun, Termin.toNoun, Tag.jsp, argsN, listNoun] using h')
    refine ⟨r, m0, fun m hm' => (Eq.trans ?_ (hm m hm'))⟩
    dsimp only
    conv => { lhs; rw [execBlob] }
    conv => { rhs; rw [execBlob] }
    simp
  | jmp a v =>
    rcases pokeW_cases (hpk cr hc) k (Ovum.dire a false) (nh_dire _ _) with hw | ⟨p, cr', e1, hw⟩
    · exfalso
      simp only [pokeW, Ska.axPoke, Ovum.toNoun, flag, Bool.false_eq_true, if_false, Tag.dire] at hw
      blob_simp_at h' [Blob.toNoun, Termin.toNoun, Tag.dire, hw]
    simp only [pokeW, Ska.axPoke, Ovum.toNoun, flag, Bool.false_eq_true, if_false, Tag.dire] at hw
    blob_simp_at h' [Blob.toNoun, Termin.toNoun, Tag.dire, hw]
    have hc' := (hpk cr hc).2 _ _ e1 (nh_dire _ _)
    have hl2' : slot? read.layer2.axis (icore cr') = some layer2 := hc'.1
    simp only [read.layer2.axis, icore, nock_exec] at hl2'
    rcases p with _ | ⟨b, c, new⟩ | ps
    · hyb_simp_at h' []
    rotate_left
    · hyb_simp_at h' [Tag.ir, Tag.drop]
    have hloop := eval_blob_loop cr' hc' (SkaModel.Prod.toNoun (SkaModel.Prod.ir b c new)) a.toNoun
      regs (listNoun Frame.toNoun trace) s.toNoun scry v 0 HoonMap.empty
    simp only [SkaModel.Prod.toNoun, Tag.ir, Tag.jmp, icore, HoonMap.toNoun_empty, Straight.toNoun]
      at hloop
    cases e2 : v.mapM (SkaModel.read · regs) with
    | none =>
      rw [e2] at hloop
      hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, hloop, Straight.toNoun]
    | some vs =>
    rw [e2, Option.map_some] at hloop
    rw [show regsFrom 0 vs HoonMap.empty = regsOf vs from rfl] at hloop
    have hg := getF_hoonMap Blob.toNoun c.blocks 0
    cases e3 : HoonMap.get c.blocks 0 with
    | none =>
      rw [e3] at hg
      hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, hloop, Straight.toNoun, hl2', by.arm_at, by_arm,
        by.got.arm_at, got_arm, got_gate_nil layer2 hnd _ _ hg]
    | some b0 =>
    rw [e3] at hg
    simp only [unitNoun] at hg
    generalize hbn : b0.toNoun = bn at hg
    cases eB : iterN k (blobS cr' (regsOf vs) trace b0 c [] scry) eval_blob.battery with
    | none =>
      simp only [blobS, hbn, argsN, Straight.toNoun, listNoun] at eB
      hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, hloop, Straight.toNoun, hl2', by.arm_at, by_arm,
        by.got.arm_at, got_arm, got_gate layer2 hnd _ _ _ hg, eval_blob.arm, eB]
    | some y =>
      obtain ⟨r, m0, hm⟩ := hB cr' hc' _ _ _ _ _ _ _ eB
      refine ⟨r, m0 + 1, fun m hm' => ?_⟩
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      dsimp only
      rw [execBlob]
      simp [e2, SkaModel.interp, callBody, e1, execEntry, e3, hm m' (by omega)]
  | jsp a sr =>
    rcases pokeW_cases (hpk cr hc) k (Ovum.dire a true) (nh_dire _ _) with hw | ⟨p, cr', e1, hw⟩
    · exfalso
      simp only [pokeW, Ska.axPoke, Ovum.toNoun, flag, if_true, Tag.dire] at hw
      blob_simp_at h' [Blob.toNoun, Termin.toNoun, Tag.dire, hw]
    simp only [pokeW, Ska.axPoke, Ovum.toNoun, flag, if_true, Tag.dire] at hw
    blob_simp_at h' [Blob.toNoun, Termin.toNoun, Tag.dire, hw]
    have hc' := (hpk cr hc).2 _ _ e1 (nh_dire _ _)
    have hl2' : slot? read.layer2.axis (icore cr') = some layer2 := hc'.1
    simp only [read.layer2.axis, icore, nock_exec] at hl2'
    obtain ⟨_, hrd', _, hrc'⟩ := evalPoleIn_icore hc'
    have hrm' := read_model (icore cr') hrc'
    simp only [read.axis, icore, nock_exec] at hrd'
    rcases p with _ | ⟨b, c, new⟩ | ps
    · hyb_simp_at h' []
    rotate_left
    · hyb_simp_at h' [Tag.ir, Tag.drop]
    have hg := getF_hoonMap Blob.toNoun c.blocks 0
    cases e2 : SkaModel.read sr regs with
    | none =>
      hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, Straight.toNoun, hrd', read_arm, hrm', e2]
    | some vs =>
    have hreg : HoonMap.toNoun (unitNoun id) (regsOf [vs] : TreapMap mugF (Option Noun))
        = C (C (A 0) (C (A 0) vs)) (C (A 0) (A 0)) := rfl
    cases e3 : HoonMap.get c.blocks 0 with
    | none =>
      rw [e3] at hg
      hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, Straight.toNoun, hrd', read_arm, hrm', e2,
        hl2', by.arm_at, by_arm, by.got.arm_at, got_arm, got_gate_nil layer2 hnd _ _ hg]
    | some b0 =>
    rw [e3] at hg
    simp only [unitNoun] at hg
    generalize hbn : b0.toNoun = bn at hg
    cases eB : iterN k (blobS cr' (regsOf [vs]) trace b0 c [] scry) eval_blob.battery with
    | none =>
      simp only [blobS, hbn, argsN, Straight.toNoun, listNoun, hreg] at eB
      hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, Straight.toNoun, hrd', read_arm, hrm', e2,
        hl2', by.arm_at, by_arm, by.got.arm_at, got_arm, got_gate layer2 hnd _ _ _ hg,
        eval_blob.arm, eB]
    | some y =>
      obtain ⟨r, m0, hm⟩ := hB cr' hc' _ _ _ _ _ _ _ eB
      refine ⟨r, m0 + 1, fun m hm' => ?_⟩
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      dsimp only
      rw [execBlob]
      simp [e2, SkaModel.interp, callBody, e1, execEntry, e3, hm m' (by omega)]


/-- At every depth of calls, what the pill's `+eval-top`, `+eval-blob` and
`+eval-pole` return, the model returns from some level on. -/
theorem interp_ge : ∀ k, TopGe lib pk k ∧ BlobGe lib pk k ∧ PoleGe lib pk k
  | 0 => ⟨topGe_zero lib pk, blobGe_zero lib pk, poleGe_zero lib pk⟩
  | k + 1 =>
    let ⟨hT, hB, hP⟩ := interp_ge k
    ⟨top_step lib hslam pk hpk k hB, blob_step lib hslam pk hpk k hP hB,
      pole_step lib hslam pk hpk k hB hT hP⟩

/-- What the pill's `+eval-top` returns, slammed on `[[s f] gul]` in the
interpreter core over a compiler's core `cr` that keeps layers 2 and 4, is a
tone and a core that the model's `EvalTop` says. -/
theorem eval_top_to_model (cr : Noun) (hc : CorIn cr) (s f gul x : Noun)
    (h : nock (topS cr s f gul) eval_top.battery = some x) :
    ∃ ton cr', x = C ton.toNoun cr' ∧ EvalTop lib pk cr s f gul ton cr' ∧ CorIn cr' := by
  obtain ⟨k, hk⟩ := iterN_complete h
  obtain ⟨r, hr⟩ := (interp_ge lib hslam pk hpk k).1 cr hc s f gul x hk
  obtain ⟨rfl, hc'⟩ := top_val lib hslam pk hpk hc hr hk
  obtain ⟨m, hm⟩ := hr.at
  exact ⟨r.1, r.2, rfl, ⟨m, hm⟩, hc'⟩

end

theorem listNoun_frame_inj : ∀ {a b : Trace}, listNoun Frame.toNoun a = listNoun Frame.toNoun b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [listNoun] at h
  | _ :: _, [], h => by simp [listNoun] at h
  | ⟨n, x⟩ :: a, ⟨n', x'⟩ :: b, h => by
    simp only [listNoun, Frame.toNoun, Noun.cell.injEq, Noun.atom.injEq] at h
    rw [h.1.1, h.1.2, listNoun_frame_inj h.2]

theorem tone_toNoun_inj {a b : Tone} (h : a.toNoun = b.toNoun) : a = b := by
  cases a <;> cases b <;> simp_all [Tone.toNoun]
  all_goals exact listNoun_frame_inj h

/-- The pill's `+eval-top` returns `[ton cr']` exactly when the model's
`EvalTop` says so: slammed on `[[s f] gul]` in the interpreter core over a
compiler's core `cr` that keeps layers 2 and 4, with a poke that the model
`pk` computes and that keeps them, and the scry gate slammed as Nock does. -/
theorem eval_top_iff (lib : Lib) (hslam : SlamIsNock lib)
    (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
    (hpk : ∀ cr, CorIn cr → PokeIs pk cr) (cr : Noun) (hc : CorIn cr) (s f gul : Noun)
    (ton : Tone) (cr' : Noun) :
    nock (topS cr s f gul) eval_top.battery = some (C ton.toNoun cr') ↔
      EvalTop lib pk cr s f gul ton cr' := by
  constructor
  · intro h
    obtain ⟨ton', cr'', e, he, -⟩ := eval_top_to_model lib hslam pk hpk cr hc s f gul _ h
    simp only [Noun.cell.injEq] at e
    rw [tone_toNoun_inj e.1, e.2]
    exact he
  · exact fun h => (eval_top_of_model lib hslam pk hpk cr hc s f gul ton cr' h).1

end Compiler
end Formalization
