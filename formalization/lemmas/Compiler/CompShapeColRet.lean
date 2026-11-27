import lemmas.Compiler.CompSccSixSc

/-!
# When the model's `+shape-collapse` returns

`ScRet` of `CompSccSixSc.lean` (the model's `shapeCol` returns at `fuel` on
the final pass) holds three things: `+inter1-to-inter2` succeeds (no look at
`0`), the loop of `+inter2-collapse` stops within `fuel` rounds, and
`+inter2-orig` succeeds (`?>  ?=(^ fixes)`).  The first and the last are
proved here, so the top needs only the fuel of `fixLoop` (`FixRet`):

* `fixRound_skel`, `fixLoop_skel`: a round, and so the loop, keeps the fork
  skeleton (`I2.skel`); `orig_some`: `orig` succeeds on two trees of one
  skeleton; `inter2Collapse_some`;
* `l2i_lokOk`: on a lazy need with no look at `0` anywhere (`LAll CrLok`),
  every node of `l2i` has none (`I1.LokOk`: the looks of the bonds are
  united in, their forks welded on); `i12_some`: then `i12` succeeds;
* `scRet_of_fixRet`, from `entry_lok`; **`cu_gate_scc_one_six_fix`**: the
  top with `FixRet` in place of `ScRet`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The fork skeleton -/

/-- The fork skeleton of a `need-inter2`. -/
inductive Sk where
  | mk : List (Sk × Sk) → Sk

mutual
def I2.skel : I2 → Sk
  | I2.mk _ f => Sk.mk (I2.skelF f)
def I2.skelF : List (I2 × I2) → List (Sk × Sk)
  | [] => []
  | (y, n) :: r => (I2.skel y, I2.skel n) :: I2.skelF r
end

mutual
theorem fixRound_skel (less : Cape) : ∀ (t : I2) (p : NeedOrd), I2.skel (fixRound less t p) = I2.skel t
  | I2.mk s f, p => by
    simp only [fixRound, I2.skel]
    rw [fixKids_skel less f (uniOrd p s)]
theorem fixKids_skel (less : Cape) : ∀ (f : List (I2 × I2)) (p : NeedOrd), I2.skelF (fixKids less f p) = I2.skelF f
  | [], p => by simp only [fixKids]
  | (y, n) :: r, p => by
    simp only [fixKids, I2.skelF]
    rw [fixRound_skel less y p, fixRound_skel less n p, fixKids_skel less r p]
end

theorem fixLoop_skel (less : Cape) : ∀ (fuel : Nat) (fix r : I2), fixLoop less fuel fix = some r → I2.skel r = I2.skel fix
  | 0, _, _, h => by simp [fixLoop] at h
  | k + 1, fix, r, h => by
    rw [fixLoop] at h
    split at h
    · cases h; exact fixRound_skel less fix NeedOrd.none
    · rw [fixLoop_skel less k _ r h, fixRound_skel]

mutual
/-- **`+inter2-orig` succeeds** on two trees of one skeleton. -/
theorem orig_some (less : Cape) : ∀ intr fix : I2, I2.skel intr = I2.skel fix → (orig less intr fix).isSome
  | I2.mk s fk, I2.mk fs ffk, h => by
    simp only [I2.skel, Sk.mk.injEq] at h
    rw [orig]
    exact origLoop_some less fs fk ffk h s
theorem origLoop_some (less : Cape) (fs : NeedOrd) : ∀ (fk ffk : List (I2 × I2)), I2.skelF fk = I2.skelF ffk →
    ∀ acc, (origLoop less fs fk ffk acc).isSome
  | [], ffk, h, acc => by rw [origLoop]; rfl
  | (y, n) :: r, [], h, acc => by simp [I2.skelF] at h
  | (y, n) :: r, (fy, fn) :: fr, h, acc => by
    simp only [I2.skelF, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨hy, hn⟩, hr⟩ := h
    obtain ⟨vy, ey⟩ := Option.isSome_iff_exists.1 (orig_some less y fy hy)
    obtain ⟨vn, en⟩ := Option.isSome_iff_exists.1 (orig_some less n fn hn)
    rw [origLoop, ey, en, Option.bind_some, Option.bind_some]
    exact origLoop_some less fs r fr hr _
end

/-- **`+inter2-collapse` succeeds when its loop stops.** -/
theorem inter2Collapse_some (less : Cape) (fuel : Nat) (intr fix : I2) (h : fixLoop less fuel intr = some fix) :
    (inter2Collapse fuel intr less).isSome := by
  unfold inter2Collapse
  rw [h, Option.bind_some]
  exact orig_some less intr fix (fixLoop_skel less fuel intr fix h).symm

/-! ## No look at `0` -/

mutual
/-- No look at `0` at any node of a `need-inter1`. -/
def I1.LokOk : I1 CSet → Prop
  | I1.mk _ lok fk => (∀ y ∈ HoonSet.toList lok, y ≠ 0) ∧ I1.LokOkF fk
def I1.LokOkF : List (I1 CSet × I1 CSet) → Prop
  | [] => True
  | (y, n) :: r => I1.LokOk y ∧ I1.LokOk n ∧ I1.LokOkF r
end

theorem I1.lokOkF_append : ∀ (a b : List (I1 CSet × I1 CSet)), I1.LokOkF a → I1.LokOkF b → I1.LokOkF (a ++ b)
  | [], b, _, hb => by simpa using hb
  | (y, n) :: r, b, ha, hb => by
    rw [List.cons_append, I1.LokOkF]
    rw [I1.LokOkF] at ha
    exact ⟨ha.1, ha.2.1, I1.lokOkF_append r b ha.2.2 hb⟩

mutual
/-- **`+inter1-to-inter2` succeeds** when no node has a look at `0`. -/
theorem i12_some (less : Cape) : ∀ t : I1 CSet, I1.LokOk t → (i12 less t).isSome
  | I1.mk ned lok fk, h => by
    rw [I1.LokOk] at h
    obtain ⟨s, es⟩ := sureOf_some less lok h.1 ned
    obtain ⟨f, ef⟩ := Option.isSome_iff_exists.1 (i12Forks_some less fk h.2)
    rw [i12, sureOfS_eqC, es, Option.bind_some, ef, Option.map_some]
    rfl
theorem i12Forks_some (less : Cape) : ∀ fk : List (I1 CSet × I1 CSet), I1.LokOkF fk → (i12Forks less fk).isSome
  | [], _ => by rw [i12Forks]; rfl
  | (y, n) :: r, h => by
    rw [I1.LokOkF] at h
    obtain ⟨vy, ey⟩ := Option.isSome_iff_exists.1 (i12_some less y h.1)
    obtain ⟨vn, en⟩ := Option.isSome_iff_exists.1 (i12_some less n h.2.1)
    obtain ⟨vr, er⟩ := Option.isSome_iff_exists.1 (i12Forks_some less r h.2.2)
    rw [i12Forks, ey, Option.bind_some, en, Option.bind_some, er, Option.map_some]
    rfl
end

mutual
/-- **No look at `0` in a lazy need, none in `l2i` of it.** -/
theorem l2i_lokOk : ∀ (o : Nat) (laz : Lazy CSet), WalkP (fun _ s => CrLok s) o laz → I1.LokOk (l2i laz)
  | o, Lazy.mk s f b, h => by
    rw [WalkP] at h
    rw [l2i]
    exact l2iBonds_lokOk b h.2.2 (needToOrd s.ned) s.lok (l2iForks f) h.1 (l2iForks_lokOk f h.2.1)
theorem l2iForks_lokOk : ∀ f : List (Lazy.ForkE CSet), WalkPF (fun _ s => CrLok s) f → I1.LokOkF (l2iForks f)
  | [], _ => by rw [l2iForks, I1.LokOkF]; trivial
  | ((oy, y), (on, n)) :: r, h => by
    rw [WalkPF] at h
    rw [l2iForks, I1.LokOkF]
    exact ⟨l2i_lokOk oy y h.1, l2i_lokOk on n h.2.1, l2iForks_lokOk r h.2.2⟩
theorem l2iBonds_lokOk : ∀ b : List (Nat × Lazy CSet), WalkPB (fun _ s => CrLok s) b →
    ∀ (ned : NeedOrd) (lok : CSet) (fk : List (I1 CSet × I1 CSet)),
    (∀ y ∈ HoonSet.toList lok, y ≠ 0) → I1.LokOkF fk → I1.LokOk (l2iBonds b ned lok fk)
  | [], _, ned, lok, fk, hl, hf => by rw [l2iBonds, I1.LokOk]; exact ⟨hl, hf⟩
  | (ob, i) :: r, h, ned, lok, fk, hl, hf => by
    rw [WalkPB] at h
    have hi := l2i_lokOk ob i h.1
    rw [l2iBonds]
    apply l2iBonds_lokOk r h.2
    · intro y hy
      rcases (HoonSet.mem_uni lok (l2i i).lok y).1 hy with hy | hy
      · exact hl y hy
      · generalize l2i i = J at hi hy
        obtain ⟨n', l', f'⟩ := J
        rw [I1.LokOk] at hi
        exact hi.1 y hy
    · apply I1.lokOkF_append _ _ _ hf
      generalize l2i i = J at hi
      obtain ⟨n', l', f'⟩ := J
      rw [I1.LokOk] at hi
      exact hi.2
end

/-! ## The top with the fuel alone -/

/-- **The loop of the model's `+inter2-collapse` stops within `fuel`
rounds** on the final pass of `nm`. -/
def FixRet (env : CallEnv) (nm : Nomm) (cape : Cape) (fuel : Nat) : Prop :=
  ∀ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) →
    ∀ intr, i12 cape (l2i nex.laz) = some intr → (fixLoop cape fuel intr).isSome

/-- `ScRet` from the fuel alone. -/
theorem scRet_of_fixRet (env : CallEnv) {nm : Nomm} (hn : SixOk nm = true) (ha : Bake.NoAx0 nm) (cape : Cape)
    (fuel : Nat) (h : FixRet env nm cape fuel) : ScRet env nm cape fuel := by
  intro nex g1 hr
  have hl := l2i_lokOk 0 nex.laz (entry_lok env hn ha hr)
  obtain ⟨intr, ei⟩ := Option.isSome_iff_exists.1 (i12_some cape (l2i nex.laz) hl)
  obtain ⟨fix, ef⟩ := Option.isSome_iff_exists.1 (h nex g1 hr intr ei)
  unfold shapeCol
  rw [ei, Option.bind_some]
  exact inter2Collapse_some cape fuel intr fix ef

/-- **The top on `SixOk` with the `ord` of `+shape-collapse`, the fuel of
`fixLoop` the one hypothesis on it** (`cu_gate_scc_one_six_sc` with
`FixRet`). -/
theorem cu_gate_scc_one_six_fix (fuel : Nat) (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm) (hfix : FixRet env nm cape fuel)
    (hbake : NoBakeOneO env nm (fun nex => scOrd fuel nex cape) cape DATA)
    (FUNC V : Noun) (n : Nomm) (hn' : SixOk n = true) (hax' : Bake.NoAx0 n)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFC (S := CSet) (Map := TreapMap mugF) env nm (scOrd fuel p.1 cape) cape (fun n => (n, []))).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).bind fun SURE' =>
                (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st' =>
                  C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                    (cacheN NARYU MONO SCCS INL' SURE') :=
  cu_gate_scc_one_six_sc fuel cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls nm INL'
    hinl env hn hax (scRet_of_fixRet env hn hax cape fuel hfix) hbake FUNC V n hn' hax' hgot hv

end Compiler
end Formalization
