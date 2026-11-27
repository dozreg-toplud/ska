import lemmas.Ska.CompNaryTopRec
import lemmas.Ska.CompNaryTopCalEx

/-!
# A self-recursive bell and a mutually recursive pair, closed

README Gaps 18.15, step 4.  The walker of `CompNaryTopRec.lean` as

* `F = walkF 2` on `[F x]`: `F` calls itself on `[F x.tail]` (a direct call
  in the tail of a cons: the `%cal` form in the n-ary code);
* `A = walkF 5` and `B = walkF 4` on `[[A B] x]`: `A` calls `B`, `B` calls `A`.

Without `%6` a recursion cannot stop with a product (a call that is reached
is made, so every run that reaches the call runs the callee again), so these
are the terminating shapes the class allows: they end with a crash, after as
many calls as `x` has cells along its tail.  The `#guard`s check, before the
proofs, that the real codes exist, that their needs are `[~ this]` (the need
read), and that the codes run on the table of their entries agree with
`+mink` (a crash at the end of the list, the same at every subject checked),
and that too few levels give no answer.

* `tableOK_selfWalk`, `closed_selfWalk`: the table of `F`'s two entries, with
  no hypothesis on behaviour, only `NeedsRead` of `F`.
* `tableOK_pairWalk`, `closed_pairWalk`: the table of `A`'s and `B`'s four
  entries, only `NeedsRead` of `A` and of `B`.
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- `F = [[0 3] [2 [[0 2] [0 7]] [0 2]]]`. -/
def nounWF : Noun := walkF 2
def bellWF : Bell := ⟨walkSock nounWF, nounWF⟩
/-- `A = [[0 3] [2 [[0 2] [0 7]] [0 5]]]`, `B = [[0 3] [2 [[0 2] [0 7]] [0 4]]]`. -/
def nounWA : Noun := walkF 5
def nounWB : Noun := walkF 4
def hdAB : Noun := C nounWA nounWB
def bellWA : Bell := ⟨walkSock hdAB, nounWA⟩
def bellWB : Bell := ⟨walkSock hdAB, nounWB⟩

/-- The three bells need `[~ this]`, are impure, no jet, hinted, no soft call. -/
def envW : CallEnv :=
  ⟨fun b => if b = bellWF ∨ b = bellWA ∨ b = bellWB then some walkNeed else Option.none,
   fun _ => NeedOrd.none, fun _ => false, fun _ => Option.none, fun _ => some false, fun _ _ _ _ _ => false⟩

def nommWF : Nomm := walkNomm 2 bellWF
def nommWA : Nomm := walkNomm 5 bellWB
def nommWB : Nomm := walkNomm 4 bellWA

def capeW : Cape := Cape.cell Cape.yes Cape.no

/-- The n-ary and whole-subject entries. -/
def naryW (nm : Nomm) : Option (Straight FM) := finishLFC (S := LS) envW nm walkNeed capeW (fun ned => (ned, []))
def wholeW (nm : Nomm) : Option (Straight FM) := finishLUCM (S := LS) envW nm

/-- The table of `F`, and the table of `A` and `B`. -/
def tableFg : Table FM := fun b m => if b = bellWF then (if m then wholeW nommWF else naryW nommWF) else Option.none
def tableABg : Table FM := fun b m =>
  if b = bellWA then (if m then wholeW nommWA else naryW nommWA)
  else if b = bellWB then (if m then wholeW nommWB else naryW nommWB) else Option.none

-- the codes exist and the need of each n-ary entry is the need read
#guard [nommWF, nommWA, nommWB].all fun nm => ((naryW nm).map (·.need)) == some walkNeed && (wholeW nm).isSome
#guard [bellWF, bellWA, bellWB].all fun b => envW.need b == some walkNeed

/-- The lists `x` walked. -/
def walkXs : List Noun :=
  [A 0, C (A 1) (A 2), C (A 0) (C (A 1) (C (A 2) (A 3))), C (C (A 5) (A 6)) (C (A 7) (A 8)),
   C (A 1) (C (A 1) (C (A 1) (C (A 1) (C (A 1) (A 1)))))]

/-- On `[hd x]`: `+mink` crashes, and both entries (the n-ary one entered
with the split) answer as `+mink` with `k` levels. -/
def walkRun (T : Table FM) (b : Bell) (hd : Noun) (k : Nat) : Bool :=
  walkXs.all fun x =>
    let s := C hd x
    let mk := minkF libT (A 0) 800 [] s b.fol
    (match mk with | some (Tone.two _) => true | _ => false) &&
    (match T b false, T b true with
     | some cN, some cW =>
       (match SkaModel.split cN.need s with
        | some args => (execEntry libT (tableOracle libT T k) () cN args [] (A 0)).map Prod.fst == mk
        | Option.none => false) &&
       (execEntry libT (tableOracle libT T k) () cW [s] [] (A 0)).map Prod.fst == mk
     | _, _ => false)

#guard walkRun tableFg bellWF nounWF 12
#guard walkRun tableABg bellWA hdAB 12 && walkRun tableABg bellWB hdAB 12
-- too few levels: no answer on the longest list (six calls)
#guard match tableFg bellWF true with
  | some cW => (execEntry libT (tableOracle libT tableFg 3) () cW [C nounWF (walkXs.getD 4 (A 0))] [] (A 0)).isNone
  | Option.none => false

section
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem slot_F (lib : Lib) : ∀ x gul go t, minkStep lib gul go t (C nounWF x) (slot 2) = some (Tone.zero bellWF.fol) :=
  fun x gul go t => minkStep_axis2 lib gul go t nounWF x

theorem slot_A (lib : Lib) : ∀ x gul go t, minkStep lib gul go t (C hdAB x) (slot 5) = some (Tone.zero bellWB.fol) :=
  fun x gul go t => by simp [hdAB, bellWB, minkStep, slot, slot?, axisPath, axisPathFuel, slotAtPath]

theorem slot_B (lib : Lib) : ∀ x gul go t, minkStep lib gul go t (C hdAB x) (slot 4) = some (Tone.zero bellWA.fol) :=
  fun x gul go t => by simp [hdAB, bellWA, minkStep, slot, slot?, axisPath, axisPathFuel, slotAtPath]

theorem capeNorm_W : CapeNorm capeW := by simp [capeW, CapeNorm, Cape.isNo]

/-- `NeedsRead` of a bell of `envW` says that its n-ary entry's need is `[~ this]`. -/
theorem needsRead_W {T : Table Map} {b : Bell} (hb : envW.need b = some walkNeed) (h : NeedsRead envW T b) :
    Table.needs T b false = some walkNeed ∧ ∃ ndT, Table.needs T b true = some ndT := by
  obtain ⟨bNed, ndT, h1, h2, h3⟩ := h.needs
  rw [hb] at h1; cases h1
  exact ⟨h2, ndT, h3⟩

/-- **The table of the self-recursive `F` meets its contracts**, given only
that `F`'s n-ary entry has the need read (`NeedsRead`). -/
theorem tableOK_selfWalk (lib : Lib) {cN cW : Straight Map}
    (hN : finishLFC (S := S) envW nommWF walkNeed capeW (fun ned => (ned, [])) = some cN)
    (hW : finishLUCM (S := S) envW nommWF = some cW) (hR : NeedsRead envW (table2 bellWF cN cW) bellWF) :
    TableOK lib (table2 bellWF cN cW) := by
  have hb : envW.need bellWF = some walkNeed := by simp [envW]
  obtain ⟨hNf, ndT, hNt⟩ := needsRead_W hb hR
  refine tableOK_classes (S := S) lib (fun b c hc => ?_) (fun b c hc => ?_)
  · simp only [table2] at hc
    split at hc
    · rename_i e; subst e
      simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hc; subst hc
      exact ⟨envW, nommWF, true, capeW, C nounWF (A 0), walkNeed, rfl, capeNorm_W,
        callTreeDN_walk lib rfl rfl (slot_F lib) rfl rfl rfl (fun _ => rfl) hb hNf, hN⟩
    · cases hc
  · simp only [table2] at hc
    split at hc
    · rename_i e; subst e
      simp only [if_true, Option.some.injEq] at hc; subst hc
      exact ⟨envW, nommWF, true, callTreeD_walk lib rfl rfl (slot_F lib) rfl rfl rfl hb hNf hNt, hW⟩
    · cases hc

/-- **The self-recursive `F`, closed**: on every subject `[F x]`, each of
`F`'s two entries, run on the table of its entries, answers at some number of
levels exactly when `+mink` does, and the answers stand for each other.  The
only hypothesis is `NeedsRead` of `F`. -/
theorem closed_selfWalk (lib : Lib) {cN cW : Straight Map}
    (hN : finishLFC (S := S) envW nommWF walkNeed capeW (fun ned => (ned, [])) = some cN)
    (hW : finishLUCM (S := S) envW nommWF = some cW) (hR : NeedsRead envW (table2 bellWF cN cW) bellWF)
    (m : Bool) (x gul : Noun) {args : List Noun}
    (ha : (if m then some [C nounWF x] else SkaModel.split cN.need (C nounWF x)) = some args) :
    (∀ n r, minkF lib gul n [] (C nounWF x) nounWF = some r →
      ∃ ton, execEntry lib (tableOracle lib (table2 bellWF cN cW) n) () (if m then cW else cN) args [] gul =
        some (ton, ()) ∧ ToneRel lib (Table.needs (table2 bellWF cN cW)) ton r) ∧
    (∀ k ton, execEntry lib (tableOracle lib (table2 bellWF cN cW) k) () (if m then cW else cN) args [] gul =
        some (ton, ()) → ∃ r, Mink lib gul [] (C nounWF x) nounWF r ∧ ToneRel lib (Table.needs (table2 bellWF cN cW)) ton r) := by
  have hc : table2 bellWF cN cW bellWF m = some (if m then cW else cN) := by cases m <;> simp [table2]
  have ha' : (if m then some [C nounWF x] else SkaModel.split (if m then cW else cN).need (C nounWF x)) = some args := by
    cases m <;> simpa using ha
  exact closed_entry lib (tableOK_selfWalk lib hN hW hR) hc (walk_fits nounWF x) ha' gul

/-- The table of a pair of bells. -/
def tablePair (bA bB : Bell) (aN aW bN bW : Straight Map) : Table Map := fun b m =>
  if b = bA then (if m then some aW else some aN) else if b = bB then (if m then some bW else some bN) else Option.none

/-- **The table of the mutually recursive `A` and `B` meets its contracts**,
given only `NeedsRead` of `A` and of `B`. -/
theorem tableOK_pairWalk (lib : Lib) {aN aW bN bW : Straight Map}
    (haN : finishLFC (S := S) envW nommWA walkNeed capeW (fun ned => (ned, [])) = some aN)
    (haW : finishLUCM (S := S) envW nommWA = some aW)
    (hbN : finishLFC (S := S) envW nommWB walkNeed capeW (fun ned => (ned, [])) = some bN)
    (hbW : finishLUCM (S := S) envW nommWB = some bW)
    (hRA : NeedsRead envW (tablePair bellWA bellWB aN aW bN bW) bellWA)
    (hRB : NeedsRead envW (tablePair bellWA bellWB aN aW bN bW) bellWB) :
    TableOK lib (tablePair bellWA bellWB aN aW bN bW) := by
  have ha : envW.need bellWA = some walkNeed := by simp [envW]
  have hb : envW.need bellWB = some walkNeed := by simp [envW]
  have hAB : bellWB ≠ bellWA := by simp [bellWA, bellWB, nounWA, nounWB, walkF, slot]
  obtain ⟨hNfA, ndA, hNtA⟩ := needsRead_W ha hRA
  obtain ⟨hNfB, ndB, hNtB⟩ := needsRead_W hb hRB
  refine tableOK_classes (S := S) lib (fun b c hc => ?_) (fun b c hc => ?_)
  · simp only [tablePair] at hc
    split at hc
    · rename_i e; subst e
      simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hc; subst hc
      exact ⟨envW, nommWA, true, capeW, C hdAB (A 0), walkNeed, rfl, capeNorm_W,
        callTreeDN_walk lib rfl rfl (slot_A lib) rfl rfl rfl (fun _ => rfl) hb hNfB, haN⟩
    · split at hc
      · rename_i _ e; subst e
        simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hc; subst hc
        exact ⟨envW, nommWB, true, capeW, C hdAB (A 0), walkNeed, rfl, capeNorm_W,
          callTreeDN_walk lib rfl rfl (slot_B lib) rfl rfl rfl (fun _ => rfl) ha hNfA, hbN⟩
      · cases hc
  · simp only [tablePair] at hc
    split at hc
    · rename_i e; subst e
      simp only [if_true, Option.some.injEq] at hc; subst hc
      exact ⟨envW, nommWA, true, callTreeD_walk lib rfl rfl (slot_A lib) rfl rfl rfl hb hNfB hNtB, haW⟩
    · split at hc
      · rename_i _ e; subst e
        simp only [if_true, Option.some.injEq] at hc; subst hc
        exact ⟨envW, nommWB, true, callTreeD_walk lib rfl rfl (slot_B lib) rfl rfl rfl ha hNfA hNtA, hbW⟩
      · cases hc

/-- **The mutually recursive `A` and `B`, closed**: on every subject `[[A
B] x]`, each of the four entries, run on the table of the four, answers at
some number of levels exactly when `+mink` does on its bell's formula, and
the answers stand for each other.  The only hypotheses are `NeedsRead` of `A`
and of `B`. -/
theorem closed_pairWalk (lib : Lib) {aN aW bN bW : Straight Map}
    (haN : finishLFC (S := S) envW nommWA walkNeed capeW (fun ned => (ned, [])) = some aN)
    (haW : finishLUCM (S := S) envW nommWA = some aW)
    (hbN : finishLFC (S := S) envW nommWB walkNeed capeW (fun ned => (ned, [])) = some bN)
    (hbW : finishLUCM (S := S) envW nommWB = some bW)
    (hRA : NeedsRead envW (tablePair bellWA bellWB aN aW bN bW) bellWA)
    (hRB : NeedsRead envW (tablePair bellWA bellWB aN aW bN bW) bellWB)
    {b : Bell} (hbAB : b = bellWA ∨ b = bellWB) {m : Bool} {c : Straight Map}
    (hc : tablePair bellWA bellWB aN aW bN bW b m = some c) (x gul : Noun) {args : List Noun}
    (ha : (if m then some [C hdAB x] else SkaModel.split c.need (C hdAB x)) = some args) :
    (∀ n r, minkF lib gul n [] (C hdAB x) b.fol = some r →
      ∃ ton, execEntry lib (tableOracle lib (tablePair bellWA bellWB aN aW bN bW) n) () c args [] gul =
        some (ton, ()) ∧ ToneRel lib (Table.needs (tablePair bellWA bellWB aN aW bN bW)) ton r) ∧
    (∀ k ton, execEntry lib (tableOracle lib (tablePair bellWA bellWB aN aW bN bW) k) () c args [] gul =
        some (ton, ()) → ∃ r, Mink lib gul [] (C hdAB x) b.fol r ∧
          ToneRel lib (Table.needs (tablePair bellWA bellWB aN aW bN bW)) ton r) := by
  have hs : SkaModel.Fits b.less (C hdAB x) := by rcases hbAB with rfl | rfl <;> exact walk_fits hdAB x
  exact closed_entry lib (tableOK_pairWalk lib haN haW hbN hbW hRA hRB) hc hs ha gul

end

end Comp
end SkaModel
end Formalization
