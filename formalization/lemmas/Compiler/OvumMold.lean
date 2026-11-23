import lemmas.Compiler.Validate

/-!
# The mold `ovum`

`+validate-ovum` slams the mold `ovum` (arm `685` of `vcore`) on a `%full`, a
`%jets` or a `%fast`.  The mold is a `$%`: a switch on the head of its sample,
whose branch for `%jets` is large because of `jets-comp-info`.  Only the
branches for `%full` and `%fast` are followed here: on a `%full` the mold
returns only when the tail is a cell (`mold_full`), on a `%fast` only when
the tail is a flag and a noun (`mold_fast`).  Together they are `OvumMold` of
`Assembly.lean` (`ovumMold_holds`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

/-- The battery of the gate that the arm `ovum` builds. -/
def ovumBat : Noun :=
  C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 1819047270)) (C (A 0) (A 12)))) (C (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 12)) (C (A 1) (A 1819047270)))) (C (C (A 1) (A 1819047270)) (C (A 0) (A 0))))) (C (C (A 0) (A 26)) (C (C (A 0) (A 54)) (C (A 0) (A 55))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 1937007978)) (C (A 0) (A 12)))) (C (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 12)) (C (A 1) (A 1937007978)))) (C (C (A 1) (A 1937007978)) (C (A 0) (A 0))))) (C (A 8) (C (C (A 7) (C (C (A 0) (A 7)) (C (A 8) (C (C (A 9) (C (A 1407) (C (A 0) (A 524287)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 348) (C (A 0) (A 524287)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 383) (C (A 0) (A 127)))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 343) (C (A 0) (A 15)))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 1701996900)) (C (A 0) (A 12)))) (C (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 12)) (C (A 1) (A 1701996900)))) (C (C (A 1) (A 1701996900)) (C (A 0) (A 0))))) (C (C (A 8) (C (C (A 7) (C (C (A 0) (A 7)) (C (A 9) (C (A 382) (C (A 0) (A 127)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 27)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 27)))) (C (C (A 1) (A 1)) (C (A 0) (A 0)))))))))) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 12)) (C (A 1) (A 1953718630)))) (C (C (A 1) (A 1953718630)) (C (A 0) (A 0))))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 26)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 26)))) (C (C (A 1) (A 1)) (C (A 0) (A 0)))))))) (C (A 8) (C (C (A 7) (C (C (A 0) (A 7)) (C (A 8) (C (C (A 9) (C (A 1407) (C (A 0) (A 524287)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (A 1) (A 0)))) (C (C (A 1) (C (A 8) (C (C (C (A 8) (C (C (A 7) (C (C (A 0) (A 7)) (C (A 9) (C (A 12222) (C (A 0) (A 262143)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 7) (C (C (A 0) (A 7)) (C (A 9) (C (A 11) (C (A 0) (A 511)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2))))))))) (C (A 8) (C (C (A 5) (C (C (A 0) (A 14)) (C (A 0) (A 2)))) (C (A 0) (A 6))))))) (C (A 0) (A 1)))))))) (C (A 0) (A 2)))))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))))))))) (C (A 8) (C (C (A 5) (C (C (A 0) (A 14)) (C (A 0) (A 2)))) (C (A 0) (A 6)))))

/-- The arm `ovum`: the gate with the bunt `[%fast %.y ~]` as its sample. -/
def ovumArm : Noun :=
  C (A 8) (C (C (A 1) (C (A Tag.fast) (C (A 0) (A 0)))) (C (C (A 1) ovumBat) (C (A 0) (A 1))))

theorem vcore_ovumArm : slot? 685 vcore = some ovumArm := by kernel_rfl

theorem slamAt_mold (sam : Noun) :
    slamAt vcore 685 sam = nock (C ovumBat (C sam vcore)) ovumBat := by
  simp only [slamAt, vcore_ovumArm, Option.bind_some]
  unfold ovumArm
  simp [nock_exec]

/-- On a `%full`, the mold returns only when the tail is a cell. -/
theorem mold_full (tl w : Noun) (h : slamAt vcore 685 (C (A Tag.full) tl) = some w) :
    ∃ s f, tl = C s f := by
  rw [slamAt_mold] at h
  rcases tl with a | ⟨s, f⟩
  · exfalso
    conv at h => lhs; arg 2; unfold ovumBat
    simp [nock_exec, Tag.full] at h
  · exact ⟨s, f, rfl⟩

/-- On a `%fast`, the mold returns only when the tail is a flag and a noun. -/
theorem mold_fast (tl w : Noun) (h : slamAt vcore 685 (C (A Tag.fast) tl) = some w) :
    ∃ r p, tl = C (flag r) p := by
  rw [slamAt_mold] at h
  rcases tl with a | ⟨x, p⟩
  · exfalso
    conv at h => lhs; arg 2; unfold ovumBat
    simp [nock_exec, Tag.fast] at h
  · rcases x with a | ⟨x₁, x₂⟩
    · rcases (by omega : a = 0 ∨ a = 1 ∨ 2 ≤ a) with rfl | rfl | ha
      · exact ⟨true, p, rfl⟩
      · exact ⟨false, p, rfl⟩
      · exfalso
        have h1 : ¬ (1 = a) := by omega
        have h0 : ¬ (0 = a) := by omega
        conv at h => lhs; arg 2; unfold ovumBat
        simp [nock_exec, Tag.fast, h0, h1] at h
    · exfalso
      conv at h => lhs; arg 2; unfold ovumBat
      simp [nock_exec, Tag.fast] at h

end Compiler
end Formalization
