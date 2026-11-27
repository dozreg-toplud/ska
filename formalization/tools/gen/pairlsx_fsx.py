import sys
D = 'lemmas/Ska/'
src = open(D + 'CompFrontS.lean').read()
i = src.index('theorem frontS_pair ')
j = src.index('/-! ## The fronts of a run and the relation -/')
body = src[i:j]
old_stmt = body[:body.index(':= by') + len(':= by')]
new_stmt = open(sys.argv[1]).read().rstrip('\n')
body = body.replace(old_stmt, new_stmt)


def rep(o, n, c=1):
    global body
    assert body.count(o) == c, (o, body.count(o))
    body = body.replace(o, n)


rep('''    obtain ⟨vp, vq, dp, dq, wp, wq, rfl, rfl, rfl, qp, qq⟩ := hq
    rcases hd with hd | hd
    · have := hdp s vp dp wp r qp hd''', '''    obtain ⟨vp, vq, dp, dq, wp, wq, rfl, rfl, rfl, qp, qq⟩ := hq
    rcases hd with hd | hd | hd
    · obtain ⟨a1, a2, a3, a4, _⟩ := hH r hd
      rcases hM r hm with a | a | ⟨a, _⟩
      · exact a3 a
      · exact a4 a
      · omega
    · have := hdp s vp dp wp r qp hd''')
rep('''    intro lib σ O c gul st t R s v d w hq hM' hd hE
    obtain ⟨vp, vq, dp, dq, wp, wq, rfl, rfl, rfl, qp, qq⟩ := hq
    have hdp' : HoldsN dp R wp := hd.1
    have hdq' : HoldsN dq R wq := hd.2''', '''    intro lib σ O c gul st t R s v d w hq hM' hd hE
    obtain ⟨vp, vq, dp, dq, wp, wq, rfl, rfl, rfl, qp, qq⟩ := hq
    have hdp' : HoldsN dp R wp := hd.2.1
    have hdq' : HoldsN dq R wq := hd.2.2
    obtain ⟨ep0, eq0⟩ := hEH R vp vq hE hd.1''')
rep('''    have Hp := FP.run lib σ O c gul st t R1 s vp dp wp qp ⟨hp1, lkp⟩ dp1 trivial''', '''    have nLp_E : ∀ x, NMem Ep x → ¬ NMem (Need.pair Lp.ned Lq.ned) x := fun x hx hm => by
      rcases hm with hm | hm
      · exact (hEp x hx).1 hm
      · exact (hEp x hx).2 hm
    have nLq_E : ∀ x, NMem Eq x → ¬ NMem (Need.pair Lp.ned Lq.ned) x := fun x hx hm => by
      rcases hm with hm | hm
      · exact (hEq x hx).2.1 hm
      · exact (hEq x hx).2.2.1 hm
    have ep1 : HoldsN Ep R1 vp := HoldsN.agree Ep (fun x hx => k1 x (nLp_E x hx)) ep0
    have eq1 : HoldsN Eq R1 vq := HoldsN.agree Eq (fun x hx => k1 x (nLq_E x hx)) eq0
    have Hp := FP.run lib σ O c gul st t R1 s vp dp wp qp ⟨hp1, lkp⟩ dp1 ep1''')
rep('''    have keepC : ∀ x, (x < lo0 ∨ lo ≤ x ∨ NMem (Need.pair dp dq) x) → ¬ NMem Lb.ned x →
        SkaModel.read x R1 = SkaModel.read x R := fun x hx hnx => by
      refine k1 x fun hm => ?_
      rcases hx with hx | hx | hx | hx''', '''    have keepC : ∀ x, (x < lo0 ∨ lo ≤ x ∨ NMem (Need.pair H (Need.pair dp dq)) x) → ¬ NMem Lb.ned x →
        SkaModel.read x R1 = SkaModel.read x R := fun x hx hnx => by
      refine k1 x fun hm => ?_
      rcases hx with hx | hx | hx | hx | hx''')
rep('''        · have := (lqL x hm).1; omega
      · exact nLp_dp x hx hm
      · exact nLp_dq x hx hm''', '''        · have := (lqL x hm).1; omega
      · rcases hm with hm | hm
        · exact (hH x hx).2.2.1 hm
        · exact (hH x hx).2.2.2.1 hm
      · exact nLp_dp x hx hm
      · exact nLp_dq x hx hm''')


def eq2(ind):
    a = ' ' * ind
    return (a + 'have eq2 : HoldsN Eq R2 vq := HoldsN.agree Eq (fun x hx => by\n' +
            a + '  have := (hEq x hx).1\n' +
            a + '  exact k2 x (Or.inl (by omega)) (hEq x hx).2.2.2) eq1\n')


rep('''        exact k2 x (Or.inl (by omega)) fun hm => by have := (hLh x hm).1; omega) dq1
      obtain ⟨R3, r3, ht3, k3⟩ := (FQ.run lib σ O c gul st t R2 s vq dq wq qq q2 dq2 trivial).1 ft''',
    '''        exact k2 x (Or.inl (by omega)) fun hm => by have := (hLh x hm).1; omega) dq1
''' + eq2(6) + '''      obtain ⟨R3, r3, ht3, k3⟩ := (FQ.run lib σ O c gul st t R2 s vq dq wq qq q2 dq2 eq2).1 ft''')
rep('''      have nt : ¬ NMem Lt.ned x := fun hm => by
        rcases hx with hx | hx | hx | hx
        · exact hnx ((hLt x hm).2 hx)
        · have := (hLt x hm).1; omega''', '''      have nt : ¬ NMem Lt.ned x := fun hm => by
        rcases hx with hx | hx | hx | hx | hx
        · exact hnx ((hLt x hm).2 hx)
        · have := (hLt x hm).1; omega
        · exact (hH x hx).2.2.2.2.2 hm''')
rep('''      have nh : ¬ NMem Lh.ned x := fun hm => by
        rcases hx with hx | hx | hx | hx
        · exact hnx ((hLh x hm).2 hx)
        · have := (hLh x hm).1; omega''', '''      have nh : ¬ NMem Lh.ned x := fun hm => by
        rcases hx with hx | hx | hx | hx | hx
        · exact hnx ((hLh x hm).2 hx)
        · have := (hLh x hm).1; omega
        · exact (hH x hx).2.2.2.2.1 hm''')
rep('''      · rcases hx with hx | hx | hx | hx
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr hx)
        · have := hdq s vq dq wq x qq hx; exact Or.inl (by omega)
      · rcases hx with hx | hx | hx | hx
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · have := hdp s vp dp wp x qp hx; exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr hx)''', '''      · rcases hx with hx | hx | hx | hx | hx
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · have := (hH x hx).2.1; exact Or.inl (by omega)
        · exact Or.inr (Or.inr hx)
        · have := hdq s vq dq wq x qq hx; exact Or.inl (by omega)
      · rcases hx with hx | hx | hx | hx | hx
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · have := (hH x hx).2.1; exact Or.inl (by omega)
        · have := hdp s vp dp wp x qp hx; exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr hx)''')
rep('''          exact k2 x (Or.inl (by omega)) fun hm => by have := (hLh x hm).1; omega) dq1
        have := Crashes.append_left (B := Fs)
          (Crashes.append_right (r1.append r2) ((FQ.run lib σ O c gul st t R2 s vq dq wq qq q2 dq2 trivial).2 ft))''',
    '''          exact k2 x (Or.inl (by omega)) fun hm => by have := (hLh x hm).1; omega) dq1
''' + eq2(8) + '''        have := Crashes.append_left (B := Fs)
          (Crashes.append_right (r1.append r2) ((FQ.run lib σ O c gul st t R2 s vq dq wq qq q2 dq2 eq2).2 ft))''')
head = open(sys.argv[2]).read()
out = head + body.rstrip() + '''

end Comp
end SkaModel
end Formalization
'''
open(D + 'CompFrontSX.lean', 'w').write(out)
print('ok')
