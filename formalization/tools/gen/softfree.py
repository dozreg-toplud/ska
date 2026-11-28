"""The nouns of `+soft-free` (line 5490) in `CompSccLoopSoftTryFree.lean` (README Gaps 21.22): the arm at
battery slot 882367 of `comp.door` (`tf_at`) and its parts `tfBunt` .. `tfRec2`, `tfG1Bat`, `tfG1Bunt`, printed
as Lean definitions for that file (paste over the old ones after a pill switch; `tf_at` checks the slot).

    tools/capped.sh -m 3G python3 tools/gen/softfree.py
"""
import sys
sys.path.insert(0,'/home/kirill/work/ska-scratch/wt/ska-formalization-i/formalization/tools/gen')
import nouns
from nouns import slot, norm, lean
door=nouns.get('comp.door')
arm=norm(slot(882367,door))
def sl(a,n): 
    r=slot(a,n); return norm(r)
P={}
P['tfArm']=arm
P['tfBunt']=sl(13,arm)
P['tfBat']=sl(29,arm)
R1=sl(7,P['tfBat']); R2=sl(7,R1)
P['tfTrap']=sl(13,R2)
T=P['tfTrap']
P['tfR1']=sl(15,T)
P['tfOr']=sl(6,P['tfR1']); P['tfRec1']=sl(14,P['tfR1']); P['tfR2']=sl(15,P['tfR1'])
P['tfGot']=sl(6,P['tfR2']); P['tfR3']=sl(7,P['tfR2'])
P['tfLien']=sl(6,P['tfR3']); P['tfR4']=sl(15,P['tfR3'])
P['tfNex']=sl(6,P['tfR4']); P['tfR5']=sl(7,P['tfR4'])
P['tfRec2']=sl(15,P['tfR5'])
# the inner gate literal in tfLien
def find(n):
    n=norm(n)
    if n[0]!='C': return None
    if n[1]==('A',8) or norm(n[1])==('A',8):
        x=norm(n[2])
        if x[0]=='C':
            a=norm(x[1]); b=norm(x[2])
            if a[0]=='C' and norm(a[1])==('A',1) and b[0]=='C':
                b1=norm(b[1]); b2=norm(b[2])
                if b1[0]=='C' and norm(b1[1])==('A',1) and nouns.eqn(b2,('C',('A',0),('A',1))):
                    return (norm(a[2]), norm(b1[2]))
    return find(n[1]) or find(n[2])
bu,gb=find(P['tfLien'])
P['tfG1Bunt']=bu; P['tfG1Bat']=gb
order=['tfArm','tfBat','tfTrap','tfR1','tfR2','tfR3','tfR4','tfR5','tfRec2','tfNex','tfLien','tfG1Bat','tfG1Bunt','tfGot','tfRec1','tfOr','tfBunt']
out=[]
for nm in reversed(order):
    sub=[(k,P[k]) for k in order if k!=nm and order.index(k)>order.index(nm)]
    # only names defined before (smaller pieces), largest first
    out.append('def %s : Noun :=\n  %s\n' % (nm, lean(P[nm], sub)))
print('\n'.join(out))
