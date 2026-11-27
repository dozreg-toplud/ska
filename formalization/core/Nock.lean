module
/-  Nock 4K

A noun is an atom or a cell. An atom is a natural number. A cell is an ordered pair of nouns.

Reduce by the first matching pattern; variables match any noun.

nock(a)             *a
[a b c]             [a [b c]]

?[a b]              0
?a                  1
+[a b]              +[a b]
+a                  1 + a
=[a a]              0
=[a b]              1

/[1 a]              a
/[2 a b]            a
/[3 a b]            b
/[(a + a) b]        /[2 /[a b]]
/[(a + a + 1) b]    /[3 /[a b]]
/a                  /a

#[1 a b]            a
#[(a + a) b c]      #[a [b /[(a + a + 1) c]] c]
#[(a + a + 1) b c]  #[a [/[(a + a) c] b] c]
#a                  #a

*[a [b c] d]        [*[a b c] *[a d]]

*[a 0 b]            /[b a]
*[a 1 b]            b
*[a 2 b c]          *[*[a b] *[a c]]
*[a 3 b]            ?*[a b]
*[a 4 b]            +*[a b]
*[a 5 b c]          =[*[a b] *[a c]]

*[a 6 b c d]        *[a *[[c d] 0 *[[2 3] 0 *[a 4 4 b]]]]
*[a 7 b c]          *[*[a b] c]
*[a 8 b c]          *[[*[a b] a] c]
*[a 9 b c]          *[*[a c] 2 [0 1] 0 b]
*[a 10 [b c] d]     #[b *[a c] *[a d]]

*[a 11 [b c] d]     *[[*[a c] *[a d]] 0 3]
*[a 11 b c]         *[a c]

*a                  *a
-/

@[expose] public section

namespace Formalization
namespace Nock

inductive Noun where
    | atom : Nat -> Noun
    | cell : Noun -> Noun -> Noun
    deriving DecidableEq, Repr

abbrev A : Nat -> Noun := Noun.atom
abbrev C : Noun -> Noun -> Noun := Noun.cell
abbrev T2 (t : Nat) (x : Noun) : Noun := C (A t) x
abbrev T3 (t : Nat) (x y : Noun) : Noun := C (A t) (C x y)
abbrev T4 (t : Nat) (x y z : Noun) : Noun := C (A t) (C x (C y z))

-- ?[a b]       0
-- ?a           1
def Wut : Noun -> Noun
    | Noun.cell _ _ => A 0
    | _ => A 1

-- +[a b]       +[a b]
-- +a           1 + a
def Lus: Noun -> Noun -> Prop
    | Noun.cell _ _, _ => False
    | Noun.atom a, p => p = A (1 + a)


-- =[a a] = 0
-- =[a b] = 1
def Tis (a b : Noun) : Noun :=
    if a = b then A 0 else A 1

-- /[1 a]               a
-- /[2 a b]             a
-- /[3 a b]             b
-- /[(a + a) b]         /[2 /[a b]]
-- /[(a + a + 1) b]     /[3 /[a b]]
inductive Fas : Noun -> Noun -> Noun -> Prop where
    | one {a} :   Fas (A 1) a a
    | two {a b} : Fas (A 2) (C a b) a
    | three {a b} : Fas (A 3) (C a b) b
    | left {a b p q n} :
        Fas a b p ->
        Fas (A 2) p q ->
        a = A n ->
        Fas (A (n + n)) b q
    | right {a b p q n} :
        Fas a b p ->
        Fas (A 3) p q ->
        a = A n ->
        Fas (A (n + n + 1)) b q

-- #[1 a b]            a
-- #[(a + a) b c]      #[a [b /[(a + a + 1) c]] c]
-- #[(a + a + 1) b c]  #[a [/[(a + a) c] b] c]
-- #a                  #a
inductive Hax : Noun -> Noun -> Noun -> Noun -> Prop where
    | one {a b} : Hax (A 1) a b a
    | left {a b c p q n} :
        a = A n ->
        Fas (A (n + n + 1)) c p ->
        Hax a (C b p) c q ->
        Hax (A (n + n)) b c q
    | right {a b c p q n} :
        a = A n ->
        Fas (A (n + n)) c p ->
        Hax a (C p b) c q ->
        Hax (A (n + n + 1)) b c q

inductive Nock : Noun -> Noun -> Noun -> Prop where
    | cons {a b c d p q} :
        Nock a (C b c) p ->
        Nock a d q ->
        Nock a (C (C b c) d) (C p q)
    | op0 {a b p} :
        Fas b a p ->
        Nock a (T2 0 b) p
    | op1 {a b} :
        Nock a (T2 1 b) b
    | op2 {a b c p q r} :
        Nock a b p ->
        Nock a c q ->
        Nock p q r ->
        Nock a (T3 2 b c) r
    | op3 {a b p q} :
        Nock a b p ->
        q = (Wut p) ->
        Nock a (T2 3 b) q
    | op4 {a b p q} :
        Nock a b p ->
        Lus p q ->
        Nock a (T2 4 b) q
    | op5 {a b c p q r} :
        Nock a b p ->
        Nock a c q ->
        r = Tis p q ->
        Nock a (T3 5 b c) r
    | op6 {a b c d p q r s} :
        Nock a (C (A 4) (C (A 4) b)) p ->
        Nock (C (A 2) (A 3)) (T2 0 p) q ->
        Nock (C c d) (T2 0 q) r ->
        Nock a r s ->
        Nock a (T4 6 b c d) s
    | op7 {a b c p q} :
        Nock a b p ->
        Nock p c q ->
        Nock a (T3 7 b c) q
    | op8 {a b c p q} :
        Nock a b p ->
        Nock (C p a) c q ->
        Nock a (T3 8 b c) q
    | op9 {a b c p q} :
        Nock a c p ->
        Nock p (T3 2 (T2 0 (A 1)) (T2 0 b)) q ->
        Nock a (T3 9 b c) q
    | op10 {a b c d p q r} :
        Nock a c p ->
        Nock a d q ->
        Hax b p q r ->
        Nock a (T3 10 (C b c) d) r
    | op11cell {a b c d p q r} :
        Nock a c p ->
        Nock a d q ->
        Nock (C p q) (T2 0 (A 3)) r ->
        Nock a (T3 11 (C b c) d) r
    | op11atom {a c p n} :
        Nock a c p ->
        Nock a (T3 11 (A n) c) p

end Nock
end Formalization
