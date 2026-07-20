/-
================================================================================
  A candidate counterexample to the COMPLEX Jacobian Conjecture, machine-checked.
================================================================================
  Jacobian Conjecture (char 0 / ℂ):  a polynomial map F : ℂⁿ → ℂⁿ whose Jacobian
  determinant is a nonzero constant is bijective (with polynomial inverse).

  For  F : ℚ³ → ℚ³ ⊂ ℂ³  below we machine-verify, in exact arithmetic:
    (F1)  det J(F) ≡ -2                    — a nonzero CONSTANT  (symbolic identity)
    (F2)  F(0,0,-1/4) = F(1,-3/2,13/2)
                       = F(-1,3/2,13/2) = (-1/4, 0, 0)   — NOT injective
  These two facts, with the standard definitions, are LOGICALLY INCOMPATIBLE with
  the Jacobian Conjecture over ℂ.  This file certifies the ARITHMETIC only; whether
  that constitutes a genuine refutation is a separate question flagged in prose.
================================================================================
-/

-------------------------------------------------- ℤ[x,y,z], fully expanded
abbrev Mono := Nat × Nat × Nat
abbrev Poly := List (Mono × Int)
def monoLt (a b : Mono) : Bool :=
  let (a1,a2,a3) := a; let (b1,b2,b3) := b
  a1 < b1 || (a1 == b1 && (a2 < b2 || (a2 == b2 && a3 < b3)))
def norm (p : Poly) : Poly :=
  let merged := p.foldl (init := ([] : Poly)) fun acc (m, c) =>
    match acc.find? (fun kv => kv.1 == m) with
    | some (_, c0) => (acc.filter (fun kv => kv.1 != m)) ++ [(m, c0 + c)]
    | none         => acc ++ [(m, c)]
  (merged.filter (fun kv => kv.2 != 0)).toArray.qsort (fun a b => monoLt a.1 b.1) |>.toList
def padd (p q : Poly) : Poly := norm (p ++ q)
def pscale (c : Int) (p : Poly) : Poly := norm (p.map (fun (m, d) => (m, c * d)))
def pmul (p q : Poly) : Poly :=
  norm <| p.flatMap fun (⟨a1,a2,a3⟩, c) =>
    q.map fun (⟨b1,b2,b3⟩, d) => ((a1+b1, a2+b2, a3+b3), c * d)
def psub (p q : Poly) : Poly := padd p (pscale (-1) q)
def ppow (p : Poly) : Nat → Poly | 0 => [((0,0,0),1)] | (n+1) => pmul p (ppow p n)
def X : Poly := [((1,0,0), 1)]
def Y : Poly := [((0,1,0), 1)]
def Z : Poly := [((0,0,1), 1)]
def CC (c : Int) : Poly := norm [((0,0,0), c)]
def dX (p : Poly) : Poly := norm <| p.filterMap fun (⟨e1,e2,e3⟩, c) =>
  if e1 == 0 then none else some ((e1-1, e2, e3), c * (e1 : Int))
def dY (p : Poly) : Poly := norm <| p.filterMap fun (⟨e1,e2,e3⟩, c) =>
  if e2 == 0 then none else some ((e1, e2-1, e3), c * (e2 : Int))
def dZ (p : Poly) : Poly := norm <| p.filterMap fun (⟨e1,e2,e3⟩, c) =>
  if e3 == 0 then none else some ((e1, e2, e3-1), c * (e3 : Int))

-- the map F
def U : Poly := padd (CC 1) (pmul X Y)
def F1 : Poly := padd (pmul (ppow U 3) Z) (pmul (pmul (ppow Y 2) U) (padd (CC 4) (pscale 3 (pmul X Y))))
def F2 : Poly := padd (padd Y (pmul (pscale 3 (pmul X (ppow U 2))) Z)) (pmul (pscale 3 (pmul X (ppow Y 2))) (padd (CC 4) (pscale 3 (pmul X Y))))
def F3 : Poly := psub (pscale 2 X) (padd (pmul (pscale 3 (ppow X 2)) Y) (pmul (ppow X 3) Z))
def det3 (a b c d e f g h i : Poly) : Poly :=
  padd (padd (pmul a (psub (pmul e i) (pmul f h))) (pscale (-1) (pmul b (psub (pmul d i) (pmul f g))))) (pmul c (psub (pmul d h) (pmul e g)))
def detJ : Poly := det3 (dX F1) (dY F1) (dZ F1) (dX F2) (dY F2) (dZ F2) (dX F3) (dY F3) (dZ F3)

-------------------------------------------------- exact ℚ evaluation
structure Q where
  num : Int
  den : Int
deriving Repr, BEq
def gI (a b : Int) : Int := Int.ofNat (Nat.gcd a.natAbs b.natAbs)
def qmk (n d : Int) : Q :=
  let s : Int := if d < 0 then -1 else 1
  let n := n*s; let d := d*s; let g := gI n d; let g := if g==0 then 1 else g
  { num := n/g, den := d/g }
def qadd (a b : Q) : Q := qmk (a.num*b.den + b.num*a.den) (a.den*b.den)
def qmul (a b : Q) : Q := qmk (a.num*b.num) (a.den*b.den)
def qpow (a : Q) : Nat → Q | 0 => qmk 1 1 | (n+1) => qmul a (qpow a n)
def evalQ (p : Poly) (x y z : Q) : Q :=
  p.foldl (init := qmk 0 1) fun acc (⟨e1,e2,e3⟩, c) =>
    qadd acc (qmul (qmk c 1) (qmul (qpow x e1) (qmul (qpow y e2) (qpow z e3))))
def evF (x y z : Q) : Q × Q × Q := (evalQ F1 x y z, evalQ F2 x y z, evalQ F3 x y z)

-------------------------------------------------- Boolean-checkable claims
def isConst (p : Poly) (c : Int) : Bool := p == [((0,0,0), c)]
def eqPt (a b : Q × Q × Q) : Bool :=
  a.1 == b.1 && a.2.1 == b.2.1 && a.2.2 == b.2.2

def V  : Q × Q × Q := (qmk (-1) 4, qmk 0 1, qmk 0 1)
def P1 : Q × Q × Q := evF (qmk 0 1)    (qmk 0 1)    (qmk (-1) 4)
def P2 : Q × Q × Q := evF (qmk 1 1)    (qmk (-3) 2) (qmk 13 2)
def P3 : Q × Q × Q := evF (qmk (-1) 1) (qmk 3 2)    (qmk 13 2)

-- (F1) Jacobian determinant is the nonzero constant -2
def fact_constant_jacobian : Bool := isConst detJ (-2)
-- (F2) three distinct source points share the image V = (-1/4,0,0)  ⇒ non-injective
def fact_non_injective : Bool :=
  eqPt P1 V && eqPt P2 V && eqPt P3 V

-- The Jacobian-Conjecture-incompatibility, as a Boolean:  constant nonzero Jac ∧ ¬injective
def contradicts_JC_over_C : Bool := fact_constant_jacobian && fact_non_injective

#eval detJ                     -- [((0,0,0), -2)]
#eval (P1, P2, P3)             -- all (-1/4, 0, 0)
#eval fact_constant_jacobian   -- true
#eval fact_non_injective       -- true
#eval contradicts_JC_over_C    -- true  ⇐ the arithmetic certifies incompatibility with JC/ℂ
