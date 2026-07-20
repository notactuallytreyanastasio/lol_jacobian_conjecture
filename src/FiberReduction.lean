/-
  Fiber analysis of F in pure Lean 4 core.

  Strategy: solving F(x,y,z)=(p,q,r) for x ≠ 0, with t := x*y, collapses (proved
  below as two symbolic polynomial identities) to
     (A*)  q x² - (6+4t) x + 3 r (1+t)²        = 0
     (B*)  p x³ - (t²+3t+2) x + r (1+t)³        = 0
  We (1) PROVE (A*),(B*) hold identically for (p,q,r)=F(x,y,z), t=xy;
     (2) exhibit the full fiber over (-1/4,0,0);
     (3) count the generic fiber via the resultant of (A*),(B*).
-/

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
  let nz := merged.filter (fun kv => kv.2 != 0)
  nz.toArray.qsort (fun a b => monoLt a.1 b.1) |>.toList

def padd (p q : Poly) : Poly := norm (p ++ q)
def pscale (c : Int) (p : Poly) : Poly := norm (p.map (fun (m, d) => (m, c * d)))
def pmul (p q : Poly) : Poly :=
  norm <| p.flatMap fun (⟨a1,a2,a3⟩, c) =>
    q.map fun (⟨b1,b2,b3⟩, d) => ((a1+b1, a2+b2, a3+b3), c * d)
def psub (p q : Poly) : Poly := padd p (pscale (-1) q)
def ppow (p : Poly) : Nat → Poly
  | 0     => [((0,0,0), 1)]
  | (n+1) => pmul p (ppow p n)

def X : Poly := [((1,0,0), 1)]
def Y : Poly := [((0,1,0), 1)]        -- doubles as t in the resultant section
def Z : Poly := [((0,0,1), 1)]
def C (c : Int) : Poly := norm [((0,0,0), c)]

def U : Poly := padd (C 1) (pmul X Y)  -- u = 1 + x y

def F1 : Poly := padd (pmul (ppow U 3) Z)
                      (pmul (pmul (ppow Y 2) U) (padd (C 4) (pscale 3 (pmul X Y))))
def F2 : Poly := padd (padd Y (pmul (pscale 3 (pmul X (ppow U 2))) Z))
                      (pmul (pscale 3 (pmul X (ppow Y 2))) (padd (C 4) (pscale 3 (pmul X Y))))
def F3 : Poly := psub (pscale 2 X) (padd (pmul (pscale 3 (ppow X 2)) Y) (pmul (ppow X 3) Z))

-- ===== (1) PROVE the reduction: both must print []  (the zero polynomial) =====
-- (A*):  F2·x² − (6+4t)·x + 3·F3·(1+t)²  ≡ 0     (t = x y)
def idA : Poly :=
  padd (pmul F2 (ppow X 2))
    (padd (pscale (-1) (pmul (padd (C 6) (pscale 4 (pmul X Y))) X))
          (pscale 3 (pmul F3 (ppow U 2))))
-- (B*):  F1·x³ − (t²+3t+2)·x + F3·(1+t)³  ≡ 0
def idB : Poly :=
  padd (pmul F1 (ppow X 3))
    (padd (pscale (-1) (pmul (pmul (padd (C 1) (pmul X Y)) (padd (C 2) (pmul X Y))) X))
          (pmul F3 (ppow U 3)))

#eval idA   -- expect []
#eval idB   -- expect []

-- ===== (2) Fiber over (-1/4, 0, 0): rational-eval machinery =====
structure Q where
  num : Int
  den : Int
deriving Repr
def gcdI (a b : Int) : Int := Int.ofNat (Nat.gcd a.natAbs b.natAbs)
def qmk (n d : Int) : Q :=
  let s : Int := if d < 0 then -1 else 1
  let n := n * s; let d := d * s
  let g := gcdI n d
  let g := if g == 0 then 1 else g
  { num := n / g, den := d / g }
def qadd (a b : Q) : Q := qmk (a.num*b.den + b.num*a.den) (a.den*b.den)
def qmul (a b : Q) : Q := qmk (a.num*b.num) (a.den*b.den)
def qpow (a : Q) : Nat → Q | 0 => qmk 1 1 | (n+1) => qmul a (qpow a n)
def qOfInt (c : Int) : Q := qmk c 1
def evalQ (p : Poly) (x y z : Q) : Q :=
  p.foldl (init := qmk 0 1) fun acc (⟨e1,e2,e3⟩, c) =>
    qadd acc (qmul (qOfInt c) (qmul (qpow x e1) (qmul (qpow y e2) (qpow z e3))))
def evalF (x y z : Q) : Q × Q × Q := (evalQ F1 x y z, evalQ F2 x y z, evalQ F3 x y z)

-- three claimed preimages of (-1/4,0,0)
#eval evalF (qmk 0 1)   (qmk 0 1)   (qmk (-1) 4)   -- (0,   0,   -1/4)
#eval evalF (qmk 1 1)   (qmk (-3) 2)(qmk 13 2)     -- (1,  -3/2,  13/2)
#eval evalF (qmk (-1) 1)(qmk 3 2)   (qmk 13 2)     -- (-1,  3/2,  13/2)

-- ===== (3) Generic fiber: resultant of (A*),(B*) in x, at target (57,115,-16)=F(2,1,1) =====
-- coefficients are polynomials in t (represented with the Y variable)
def a2 : Poly := C 115
def a1 : Poly := padd (C (-6)) (pscale (-4) Y)
def a0 : Poly := pscale (-48) (ppow (padd (C 1) Y) 2)
def b3 : Poly := C 57
def b2 : Poly := C 0
def b1 : Poly := pscale (-1) (padd (padd (ppow Y 2) (pscale 3 Y)) (C 2))
def b0 : Poly := pscale (-16) (ppow (padd (C 1) Y) 3)

-- general n×n determinant over the Poly ring (cofactor expansion, first row)
partial def detN (m : List (List Poly)) : Poly :=
  match m with
  | []        => C 1
  | [row]     => match row with | [a] => a | _ => C 0
  | (row0 :: rest) =>
    let n := row0.length
    (List.range n).foldl (init := C 0) fun acc j =>
      let sign : Int := if j % 2 == 0 then 1 else -1
      let minor := rest.map (fun r => (r.zipIdx.filter (fun p => p.2 ≠ j)).map (fun p => p.1))
      padd acc (pscale sign (pmul (row0[j]!) (detN minor)))

def O : Poly := C 0
def sylv : List (List Poly) :=
  [ [a2, a1, a0, O,  O ],
    [O,  a2, a1, a0, O ],
    [O,  O,  a2, a1, a0],
    [b3, b2, b1, b0, O ],
    [O,  b3, b2, b1, b0] ]

#eval detN sylv   -- resultant_x(t): roots in t = t-values of preimages of (57,115,-16)
