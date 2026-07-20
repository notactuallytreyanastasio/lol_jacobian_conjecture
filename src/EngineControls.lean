/- Control tests for the symbolic engine: known determinants. -/
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
def C (c : Int) : Poly := norm [((0,0,0), c)]
def dX (p : Poly) : Poly := norm <| p.filterMap fun (⟨e1,e2,e3⟩, c) =>
  if e1 == 0 then none else some ((e1-1, e2, e3), c * (e1 : Int))
def dY (p : Poly) : Poly := norm <| p.filterMap fun (⟨e1,e2,e3⟩, c) =>
  if e2 == 0 then none else some ((e1, e2-1, e3), c * (e2 : Int))
def dZ (p : Poly) : Poly := norm <| p.filterMap fun (⟨e1,e2,e3⟩, c) =>
  if e3 == 0 then none else some ((e1, e2, e3-1), c * (e3 : Int))
def det3 (a b c d e f g h i : Poly) : Poly :=
  padd (padd (pmul a (psub (pmul e i) (pmul f h)))
             (pscale (-1) (pmul b (psub (pmul d i) (pmul f g)))))
       (pmul c (psub (pmul d h) (pmul e g)))
def jac (G1 G2 G3 : Poly) : Poly :=
  det3 (dX G1) (dY G1) (dZ G1) (dX G2) (dY G2) (dZ G2) (dX G3) (dY G3) (dZ G3)

-- control 1: identity map (x,y,z) → det = 1
#eval jac X Y Z
-- control 2: (x², y, z) → det = 2x  → [((1,0,0),2)]
#eval jac (ppow X 2) Y Z
-- control 3: swap (y, x, z) → det = -1
#eval jac Y X Z
-- control 4: (x+y², y+z², z+x²) → det = 1 + 8xyz  (known)
#eval jac (padd X (ppow Y 2)) (padd Y (ppow Z 2)) (padd Z (ppow X 2))
-- control 5: multiplication check  (x+1)²·(x-1) expand  → x³+x²-x-1
#eval pmul (ppow (padd X (C 1)) 2) (psub X (C 1))
