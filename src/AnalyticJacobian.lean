/-
  Exact analytic Jacobian, hand-differentiated (independent of the polynomial
  engine AND of finite differences). Evaluated with exact rationals.
  u = 1+xy.  Partials of F1,F2,F3:
-/
structure Q where
  num : Int
  den : Int
deriving Repr
def gcdI (a b : Int) : Int := Int.ofNat (Nat.gcd a.natAbs b.natAbs)
def qmk (n d : Int) : Q :=
  let s : Int := if d < 0 then -1 else 1
  let n := n*s; let d := d*s
  let g := gcdI n d; let g := if g==0 then 1 else g
  { num := n/g, den := d/g }
def qadd (a b : Q) : Q := qmk (a.num*b.den + b.num*a.den) (a.den*b.den)
def qsub (a b : Q) : Q := qmk (a.num*b.den - b.num*a.den) (a.den*b.den)
def qmul (a b : Q) : Q := qmk (a.num*b.num) (a.den*b.den)
def qpow (a : Q) : Nat → Q | 0 => qmk 1 1 | (n+1) => qmul a (qpow a n)
def I (n : Int) : Q := qmk n 1
instance : OfNat Q n := ⟨qmk (Int.ofNat n) 1⟩
instance : Add Q := ⟨qadd⟩
instance : Sub Q := ⟨qsub⟩
instance : Mul Q := ⟨qmul⟩

def det (x y z : Q) : Q :=
  let u := 1 + x*y
  -- ∂F1
  let a1 := 3*y*u*u*z + I 7*qpow y 3 + I 6*x*qpow y 4
  let b1 := 3*x*u*u*z + I 8*y + I 21*x*qpow y 2 + I 12*qpow x 2*qpow y 3
  let c1 := qpow u 3
  -- ∂F2
  let a2 := 3*u*u*z + I 6*x*y*u*z + I 12*qpow y 2 + I 18*x*qpow y 3
  let b2 := 1 + I 6*qpow x 2*u*z + I 24*x*y + I 27*qpow x 2*qpow y 2
  let c2 := 3*x*u*u
  -- ∂F3
  let a3 := 2 - I 6*x*y - 3*qpow x 2*z
  let b3 := (I (-3))*qpow x 2
  let c3 := (I (-1))*qpow x 3
  a1*(b2*c3 - c2*b3) - b1*(a2*c3 - c2*a3) + c1*(a2*b3 - b2*a3)

#eval det 5 7 (I (-3))
#eval det 2 1 1
#eval det (I (-3)) 4 9
#eval det 10 (I (-6)) 2
#eval det 0 0 (qmk (-1) 4)
