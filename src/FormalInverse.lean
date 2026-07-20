/-
  THE LAST PIECE: formal power-series inverse of F at the origin, exact ℚ arithmetic.
  F(0)=0 and DF(0)=[[0,0,1],[0,1,0],[2,0,0]] (det -2), so a unique formal inverse
  G with G(0)=0 exists. Iterate  G ← A⁻¹(W − H(G)),  H := F − A·(·),  A⁻¹(w1,w2,w3)=(w3/2,w2,w1).
  Truncate at total degree N. If the number of terms of G keeps growing with N,
  G is a genuine INFINITE series ⇒ F has no polynomial inverse ⇒ F is not an
  automorphism. (An automorphism would make G terminate.)
-/

------------------------------------------------------- exact rationals
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
def qz : Q := qmk 0 1
def qI (n : Int) : Q := qmk n 1

------------------------------------------------------- ℚ-polynomials, truncated at total degree N
abbrev Mono := Nat × Nat × Nat
abbrev QP := List (Mono × Q)
def deg (m : Mono) : Nat := m.1 + m.2.1 + m.2.2
def monoLt (a b : Mono) : Bool :=
  let (a1,a2,a3) := a; let (b1,b2,b3) := b
  a1 < b1 || (a1 == b1 && (a2 < b2 || (a2 == b2 && a3 < b3)))
def qnorm (p : QP) : QP :=
  let merged := p.foldl (init := ([] : QP)) fun acc (m, c) =>
    match acc.find? (fun kv => kv.1 == m) with
    | some (_, c0) => (acc.filter (fun kv => kv.1 != m)) ++ [(m, qadd c0 c)]
    | none         => acc ++ [(m, c)]
  (merged.filter (fun kv => kv.2.num != 0)).toArray.qsort (fun a b => monoLt a.1 b.1) |>.toList
def trunc (N : Nat) (p : QP) : QP := p.filter (fun kv => deg kv.1 ≤ N)
def qadd' (N : Nat) (p q : QP) : QP := trunc N (qnorm (p ++ q))
def qscale (c : Q) (p : QP) : QP := qnorm (p.map (fun (m,d) => (m, qmul c d)))
def qmulP (N : Nat) (p q : QP) : QP :=
  trunc N <| qnorm <| p.flatMap fun (⟨a1,a2,a3⟩, c) =>
    q.filterMap fun (⟨b1,b2,b3⟩, d) =>
      if a1+b1+a2+b2+a3+b3 ≤ N then some ((a1+b1,a2+b2,a3+b3), qmul c d) else none
def qsub' (N : Nat) (p q : QP) : QP := qadd' N p (qscale (qI (-1)) q)
def qpowP (N : Nat) (p : QP) : Nat → QP
  | 0 => [((0,0,0), qI 1)]
  | (k+1) => qmulP N p (qpowP N p k)

-- variables
def W1 : QP := [((1,0,0), qI 1)]
def W2 : QP := [((0,1,0), qI 1)]
def W3 : QP := [((0,0,1), qI 1)]
def QC (c : Q) : QP := qnorm [((0,0,0), c)]

-- F components as ℚ-polys (same map)
def U (N : Nat) : QP := qadd' N (QC (qI 1)) (qmulP N W1 W2)
def F1 (N : Nat) : QP := qadd' N (qmulP N (qpowP N (U N) 3) W3)
  (qmulP N (qmulP N (qpowP N W2 2) (U N)) (qadd' N (QC (qI 4)) (qscale (qI 3) (qmulP N W1 W2))))
def F2 (N : Nat) : QP := qadd' N (qadd' N W2 (qmulP N (qscale (qI 3) (qmulP N W1 (qpowP N (U N) 2))) W3))
  (qmulP N (qscale (qI 3) (qmulP N W1 (qpowP N W2 2))) (qadd' N (QC (qI 4)) (qscale (qI 3) (qmulP N W1 W2))))
def F3 (N : Nat) : QP := qsub' N (qscale (qI 2) W1)
  (qadd' N (qmulP N (qscale (qI 3) (qpowP N W1 2)) W2) (qmulP N (qpowP N W1 3) W3))

-- compose: substitute (V1,V2,V3) for (x,y,z) into P
def compose (N : Nat) (P : QP) (V1 V2 V3 : QP) : QP :=
  P.foldl (init := ([] : QP)) fun acc (⟨e1,e2,e3⟩, c) =>
    let term := qmulP N (QC c) (qmulP N (qpowP N V1 e1) (qmulP N (qpowP N V2 e2) (qpowP N V3 e3)))
    qadd' N acc term

-- H(V) = (F1(V)-V3, F2(V)-V2, F3(V)-2 V1)   (higher-order part, degree ≥ 2)
def Hvec (N : Nat) (V1 V2 V3 : QP) : QP × QP × QP :=
  ( qsub' N (compose N (F1 N) V1 V2 V3) V3,
    qsub' N (compose N (F2 N) V1 V2 V3) V2,
    qsub' N (compose N (F3 N) V1 V2 V3) (qscale (qI 2) V1) )

-- A⁻¹ (w1,w2,w3) = (w3/2, w2, w1)
def Ainv (a b c : QP) : QP × QP × QP := (qscale (qmk 1 2) c, b, a)

-- one Newton/substitution step:  G ← A⁻¹(W − H(G))
def step (N : Nat) (G : QP × QP × QP) : QP × QP × QP :=
  let (g1,g2,g3) := G
  let (h1,h2,h3) := Hvec N g1 g2 g3
  Ainv (qsub' N W1 h1) (qsub' N W2 h2) (qsub' N W3 h3)

def iterate (N k : Nat) : QP × QP × QP :=
  Nat.rec (Ainv W1 W2 W3) (fun _ G => step N G) k

-- count nonzero terms and max degree of the three inverse components at truncation N
def sizes (N : Nat) : (Nat × Nat) × (Nat × Nat) × (Nat × Nat) :=
  let (g1,g2,g3) := iterate N (N+1)   -- N+1 iterations converges the truncation
  let f := fun (g : QP) => (g.length, g.foldl (fun m kv => max m (deg kv.1)) 0)
  (f g1, f g2, f g3)

-- SANITY: does the truncated inverse actually invert F up to degree N?  compute G(F(w)) − w, its size (should be 0 if exact-to-degree-N)
def residual (N : Nat) : Nat :=
  let (g1,g2,g3) := iterate N (N+1)
  let r1 := qsub' N (compose N g1 (F1 N) (F2 N) (F3 N)) W1
  let r2 := qsub' N (compose N g2 (F1 N) (F2 N) (F3 N)) W2
  let r3 := qsub' N (compose N g3 (F1 N) (F2 N) (F3 N)) W3
  (qnorm r1).length + (qnorm r2).length + (qnorm r3).length

#eval sizes 2      -- (terms,maxdeg) per component at degree ≤2
#eval sizes 3
#eval sizes 4
#eval sizes 5
#eval residual 4   -- 0 ⇒ G really is the degree-4 inverse; formal inverse valid
