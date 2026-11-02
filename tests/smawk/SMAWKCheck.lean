import CutQueryComplexity.Search.SMAWK

/-! Executable and axiom checks for `CutQueryComplexity.Search.SMAWK`.

Run with `lake env lean tests/smawk/SMAWKCheck.lean`. The randomized part compares
`smawk` and `matrixMin` with brute force on integer Monge matrices and on small
totally monotone matrices with many ties, and checks the evaluation bounds.
-/

open CutQueryComplexity.Search

#print axioms smawk_spec
#print axioms smawk_queryBound
#print axioms matrixMin_spec
#print axioms monge_min_queryBound

namespace SMAWKCheck

/-- A small linear congruential generator. -/
def lcg (s : ℕ) : ℕ := (s * 1103515245 + 12345) % 2147483648

def randList (s : ℕ) (n m : ℕ) : List ℕ × ℕ :=
  (List.range n).foldl (fun (acc, s) _ => let s' := lcg s; (acc ++ [s' / 65536 % m], s')) ([], s)

/-- `A i + B j + Σ_{p ≤ i, q ≥ j} W p q` is Monge for nonnegative `W`. -/
def mongeOf (A B : List ℤ) (W : List (List ℤ)) (i j : ℕ) : ℤ :=
  A.getD i 0 + B.getD j 0 +
    ((List.range (i + 1)).map fun p =>
      ((List.range (B.length)).filter (· ≥ j)).map (fun q => (W.getD p []).getD q 0) |>.sum).sum

def leftmostMin (M : ℕ → ℕ → ℤ) (r : ℕ) (C : List ℕ) : Option ℕ :=
  C.foldl (fun best c => match best with
    | none => some c
    | some b => if M r c < M r b then some c else some b) none

def isTM (M : ℕ → ℕ → ℤ) (R C : List ℕ) : Bool :=
  R.all fun r => R.all fun r' => C.all fun c => C.all fun c' =>
    !(decide (r < r') && decide (c < c') && decide (M r c' < M r c)) || decide (M r' c' < M r' c)

/-- One trial: returns `true` iff SMAWK agrees with brute force within its budget. -/
def check (M : ℕ → ℕ → ℤ) (R C : List ℕ) : Bool :=
  let o := entryOracle M
  let out := (smawk R C).eval o
  let okRows := out == R.map fun r => leftmostMin M r C
  let okCost := (smawk (α := ℤ) R C).cost o ≤ 4 * C.length + 12 * R.length
  let mn := (matrixMin R C).eval o
  let brute := (R.flatMap fun r => C.map fun c => M r c).min?
  let okMin := match mn, brute with
    | some (r, j), some v => M r j == v
    | none, none => true
    | _, _ => false
  let okMinCost := (matrixMin (α := ℤ) R C).cost o ≤ 4 * C.length + 13 * R.length
  okRows && okCost && okMin && okMinCost

def mongeTrials (seed trials : ℕ) : ℕ × ℕ := Id.run do
  let mut s := seed
  let mut pass := 0
  let mut total := 0
  for _ in List.range trials do
    s := lcg s
    let a := s / 65536 % 9 + 1
    s := lcg s
    let b := s / 65536 % 12 + 1
    let (A, s1) := randList s a 7
    let (B, s2) := randList s1 b 7
    let mut W : List (List ℤ) := []
    let mut t := s2
    for _ in List.range a do
      let (row, t') := randList t b 3
      W := W ++ [row.map Int.ofNat]
      t := t'
    s := t
    let M := mongeOf (A.map Int.ofNat) (B.map Int.ofNat) W
    -- full index lists and a gapped column subsequence
    let R := List.range a
    let C := List.range b
    let Cg := C.filter (· % 2 == 0)
    total := total + 2
    if check M R C then pass := pass + 1
    if check M R Cg then pass := pass + 1
  return (pass, total)

/-- Random 0/1/2 matrices on up to 4×5, kept only when totally monotone (many ties). -/
def tmTrials (seed trials : ℕ) : ℕ × ℕ := Id.run do
  let mut s := seed
  let mut pass := 0
  let mut total := 0
  for _ in List.range trials do
    s := lcg s
    let a := s / 65536 % 4 + 1
    s := lcg s
    let b := s / 65536 % 5 + 1
    let (vals, s') := randList s (a * b) 3
    s := s'
    let M : ℕ → ℕ → ℤ := fun i j => Int.ofNat (vals.getD (i * b + j) 0)
    let R := List.range a
    let C := List.range b
    if isTM M R C then
      total := total + 1
      if check M R C then pass := pass + 1
  return (pass, total)

#eval mongeTrials 42 400
#eval tmTrials 7 4000

end SMAWKCheck
