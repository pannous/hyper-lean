-- Clean implementation of HyperReals focused on applications
-- Following the Julia version structure

namespace HyperReals

-- Constants for precision
def TERM_PRECISION : Nat := 60
def TAYLOR_TERMS : Nat := 10
def INTEGRATION_TERMS : Nat := 10000

-- A hyperreal is represented as a list of (coefficient, order/exponent) pairs
-- Example: 3ω² + 1 + 2ε = [(3.0, 2.0), (1.0, 0.0), (2.0, -1.0)]
structure Hyper where
  terms : List (Float × Float)
  deriving Repr, BEq

-- Basic constants
def zero : Hyper := ⟨[]⟩
def one : Hyper := ⟨[(1.0, 0.0)]⟩
def ε : Hyper := ⟨[(1.0, -1.0)]⟩  -- infinitesimal
def ω : Hyper := ⟨[(1.0, 1.0)]⟩   -- infinite

notation "𝟘" => zero
notation "𝟙" => one

-- Convert numbers to Hyper
def fromFloat (x : Float) : Hyper := ⟨[(x, 0.0)]⟩
def fromNat (n : Nat) : Hyper := fromFloat n.toFloat

instance : OfNat Hyper n where
  ofNat := fromNat n

instance : Coe Float Hyper where
  coe := fromFloat

-- Simplify by combining like terms
def simplify (h : Hyper) : Hyper :=
  let combined := h.terms.foldl (fun acc (r, e) =>
    match acc.findIdx? (fun (_, e') => e' == e) with
    | none => acc ++ [(r, e)]
    | some idx =>
      let (r', e') := acc[idx]!
      acc.set idx (r' + r, e')
  ) []
  let filtered := combined.filter (fun (r, _) => r != 0.0)
  ⟨filtered⟩

-- Sort terms by exponent (descending)
def sort (h : Hyper) : Hyper :=
  ⟨h.terms.mergeSort (fun (_, e1) (_, e2) => e1 > e2)⟩

def order (h : Hyper) : Hyper :=
  sort (simplify h)

-- Helper functions (defined early for use in other functions)
def real (h : Hyper) : Float :=
  let simplified := simplify h
  match simplified.terms.find? (fun (_, e) => e == 0.0) with
  | some (r, _) => r
  | none => 0.0

def isFinite (h : Hyper) : Bool :=
  let simplified := simplify h
  simplified.terms.all (fun (_, e) => e <= 0.0)

def isInfinite (h : Hyper) : Bool :=
  let simplified := simplify h
  simplified.terms.any (fun (_, e) => e > 0.0)

-- Addition
def add (x y : Hyper) : Hyper :=
  simplify ⟨x.terms ++ y.terms⟩

instance : Add Hyper where
  add := add

instance : HAdd Hyper Hyper Hyper where
  hAdd := add

-- Negation
def neg (h : Hyper) : Hyper :=
  ⟨h.terms.map (fun (r, e) => (-r, e))⟩

instance : Neg Hyper where
  neg := neg

-- Subtraction
def sub (x y : Hyper) : Hyper :=
  add x (neg y)

instance : Sub Hyper where
  sub := sub

-- Multiplication
def mul (x y : Hyper) : Hyper :=
  let terms := x.terms.flatMap fun (r1, e1) =>
    y.terms.map fun (r2, e2) => (r1 * r2, e1 + e2)
  simplify ⟨terms⟩

instance : Mul Hyper where
  mul := mul

-- Inverse using Newton iteration
partial def inv (h : Hyper) : Hyper :=
  if h.terms.isEmpty then ω  -- 1/0 = ∞
  else
    let sorted := (sort h).terms
    let (a₀, e₀) := sorted.head!
    let x₀ : Hyper := ⟨[(1.0 / a₀, -e₀)]⟩
    -- Newton iteration: x_{n+1} = x_n * (2 - h * x_n)
    let x₁ := x₀ * (fromFloat 2.0 - h * x₀)
    let x₂ := x₁ * (fromFloat 2.0 - h * x₁)
    let x₃ := x₂ * (fromFloat 2.0 - h * x₂)
    x₃

-- Division
def div (x y : Hyper) : Hyper :=
  mul x (inv y)

instance : Div Hyper where
  div := div

-- Integer power
partial def ipow (x : Hyper) (n : Int) : Hyper :=
  if n < 0 then inv (ipow x (-n))
  else if n == 0 then one
  else if n == 1 then x
  else if n % 2 == 0 then
    let half := ipow x (n / 2)
    mul half half
  else
    mul x (ipow x (n - 1))

-- Power function
instance : HPow Hyper Int Hyper where
  hPow := ipow

instance : HPow Hyper Nat Hyper where
  hPow x n := ipow x (Int.ofNat n)

-- Equality
instance : BEq Hyper where
  beq x y := simplify x == simplify y

def Hyper.eq (x y : Hyper) : Bool :=
  simplify x == simplify y

-- Exponential function: exp(x) = Σ xⁿ/n!
partial def exp (h : Hyper) : Hyper :=
  let rec expHelper (n : Nat) (sum : Hyper) (term : Hyper) : Hyper :=
    if n >= TAYLOR_TERMS then sum
    else
      let newTerm := (term * h) / fromNat (n + 1)
      expHelper (n + 1) (sum + newTerm) newTerm
  expHelper 0 one one

-- Logarithm with argument reduction
-- Based on Julia implementation lines 262-312
partial def log (u : Hyper) : Hyper :=
  let LOG2 := fromFloat 0.693147  -- ln(2)
  let stv := real u
  if stv <= 0.0 then zero  -- hack for now
  else
    -- Argument reduction: scale to [0.666, 1.5]
    let rec reduce (v : Hyper) (n : Int) : Hyper × Int :=
      if real v > 1.5 then reduce (v / fromFloat 2.0) (n + 1)
      else if real v < 0.666 then reduce (v * fromFloat 2.0) (n - 1)
      else (v, n)
    let (v, n) := reduce u 0
    -- Taylor series for log(1+z) where z = v - 1
    let z := v - one
    let rec logHelper (k : Nat) (s : Hyper) (t : Hyper) (sign : Float) : Hyper :=
      if k >= TERM_PRECISION then s
      else
        let term := (fromFloat sign * t) / fromNat (k + 1)
        logHelper (k + 1) (s + term) (t * z) (-sign)
    let s := logHelper 0 zero z 1.0
    let nFloat : Float := if n >= 0 then n.natAbs.toFloat else -(n.natAbs.toFloat)
    (fromFloat nFloat * LOG2) + s

-- Helper: factorial function
partial def factorial (n : Nat) : Nat :=
  if n == 0 then 1
  else n * factorial (n - 1)

-- Sine using Taylor series: sin(x) = Σ(-1)ⁿ x^(2n+1)/(2n+1)!
partial def sinHelper (x : Hyper) (n : Nat) (sum : Hyper) : Hyper :=
  if n >= 10 then sum
  else
    let sign := if n % 2 == 0 then 1.0 else -1.0
    let power := ipow x (2 * n + 1)
    let fact := factorial (2 * n + 1)
    let term := (fromFloat sign * power) / fromNat fact
    sinHelper x (n + 1) (sum + term)

partial def sin (x : Hyper) : Hyper :=
  sinHelper x 0 zero

-- Cosine using Taylor series: cos(x) = Σ(-1)ⁿ x^(2n)/(2n)!
partial def cosHelper (x : Hyper) (n : Nat) (sum : Hyper) : Hyper :=
  if n >= 10 then sum
  else
    let sign := if n % 2 == 0 then 1.0 else -1.0
    let power := ipow x (2 * n)
    let fact := factorial (2 * n)
    let term := (fromFloat sign * power) / fromNat fact
    cosHelper x (n + 1) (sum + term)

partial def cos (x : Hyper) : Hyper :=
  cosHelper x 0 zero

-- Square root: x^0.5 = exp(0.5 * log(x))
partial def sqrt (x : Hyper) : Hyper :=
  exp ((fromFloat 0.5) * log x)

-- Derivative: ∂f/∂x ≈ (f(x+ε) - f(x-ε)) / (2ε)
def derivative (f : Hyper → Hyper) (x : Hyper) : Hyper :=
  (f (x + ε) - f (x - ε)) / (fromFloat 2.0 * ε)

notation "∂" => derivative

-- Helper: lower order by removing e=0 terms
def lower (h : Hyper) : Hyper :=
  ⟨h.terms.filter (fun (_, e) => e > 0.0) |>.map (fun (r, e) => (r, e - 1.0))⟩

-- Integration using Riemann sum
-- Based on Julia implementation lines 860-874
partial def integrate (f : Hyper → Hyper) (x : Hyper) : Hyper :=
  if real x == 0.0 then zero
  else
    let rec intHelper (i : Nat) (sum : Hyper) (dx : Hyper) : Hyper :=
      if i >= INTEGRATION_TERMS then sum
      else
        let val := f (fromNat i * dx)
        let newSum := if isInfinite val then
          sum + (if real x > 0.0 then lower val else neg (lower val))
        else
          sum + val * dx
        intHelper (i + 1) newSum dx
    let dx := x / fromNat INTEGRATION_TERMS
    intHelper 0 zero dx

notation "∫" => integrate

-- Tests
#eval zero
#eval one
#eval ε
#eval ω
#eval ε * ω
#eval one + one
#eval one + ε

end HyperReals
