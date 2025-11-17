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
  deriving Repr

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

-- Exponential function: exp(x) = Σ xⁿ/n!
partial def exp (h : Hyper) : Hyper :=
  let rec expHelper (n : Nat) (sum : Hyper) (term : Hyper) : Hyper :=
    if n >= TAYLOR_TERMS then sum
    else
      let newTerm := (term * h) / fromNat (n + 1)
      expHelper (n + 1) (sum + newTerm) newTerm
  expHelper 0 one one

-- Logarithm with argument reduction
def log (u : Hyper) : Hyper :=
  sorry  -- Will implement after exp works

-- Sine using Taylor series
partial def sin (x : Hyper) : Hyper :=
  let rec sinHelper (n : Nat) (sum : Hyper) : Hyper :=
    if n >= 10 then sum
    else
      let sign := if n % 2 == 0 then 1.0 else -1.0
      let power := ipow x (2 * n + 1)
      let factorial := (List.range (2 * n + 2)).foldl (· * ·) 1
      let term := (fromFloat sign * power) / fromNat factorial
      sinHelper (n + 1) (sum + term)
  sinHelper 0 zero

-- Cosine using Taylor series
partial def cos (x : Hyper) : Hyper :=
  let rec cosHelper (n : Nat) (sum : Hyper) : Hyper :=
    if n >= 10 then sum
    else
      let sign := if n % 2 == 0 then 1.0 else -1.0
      let power := ipow x (2 * n)
      let factorial := (List.range (2 * n + 1)).foldl (· * ·) 1
      let term := (fromFloat sign * power) / fromNat factorial
      cosHelper (n + 1) (sum + term)
  cosHelper 0 zero

-- Square root
def sqrt (x : Hyper) : Hyper :=
  sorry  -- x^0.5, will need exp/log

-- Derivative: ∂f/∂x ≈ (f(x+ε) - f(x-ε)) / (2ε)
def derivative (f : Hyper → Hyper) (x : Hyper) : Hyper :=
  (f (x + ε) - f (x - ε)) / (fromFloat 2.0 * ε)

notation "∂" => derivative

-- Integration (simplified version)
def integrate (f : Hyper → Hyper) (x : Hyper) : Hyper :=
  sorry  -- Will implement

notation "∫" => integrate

-- Helper functions
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

-- Tests
#eval zero
#eval one
#eval ε
#eval ω
#eval ε * ω
#eval one + one
#eval one + ε

end HyperReals
