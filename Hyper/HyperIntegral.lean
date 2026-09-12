/-
  The hyperreal integral: `∫ f dx` with `dx = ε`, computed exactly.
  =================================================================

  `notes/integral/integral-probability-foundations.md` is the prose version.
  The integral is the hyperfinite Riemann sum over the dots of an interval,

      ∫_[a,b) f(x) dx  :=  ∑_{k < (b-a)·ω} f(a + (k+s)·ε) · ε

  with `s` the sample offset inside each dot: `0` left, `1/2` midpoint (the
  symmetric convention, canonical here), `1` right.  No standard part is taken;
  the value is an exact `R*` number, ε-corrections included.

  Nothing is summed term by term — there is no index type of size `ω`.  The sum
  is evaluated in closed form through the power-sum recursion

      (p+1)·S_p(M) = M^(p+1) - ∑_{j<p} C(p+1,j)·S_j(M),     S_p(M) = ∑_{k<M} k^p,

  which is exact for a hyperreal bound `M = (b-a)·ω`, so the whole integral is
  ordinary `R*` arithmetic.

  The default domain is the reals, taken as the ambient line `[-ω, ω)`, where
  `∫1 dx = 2ω`.  The probability layer restricts to a region whose total mass is
  exactly `1`; see `IsDensity`.
-/
import Hyper.HyperList

namespace Hypers
namespace HyperLists
namespace Integral

-- ═══════════════════════════════════════════════════════════════════════════
-- Conventions, all in one place
-- ═══════════════════════════════════════════════════════════════════════════

/-- Where inside its dot `[x, x+ε)` a function is sampled. -/
abbrev Sample := ℚ

def leftRule : Sample := 0
/-- Canonical: pairs with the symmetric difference quotient and the
    symmetric Dirac `δ = ω₀/2`. -/
def midRule : Sample := 1 / 2
def rightRule : Sample := 1

/-- The reals as an integration domain: the ambient line `[-ω, ω)`, on which
    `∫ 1 dx = 2ω`. -/
def lineLow : R* := -omega
def lineHigh : R* := omega

-- ═══════════════════════════════════════════════════════════════════════════
-- Exact hyperfinite power sums
-- ═══════════════════════════════════════════════════════════════════════════

/-- `x ^ n` by repeated multiplication, independent of the `Field R*`
    instance's `^` (whose `mul_inv_cancel` is still open). -/
def hpow (x : R*) : ℕ → R*
  | 0 => 1
  | (n + 1) => x * hpow x n

/-- Multiplication by a rational scalar. -/
def scale (q : ℚ) (x : R*) : R* := embedQ (q : 𝔽) * x

/-- `powerSumsUpTo M n = [S_0(M), …, S_(n-1)(M)]` where `S_p(M) = ∑_{k<M} k^p`,
    each an exact `R*` value for a hyperreal bound `M`. -/
def powerSumsUpTo (M : R*) : ℕ → List R*
  | 0 => []
  | (n + 1) =>
    let previous := powerSumsUpTo M n
    -- computing S_n from S_0 … S_(n-1)
    let corrections : R* :=
      (List.range n).foldl
        (fun acc j => acc + scale ((Nat.choose (n + 1) j : ℚ)) (previous.getD j 0)) 0
    previous ++ [scale (1 / (n + 1 : ℚ)) (hpow M (n + 1) - corrections)]

/-- `powerSum p M = ∑_{k<M} k^p`, exact. -/
def powerSum (p : ℕ) (M : R*) : R* := (powerSumsUpTo M (p + 1)).getD p 0

/-- `∑_{k<M} (k+s)^p`, the sum actually needed for a sample offset `s`. -/
def shiftedPowerSum (s : Sample) (p : ℕ) (M : R*) : R* :=
  let sums := powerSumsUpTo M (p + 1)
  (List.range (p + 1)).foldl
    (fun acc i =>
      acc + scale ((Nat.choose p i : ℚ) * s ^ (p - i)) (sums.getD i 0)) 0

-- ═══════════════════════════════════════════════════════════════════════════
-- The integral of a polynomial part
-- ═══════════════════════════════════════════════════════════════════════════

/-- Number of dots in `[a, b)`. -/
def dotCount (a b : R*) : R* := (b - a) * omega

/-- `∫_[a,b) x^n dx`, exact, with sample offset `s`.

    Expanding `(a + (k+s)ε)^n` binomially turns the hyperfinite sum into
    `∑_j C(n,j)·a^(n-j)·ε^(j+1)·∑_{k<M}(k+s)^j`. -/
def integralMonomial (s : Sample) (n : ℕ) (a b : R*) : R* :=
  let M := dotCount a b
  (List.range (n + 1)).foldl
    (fun acc j =>
      acc + scale (Nat.choose n j : ℚ)
        (hpow a (n - j) * hpow epsilon (j + 1) * shiftedPowerSum s j M)) 0

/-- A density's ordinary part: `∑ i, coefficients[i] · x^i`, coefficients in
    `R*` so that infinitesimal densities such as `ε/2` on the whole line are
    expressible. -/
def polyValue (coefficients : List R*) (x : R*) : R* :=
  (coefficients.zipIdx).foldl (fun acc (c, i) => acc + c * hpow x i) 0

def integralPoly (s : Sample) (coefficients : List R*) (a b : R*) : R* :=
  (coefficients.zipIdx).foldl
    (fun acc (c, i) => acc + c * integralMonomial s i a b) 0

-- ═══════════════════════════════════════════════════════════════════════════
-- Spikes: an atom is a density value, not a second mechanism
-- ═══════════════════════════════════════════════════════════════════════════

/-- A concentrated mass: the density value `mass·ω` on the cell of `position`.

    **The probability atom and the Dirac delta are this same object.**  `ω` is
    what unifies them: an atom of mass `a` and the spike `a·δ` are both "`ω`
    scaled to carry mass `a` on a point's cell", and `P({y}) = p(y)·ε` returns
    that mass.  There is no second mechanism and no second kind of spike.

    `stencil := true` is *not* a different delta.  It is what the **central
    difference quotient** `∂f = (f(x+ε) - f(x-ε))/(2ε)` returns when applied to
    a step: `ω/2` on *each* of the two cells of the halo, because the stencil is
    `2ε` wide while the jump is a point.  It is `δ` convolved with that stencil
    — same mass, same integral over every halo-aligned region, support `2ε`
    instead of `ε`.  The `/2` belongs to the stencil's width, not to `δ`.

    Consequently `∫(−ε,ε) ω = 2` and `∫(0,ε) ω = 1` are simply the constant `ω`
    on two cells and on one; and `δ := ω₀/2` is right exactly when `ω₀` means
    "`ω` on the two-cell halo", which is the form the symmetric derivative
    produces. -/
structure Spike where
  position : R*
  mass : R*
  /-- Carried by the two-cell halo rather than the single cell: the shape the
      central difference quotient produces. -/
  stencil : Bool := false

/-- The cells of `[a,b)` that a spike's support meets. -/
def spikeMass (spike : Spike) (a b : R*) : R* :=
  let cellIn (c : R*) := decide (a ≤ c ∧ c + epsilon ≤ b)
  if spike.stencil then
    match cellIn (spike.position - epsilon), cellIn spike.position with
    | true, true => spike.mass
    | true, false | false, true => scale (1 / 2) spike.mass
    | false, false => 0
  else if cellIn spike.position then spike.mass else 0

/-- The value a spike contributes to the density at `x`. -/
def spikeValue (spike : Spike) (x : R*) : R* :=
  let onCell (c : R*) := decide (c ≤ x ∧ x < c + epsilon)
  if spike.stencil then
    if onCell (spike.position - epsilon) ∨ onCell spike.position
    then scale (1 / 2) (spike.mass * omega) else 0
  else if onCell spike.position then spike.mass * omega else 0

/-- An elementary function: an ordinary polynomial part plus finitely many
    `ω`-spikes.  Every density in the exercise curriculum is of this shape. -/
structure Elementary where
  poly : List R* := []
  spikes : List Spike := []

def Elementary.value (f : Elementary) (x : R*) : R* :=
  polyValue f.poly x + f.spikes.foldl (fun acc spike => acc + spikeValue spike x) 0

/-- `∫_[a,b) f(x) dx` with sample offset `s`. -/
def integralWith (s : Sample) (f : Elementary) (a b : R*) : R* :=
  integralPoly s f.poly a b + f.spikes.foldl (fun acc spike => acc + spikeMass spike a b) 0

/-- The canonical integral: symmetric (midpoint) sampling. -/
def integral (f : Elementary) (a b : R*) : R* := integralWith midRule f a b

/-- Default domain: the reals. -/
def integralLine (f : Elementary) : R* := integral f lineLow lineHigh

notation "∫[" a ", " b "] " f => integral f a b
notation "∫ℝ " f => integralLine f

/-- An atom of mass `m` at `position`: `m·ω` on the point's cell, so that
    `P({position}) = m` exactly. -/
def atom (position m : R*) : Elementary :=
  { spikes := [{ position := position, mass := m }] }

/-- The unit Dirac delta.  Definitionally the unit atom — one object. -/
def dirac (position : R*) : Elementary := atom position 1

/-- What the central difference quotient of a unit step actually returns:
    `ω/2` on each halo cell.  Equal to `dirac` in mass and in every
    halo-aligned integral, but smeared over the `2ε` stencil. -/
def stepDerivative (position : R*) : Elementary :=
  { spikes := [{ position := position, mass := 1, stencil := true }] }

/-- The constant density `c`. -/
def constant (c : R*) : Elementary := { poly := [c] }

-- ═══════════════════════════════════════════════════════════════════════════
-- Probability: a density is an elementary function of total mass one
-- ═══════════════════════════════════════════════════════════════════════════

/-- A distribution: an elementary density together with the region it lives on.
    `IsDensity` is the requirement that the region carry total mass exactly `1`;
    on the reals take `low = -ω`, `high = ω`. -/
structure Distribution where
  density : Elementary
  low : R* := lineLow
  high : R* := lineHigh

def Distribution.total (d : Distribution) : R* := integral d.density d.low d.high

def Distribution.IsDensity (d : Distribution) : Prop := normalize d.total = normalize 1

instance (d : Distribution) : Decidable d.IsDensity := by
  unfold Distribution.IsDensity; infer_instance

/-- `P(E)` for `E = [a,b)`. -/
def Distribution.prob (d : Distribution) (a b : R*) : R* := integral d.density a b

/-- `P({y}) = p(y)·ε`, the identity the whole framework turns on. -/
def Distribution.probPoint (d : Distribution) (y : R*) : R* := d.density.value y * epsilon

/-- Uniform on `[0,1)`: `p ≡ 1`, so `P({y}) = ε`. -/
def uniformUnit : Distribution := { density := constant 1, low := 0, high := 1 }

/-- Uniform on the whole line: normalization forces the infinitesimal density
    `ε/2`, so a point is second-order rare, `P({y}) = ε²/2`. -/
def uniformLine : Distribution := { density := constant (scale (1 / 2) epsilon) }

/-- Uniform on `[0,L)`. -/
def uniformOn (a b : R*) : Distribution :=
  -- the inverse is exact while `b - a` is a single monomial
  { density := { poly := [(b - a)⁻¹] }, low := a, high := b }

end Integral
end HyperLists
end Hypers
