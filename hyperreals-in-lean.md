# hyper-lean ε*ω = 1

Hyperreal numbers implementated algebraically in the Lean 4 mathematical proof language.

[Hyperreal numbers Wiki](https://en.wikipedia.org/wiki/Hyperreal_number)

Lean comes with import Mathlib.Data.Real.Hyperreal -- defined as hyperfilter germ
**but we want Hyperreal numbers axiomatically with the added property ε*ω = 1 **
Also we want it calculable with a simple structure

In mathematics, the system of hyperreal numbers is a way of treating infinite and infinitesimal (infinitely small but non-zero) quantities. The hyperreals, or nonstandard reals, *R, are an extension of the real numbers R with algebraic spanning elements ω ≈ ∞ and ε ≈ 1/∞.

The canonical infinitesimal ε has the property of being bigger than 0 and smaller than all positive standard numbers:
0 < ε < r ∀r∊ℝ⁺

The canonical infinite ω has the property of being bigger than all standard numbers:
r < ω   ∀r∊ℝ

# Hyperreal numbers ε*ω = 1

These two symbols can be linked via canonical gauging:

ω := 1/ε

1/∞ = 0 # ∞ is not part our field, just for illustration
1/0 = ∞  # not ω!
ω/∞ = ?

⚠️ r*ω ≠ ω for 1≠r in ℝ ;unlike classical infinity notation where ∞=r·∞ ∀r>0 in ℝ
In fact ∞ is not a number but may be the equivalence class ∞=〚ωᵚ〛

Any infinitesimal a*ε has the property of being bigger than 0 and smaller than all positive standard numbers:
0 < a*ε < r ∀r∊ℝ⁺ a∊ℝ⁺


We are mostly interested in applicative usage of Hyperreal numbers, defined axiomatically similar to the simple field extension of ℂ=ℝ(ⅈ)=ℝ+ⅈℝ or Dedekind–Peano axioms for Natural numbers.

ℝ⋆ = ℝ(ε, ω)  # ordered field extension
ℝ⋆ ≈ "algebraic-span / algebraic-closure(ℝ,ε)" # ω not needed because ω=1/ε
ℝ⋆ ≅ vectorial-span(1,ε,ω,ε²,ω²,…)   # 1/ε not needed because ω=1/ε

𝕀   infinitesimal small nonstandard numbers 《ε》 span including ε*ε … order -∞ or 1/∞
𝕀⁻¹ infinitesimal small nonstandard numbers ℝ·ε  = {a*ε a∊ℝ} outer span order -1
𝕀⁻² infinitesimal small nonstandard numbers ℝ·ε² = {a*ε²a∊ℝ} outer span order -2
𝕃 limited standard ℝ and nonstandard ℝ+𝕀 numbers <ℝ,ε>
𝕐  unlimited infinite nonstandard numbers 《ω》 order ∞
𝕐¹ unlimited infinite nonstandard numbers ℝ·ω  = {a*ω  a∊ℝ} order 1
𝕐² unlimited infinite nonstandard numbers ℝ·ω² = {a*ω² a∊ℝ} order 2

ℝ⋆ ≅ ℝ×𝕀×𝕐

Pure reals in ℝ⋆ are sometimes called 'appreciable' but should just be called 'real'.

# Todo standardize notation
for easier typing these classes can be written as <I> <<I>> <Y> <<Y>> …
	Elements of 𝕀=<ε> are often denoted as δ
	Elements of 𝕐=<ω> re often denoted as H, K

# Orders

## ωⁿ

ωⁿ > r*ω for r in ℝ, n>1
εⁿ < r*ε for r in ℝ⁺ n>1

Unlike the constructive definition of ⋆ℝ (as sequence classes) we would like to differentiate between different orders:
ℝ order 0

𝕁 = <ω>ℝ = {a*ω a∊ℝ} order 1 infinites
𝕀 = <ε>ℝ = {a*ε a∊ℝ} order -1 infinitesimals

Generalisations or alternative constructions of Hyperreal numbers can be found in
https://en.wikipedia.org/wiki/Hyperreal_number
https://en.wikipedia.org/wiki/Superreal_number
https://en.wikipedia.org/wiki/Surreal_number

In fact if we were forced to 'anchor' our axioms with concrete constructions, we would pick the elegant approach of surreal numbers and skip other crutch conceptions.


# approximates
We have a canonical similarity operator ≈ as:
x≈ε <=> x=a·ε for some a in ℝ⁺
x≈0 <=> x=0 or x≈±ε
x≈y <=> x-y≈0

⚠️ one MAY define '~' so that x~ε => x~0 !
⚠️ some authors define ~ very differently as x~y <> x-y limited "of the same order"

# dot ≈ halo ≈ monad
The dot / halo around a point x is the set of all nonstandard numbers near x
halo(x) =〚x≈y for y in ℝ⋆〛
Equivalently it's the span of all infinitesimals around x
halo(x) = x+𝕀 = {x+a*ε for a in ℝ}
halo(x) = x+𝕀 = {x + e for e in 𝕀}



# real part
Similar to complex numbers we are often just interested in the real part of hyperreal numbers.
Slightly different is the https://en.wikipedia.org/wiki/Standard_part_function :

Standard part 	as St(x) or x̌ (CARON	̌) for finite x
Real part 			as Re(x) or Real(x) or x.real or x̌
Complex part 		as C(x)  or Complex(x) or ℂ(x) or x.complex or x̌ for later ℂ extension
Hyperreal part 	as Hy(x) or Hyper(x) or x.hyper or x̂ ( ε and ω components of field extension )
Infinite part 	as Inf(x) or Omega(x) or x.omega ω(x)
Infinitesimal   as Eps(x) or x.epsilon or ε(x) not to confused with ε·x

For finite hyperreals we can define the "standard part" function which is identical to the real part:
x=a+∑bᶥεᶥ a,b in ℝ => st(x)=a

The set of all hyperreal numbers with standard part x, "close to x" is called monad, or halo of x.

Instead of leaving st(ω) undefined, we set
st(ω) = ∞  thus
st(x) = ∞  if Omega(x)>0
st(x) = -∞ if Omega(x)<0

Here real(x) ≠ st(x) !

x = x̌ + x̂
x = x̌ + ω(x) + ε(x)

In some implementations one may set ε(x)=0 if ω(x)≠0 that is infinite parts make infinitesimal parts insignificant
But in some scenarios it may be beneficial to keep track of ε parts even if the expression "blows up".

x∊ℝ⋆ is called real if Real(x)=x <=> Omega(x)=0 and Epsilon(x)=0
x∊ℝ⋆ is called finite if Omega(x)=0
x∊ℝ⋆ is called infinitesimal if Omega(x)=0 and Real(x)=0 ('truely' if Epsilon(x)≠0)
x∊ℝ⋆ is called hyperinteger if Real(x)∊ℤ ('truely' if Real(x)≠x otherwise just integer within ℝ⋆)

# properties of real / st function
The real/standard function is order-preserving though not isotonic; i.e.
x ⫹ y
x ≦ y
x ≤ y => st(x) ≤ st(y) but
x < y ≠> st(x) < st(y)
st(x+y)=st(x)+st(y) if x,y finite
st(x*y)=st(x)*st(y)
st(1/x)=1/st(x) if x finite and not infinitesimal

St is continuous and even locally constant.

x ⪂ y := x-y=a·ε for some a in ℝ⁺ "x is infinitesimally bigger than y"
x ⪄ y same?
x ⪘ y same?  ⥱ ⥵
x ⪞ y see ⩺ or ⥸



Any real number x which satisfies |x| < k for some standard k is called limited |x| << ∞ and
any real number which is not limited is called unlimited.
Any real number x which satisfies |x| < 1/k for all standard k ≠ 0 is called infinitesimal (denoted x ≂ 0)
In particular, for every nonstandard n, the reciprocal n1 is a strictly positive infinitesimal. Given x; y 2 R, we write:
• x ≂ y <=> x - y is infinitesimal or 0
• x ≈ y <=> x - y is infinitesimal (but not 0?)
• x ~ y proportionality x ∝ y !
•	x ≄ y
•	x ≂̸ y
•	x ≇ y
•	x « y "usually much bigger, here: more than infinitesimally bigger"
• x << y <=> x < y and x ≄ y
• x ⪝ y <=> x < y or x ~ y
	⩯ ⩮ ⩦ ⥱ ⥵ ⩰ ⩱ ⩲ ⩳


# gauging
ε * ω = 1
|ℕ|=ω=ℕ̅
|ℤ|=2ω ⚠️  needs different metric than cardinality where  ‖ℕ‖ = ‖ℤ‖ = ‖ℚ‖

## gauging with other axioms

# integral ε = 1 or 2:
∫ε = 2/1 # that is:
∫(0,ω)(ε)  = 1   # ω*ε = 1
∫(-ω,ω)(ε) = 2/1 # infinite line AND/OR
∫(-∞,∞)(ε) = ƒ   # -''-  can't be because 2ω=ω+ω and linear ∫
∫(-ε,ε)(ω) = 2/1 # spike
∫(0,ε)(ω) =    1 # => dirac delta δ
∫1 = ω over ℝ for interval (-∞,∞)
∫1 = √ω for interval [0,1] ?

Similar to π vs τ we have ∫1 = 2ω over (-∞,∞) vs (0,∞) => ω
Similar to π vs τ we have ∫ε = 2  over (-∞,∞) vs (0,∞) => 1

⚠️ εᵚ for each σ-algebra Ω such that ∫εᵚ=1 over uncountable Ω and ∑εᵚ=1 for countables
⚠️ If the context is clear we emit εᵚ and just write ε



∫[a,b]f(x):=st(∑(f,a,b,Δx))
Integral as standard part of an infinite Riemann sum S(f,a,b,Δx)


⚠️ infinite sums of in the hyperreals don't really play the way one might expect:
⚠️ The hyperreal universe has its own kinds of sequences and series, which are no longer indexed by ℕ but rather by ∗ℕ, the nonstandard natural numbers.

point vs
dot:=circle with radius ε or circle with radius √(ε/2π) so that
Area(dot)=ε
Volume(3dot)=ε
Width/Height(line)=ε
Width/Height(sheet)=ε
Width/Height(plane)=ε

Length(line)=2ω or ∞ ?

# theoretical questions:
Is it possible to gauge / define the following:
ε*∞ = ∞ ?
∞/ω = ∞ ?
⚠️ how are countable and continuous cardinals relateable to hyperreal ordinals?
Cardinals ‖ℕ‖ = ‖ℚ‖ means they are in the same class, but for hyperreals can we distinguish:
|ℤ|=ω
|ℕ|=ω/2 =: ℕ̅
|ℚ|=ω² ?
|ℝ|=Ω=ω₂=ω̄=ω̅ = ωᵚ ?

⚠️ could a simplified theory reconsile some of the following: ?
∑ℕ(ε̄) = 1 vs ∫ℝ(ε) = 2/1 clearly needs two different ε vs ε̄?
∫ℝ(ε)=∑ℕ(ε̄)=1 via ∫[a,b]f(x):=st(Riemann ∑(f,a,b,Δx)) ?
∑ℤ(ε) = 1-ε <>
∑ℕ(ε) = 1/2 (-½ε) <>
∑1/n = ω = ζ̂(0) = ζ(1)
∑1 = ∑𝑖∈ℕ(1) = ω - ½  = ζ̂(-1) = "∑1" = "∑ℕ"   # see Riemann zeta
∑n = ∑𝑖∈ℕ(𝑖) ∝ ωˣ - 1/12     exponent ˣ?
∑n = ∑𝑖∈ℕ(𝑖) = ζ̂(-2)   ( ζ(-1) = -1/12 = "∑n" )
∑ ℚ(√ε)=1
∑ 𝑖∈ℚ(1) = ω²
∑ 𝑖∈ℚ(𝑖) ∝ ωʸ
∏ 𝑖∈ℕ>1 i = ωˣ
∏ 𝑖∊ℚ>1 i ∝ ωʸ
∏ i∊ℚ(0,1) i ≂ ε
∏ 𝑖∈ℝ>1 i ∝ ωˣ ?

Definition without variable 𝑖
∑ℕ₊=ω/2
∑ℚ ∝ ωˣ
∑ℝ=ƒ  ↯ can't take countable sum of uncountable set
∏ ℝ>1 ∝ ωˣ   ↯ can't take countable product of uncountable set
∏(0,1) ≂ εˣ

#𝕀 infinitesimal numbers
𝕀 = span field <ε, ω>
ℝ∗
ℝ⋆ = ℝ(ε, ω)  # ordered field extension
ℝ⋆ = ℝ(ε)     # because ω := 1/ε
ℝ⋆ = ℝ×𝕀
ℝ∗ = ℝ⋆

Unit Omega   # treat it externally! give automatic arithmetics see Unitful in Julia
Unit Epsilon # treat it externally too?
# 1 km + 1 s DimensionError ill defined but 1 + ε exactly what we want

class HyperReal is Number {
	# class ℝ⋆
	alias Hyper

	# hyperreals ℝ⋆ are an ordered field extension of ℝ

#Number omega alias om # omega ≠ 0 makes the following irrelevant:
	# treat it externally!
	Number real alias real part, re, standard part, st, shadow, sh
Number epsilon alias ep, eps

# transfer principle:
# first-order statements about ℝ are also valid in ℝ⋆

	𝑎*𝑏 :=
	times(number) = Hyper(this.real*number,this.epsilon, this.omega)
	plus(number)  = Hyper(this.real+number,this.epsilon, this.omega) # …

  a==b := a.omega==b.omega and a.real==b.real and a.epsilon==b.epsilon

	𝑎≃𝑏 :=
	    a.omega==b.omega==0 and a.real==b.real==0 and a.epsilon == b.epsilon or
	    a.omega==b.omega==0 and a.real==b.real or
	    a.omega==b.omega

	𝑎>𝑏 :=
	    a.omega==b.omega==0 and a.real==b.real==0 and a.epsilon > b.epsilon or
	    a.omega==b.omega==0 and a.real>b.real or
	    a.omega>b.omega

	𝑎<𝑏 :=
	    a.omega==b.omega==0 and a.real==b.real==0 and a.epsilon > b.epsilon or
	    a.omega==b.omega==0 and a.real>b.real or
	    a.omega>b.omega

	  }



# external definition as in Julia
times(ω,ε) = 1
times(ε,ω) = 1
simplify(hyper y) =
		Hyper(0, 0, y.omega) if y.omega
		Hyper(y.real, 0, 0)  eif y.real
		Hyper(0,y.epsilon,0) oif #otherwise


standard(hyper y) =
	if y.omega > 0 : +∞
	elif y.omega < 0 : -∞
	else : y.real  # ignore epsilon
	# todo: add ε ω as two special values / flags in wasp number representation f64 see Inf, NaN …

times(number x,hyper y) = Hyper(x*y.real,x*y.epsilon, x*y.omega)
times(hyper x,hyper y) = Hyper(x.real*y.real,x.real*y.epsilon+y.real*x.epsilon, hyper.omega)
times(hyper x,ε) = Hyper(0, x.real, 0)
times(hyper x,ε) = Hyper(0, x.real, 0)

epsilon := Hyper(0,1,0)
omega   := Hyper(0,0,1)

⚠️ free standing ε vs x.ε



# Applications

## Derivatives
"define the derivative algebraically"
operator ∂
∂f(x)=(f(x+ε)-f(x))/ε
// e.g
// f(x)=x^2
// ∂f(x)=((x+ε)^2)-x^2)/ε = (2xε + ε^2)/ε = 2x + ε

real derivative (f) = st(∂f)


### derivatives of spike/step function
∂(x==0)(0) = ω # derivative of spike function  # ∂(x==0)(y) = 0 for y≠0
∂(x>0)(ε)  = ω # derivative of step function   # ∂(x>0 )(y) = 0 for y≠ε

∂(x==0) = ω at 0
∂(x==0 and ω)(0) = ω² # second order spike


## Probabilities
1. "zero probability"
"Traditional probability theory introduced zero-sets to handle cases such as:"
"Probability of hitting an exact number in the Uniform Distribution over an interval e.g. [0,1]"
P(x=y)=ε for y in [0,1] # classically "'0' but not impossible"

⚠️ different zero-sets can result in different (multiplier / exponent ) variants of ε
⚠️ εᵚ for each σ-algebra Ω such that ∫εᵚ=1 over uncountable and ∑εᵚ=1 for countable Ω
⚠️ If the context is clear we emit εᵚ and just write ε

2. No pointweight
As an ad-hoc mechanism to deal with steps in probability distributions, classical theory introduced point weights.
These are no longer neccessary when any density function can be directly expressed as
F=∫p   ( meaning F(x)=P([-∞,x])=∫(-∞,x)p(y)dy just as in case of steady functions before )


π(x)=a <> p(x)=a·ω => F(x)= a + P([-∞,x[)

# algebraic δ
The δ dirac delta "function/distribution"
Since δ behaves similarly as a "spike":
∫(-ε,ε)(δ) = 1
∫(-ε,ε)(ω) = 2
We can take δ:=ω₀/2 as an algebraic definition of the dirac delta.

where ω₀(x):= ω iff x≈0  # in the halo of 0!

This new definition can be proven to be equivalent to another algebraic definition of the
Dirac Delta as Derivative of Heaviside Step Function
H(x) := x >= 0      # True ≈ 1
δ(x) := dH(x)/dx

# As an extension we may call
∫(-ε,0)(ω) = 1  "left-dirac"
∫( 0,ε)(ω) = 1  "right-dirac"

# [[step-numbers]]
δ dirac delta "function/distribution"

practical aspects see ~/wasp/lib/hyperreals.wasp

### Defining Uniform Distribution over [-∞,∞] aka ℝ now possible?
"TODO: Probability of hitting an exact number in the interval [-∞,∞] aka ℝ with Uniform Distribution"
P(x in [0,1])=ε or
P(x=y)=ε or
P(x=y)=εᵚ



# Limes
"replace limes with algebraic expressions!"
e = lim(n=>∞) (1+1/n)^n
e = (1+1/ω)^ω = (1+ε)^ω
e^ω = [1,2,…,ω] least common multiplier e = lim(n->∞) [1,2,…,n]¹ʼⁿ

sign x = tanh ω·x !

H(x) = ½ + ½·tanh ω·x  Heaviside see [[step-numbers]] step function with H(0)=1/2
H(x) = ½ + ½·erf ω·x
H(x) = 1/(1+e^(-2ω·x))
H(x) = ½ + 1/π · arctanh ω·x
H(x) = 1/(2πi) ∫e^(i·x·t)/(t+i·ε) dt

# periods
## desired theorem:
ε == 1 - 0.9̂
⚠️ careful 1 == 0.9̅ still holds and is usually not of concern https://arxiv.org/abs/1007.3018
the above statement strongly depends on exact meaning / notation 0.9̅ vs 0.9̂ vs .999… vs .999…;…999
indeed we just need proper definitions for
0.9̅ = 0.9̂ + ε = 1
likewise
1/3 = 0.333… + ε ?
but
3*1/3 = 1 = 0.9̂ + 3ε ≠ 0.9̂ + ε
so
1/3 = 0.333… + ε/3 ?

0.9̅ can be thought of as closure or limit, thus 0.9̅=1 becomes plausible
0.9̂ can be thought of as open restraint,   thus 0.9̂<1 becomes plausible

∑𝑖∈ℕ 9/10^𝑖 does not have a supremum and thus does not make sense in nonstandard analysis.

# academic questions
 we are only interested in axiomatic algebraic applications

what if we consider for the algebraic dirac delta
ω₀(x):= ω iff x==0  # only directly at 0, instead of the halo x≈0 ?

# standard infinity
What would the role of the symbol ∞ be in our theory?

∫(-ω,ω)(ε) = 2   # 'infinite' line AND/OR
∫(-∞,∞)(ε) = ƒ   # -''-  can't be because 2ω=ω+ω and linear ∫

What would a name for ω be? Since it's not infinity, one has to stick with omega

Note how infinite is an attribute of ω but infinity is an absolute term not applying to ω. Unless we can talk about ω as (partial)"omega-infinity".

# First order analysis
To simplify some calculations, we may want to restrict ourselves to
simple elements of the closure ℝ ω ε, putting all ε² ω² … into an extra bucket called
inner and outer 'zone' (rest border of higher orders).

“partial quasifield” ≠ Teilkörper ≠ Schiefkörper (nicht kommutativ) ≠ Halbkörper

# Topology
• all halos are open
… todo


## Crazy closure:
Is it under some cirumstances possible to 'connect' ±∞ in such a way ω + ∞ = -∞ ?

# L'Hôpital rule
f(x+ε) ≈ g(x+ε) ≈ 0 or ±∞ and g'(x)≠0 =>
f/g=f'/g' at x

## example
(e^x-1)/(x^2+x)=e^x/(2x+1)=1 at 0

⍰ … is there any example that profits from our algebraic definition of the derivative?

## Measures
"more generally than the above Probability values, we can allow Measure Theory to make use of HyperReal numbers"
⚠️ todo

# Nonstandard Analysis for the Working Mathematician
by Peter A. Loeb & Manfred P. H. Wolff

ᵒf(x) := st(f(x)) based function
ᵒ∫f dm = ∫ᵒf dmL ? = ∫g lifted

Loeb Measure & Lebesque Measure

# Stochastic Calculus with Infinitesimals
by F. S. Herzberg
Radically Elementary Probability Theory
Merges standard and nonstandard natural numbers n∊ℕ !!
Uses P(A)≈0 instead of P(A)=ε
Too general, waste of precision

# An Introduction to Nonstandard Analysis
Lectures on the Hyperreals by Robert Goldblatt

# Construction of ⋆ℝ
Equivalent to the algebraic axiomatic definition of ⋆R above is the
Construction of ⋆ℝ as equivalent classes of sequences over ℝ (almost everywhere 'ultrafilter')
ℝ ⫉ ⋆ℝ via [r]:=(r,r,r,… ) trivial sequences

While this view and a generalisation to 'universes' provides powerful tools for advanced mathematicians, it is complete overkill for our cause.

# HUH ??
Remark 1.1 (Underspill and Overspill Principles). In minIST, one can prove (cf. Nelson [60, Theorem 5.4, p. 18]) that there are no sets which would consist of either
• all the standard natural numbers, or
• all the nonstandard natural numbers, or
• all the limited reals, or
• all the unlimited reals, or
• all the infinitesimal reals.
This allows, for example, for the following proof principles. Let A.x/ be an internal formula.
• Underspill in N. If A.n/ holds for all nonstandard n 2 N, then also for some standard n 2 N.
• Overspill in R. If A.x/ holds for all infinitesimal x 2 R, then also for some non-infinitesimal x  R.

A functional F on ƒ is called
• continuous if and only if forall ƒ whichsatisfy .t/' .t/forallt 2T,
F. / ' F. /
• limited if and only if F. / is limited for all   2 ƒ.
Two stochastic processes ;  W T ! R are called nearly equivalent if and only if E ŒF./ ' E ŒF./ for all limited
continuous functionals F on ƒ [ ƒ.

Let ε >> 0 in F. S. Herzberg page 13 seems like a nonsensical assumption!?


https://katalogplus.sub.uni-hamburg.de/vufind/Record/1657811964?rank=3
https://katalogplus.sub.uni-hamburg.de/vufind/Record/020746121?rank=20
https://katalogplus.sub.uni-hamburg.de/vufind/Record/1651089957?rank=19
https://katalogplus.sub.uni-hamburg.de/vufind/Record/1655395300?rank=16
https://katalogplus.sub.uni-hamburg.de/vufind/Record/1646345924?rank=10
https://katalogplus.sub.uni-hamburg.de/vufind/Record/271806729?rank=8
https://katalogplus.sub.uni-hamburg.de/vufind/Record/1645533808?rank=6
https://katalogplus.sub.uni-hamburg.de/vufind/Record/1025332490?rank=2

𝔸 𝔹 ℂ 𝔻 𝔼 𝔽 𝔾 ℍ 𝕀 𝕁 𝕂 𝕃 𝕄 ℕ 𝕆 ℙ ℚ ℝ 𝕊 𝕋 𝕌 𝕍 𝕎 𝕏 𝕐 ℤ

Trivial Arithmetic of Hyperreals
Let ε,δ be infinitesimal b, c appreciable and H, K unlimited. Then
• Sums:
ε + δ is infinitesimal
b + ε is appreciable
b + c is limited (possibly infinitesimal) H +ε  and H +bare unlimited
• Opposites:
-ε  is infinitesimal -b is appreciable -H is unlimited
• Products:
ε*δ and ε*b are infinitesimal b*c is appreciable b*H and H*K are unlimited


∫(0,ω)ε dx = 1/epsilon * epsilon - 0* epsilon = 1 # unabhängig von Eichung

# Riemann conjecture

[Riemann hypothesis](https://en.wikipedia.org/wiki/Riemann_hypothesis)
Riemann hypothesis is the conjecture that the Riemann zeta function has its zeros only at the negative even integers and
complex numbers with real part 1/2. Many consider it to be the most important unsolved problem in pure mathematics.

Riemann [zeta function](https://en.wikipedia.org/wiki/Riemann_zeta_function) analytical continuation

ζ(s):=∑1/nˢ s∊ℂ, real(s)>1
ζ(s):=∑1/nˢ = ∏1/(1-p⁻ˢ) p prime
ζ(s):= 1/Γ(s) ∫(0,∞) tˢ⁻¹/(eᵗ-1) dt = ℂ(ζ̂(s-1))
ζ̂(x):= ∫tˣ/(eᵗ-1) / ∫tˣ⋅eᵗ    t over ℝ⁺ # shifted by 1
ζ̂(x) = ∫tˣ/x!(eᵗ-1)
ζ̂(x) = ζ(x+1) = ∑n/nˣ⁺² = ∏p/(p-p⁻ˣ)   ratio of primes and their inverse difference

Instead of ζ̂ being just shifted, we need ζ̂ to be ω preserving, so that
∑1 = ∑𝑖∈ℕ(1) ∝ ω - ½    = ζ̂(-1)
∑n = ∑𝑖∈ℕ(𝑖) ∝ ωˣ - 1/12 = ζ̂(-2)

Then
ζ(s) = ℂ(ζ̂(s-1)) complex part of shifted ω-zeta
⚠️ Not the standard part, because st(ω) = ∞


shifted inverse zeta function
ζꜞ(y):= ∏(p-1/pʸ)/p
ζꜞ(y):= ∫tʸ⋅eᵗ / ∫tʸ/(eᵗ-1) dℝ⁺

sign flipped shifted inverse zeta function
ζ̄(y):= ∏(p-pʸ)/p

ζ(s)=e(∑P(ks)/k)   P prime zeta P(s):=∑1/pˢ

Γ(z):=∫(0,∞) tᶻ⁻¹⋅eᵗ dt # Γ(n)= (n-1)! = Γ̂(n-1)
Γ̂(x):=∫(0,∞) tˣ⋅eᵗ dt # Γ̂(n)=n!     # shifted by 1
Γ̂(x) = Γ(x+1) = x*Γ(x)
x! := Γ̂(x) generalized faculty over x∊ℂ
# trivial zeros

ζ(s) = 0 when s is one of −2, −4, −6, .... These are called its trivial zeros
ζ̂(x) = 0 when x is one of -3, -5, -7 …

# non-trivial zeros (conjecture)

ζ(s) = 0 => s = 1/2 + ⅈ·t
ζ̂(x) = 0 => x =-1/2 + ⅈ·t

# some values￼

ζ̂(7) = ζ(8) = ∑1/n⁸ = π⁸/9450
ζ̂(6) = ζ(7) = ∑1/n⁷ ≈ 1.008349277381923 = π⁷/x x=2995.28476444…
ζ̂(5) = ζ(6) = ∑1/n⁶ = π⁶/945
ζ̂(4) = ζ(5) = ∑1/n⁵ ≈ 1.03692775514337 = π⁵/x  x=295.121509929…
ζ̂(3) = ζ(4) = ∑1/n⁴ ≈ π⁴/90 = τ⁴/1440
ζ̂(2) = ζ(3) = ∑1/n³ ≈ 1.202056903159594 = π³/x  x=25.79435016661…
ζ̂(1) = ζ(2) = ∑1/n² = π²/6  = τ²/24
ζ̂(0) = ζ(1) = ∑1/n  = ω
ζ̂(-1)= ζ(0) = -1/2  = "∑1" (real part of some a₀⋅ω - 1/2 ?)
ζ̂(-2)= ζ(-1)= -1/12 = "∑n" (real part of some a₁⋅ω - 1/12 ?)
ζ̂(-3)= ζ(-2)= 0            (real part of some a₂⋅ω - 0 + b⋅ε ? )
ζ̂(-4)= ζ(-3)= 1/120 = -B₄/4
ζ̂(-5)= ζ(-4)= 0
ζ̂(-6)= ζ(-5)= 1/(42⋅6)  = -B₆/6

ζ̂(½) ≈ 2.612375348685488343348567567924


ζ̄(n)=ω  n∊2ℕ+1

# poles

ζ(1) = ∞
ζ̂(0) = ∞

ζ(1-x) = τ⁻ˣ 2cos(τx/4) Γ(x) ζ(x)

# Volume of ball

V(Bₙ)=√πⁿ/ζ̂(n/2)  n∊ℕ

# Supercomplex ≠ Hypercomplex

Supercomplex inspired by Superreal numbers over complex field ℂ
≠ Hypercomplex quaternions octonions
Same field extension as above, just over field ℂ(ε)
Despite of it's name, Supercomplex numbers make many calculations super easy.

Against the Riemann hypothesis:
• some Epstein zeta functions do not satisfy the Riemann hypothesis even though they have an infinite number of zeros on
the critical line.
• analytic number theory has had many conjectures supported by substantial numerical evidence that turned out to be
false. ( Skewes number first exception ≈ 10^316 !)
• behavior is often influenced by very slowly increasing functions such as log log T, that tend to infinity, but do so
so slowly that this cannot be detected by computation. Such functions occur in the theory of the zeta function
controlling the behavior of its zeros;

# Hyperreals as Laurent polynomial
https://en.wikipedia.org/wiki/Laurent_polynomial αᵢεᶻ / αᵢωᶻ z∈ℤ

# Hyperreals as group ring ℤ → 𝔽
"The Laurent polynomial ring can be endowed with a structure of a commutative, cocommutative Hopf algebra." Todo: Since we only have one 'variable' ε (or equivalently ω) this trivial case may not make sense.
