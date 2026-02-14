# Hyperreal numbers ε * ω = 1

[Hyperreal numbers Wiki](https://en.wikipedia.org/wiki/Hyperreal_number)

<!-- 
⚠️ this file is hard linked across several projects
occasionally check if they are in sync
diff ~/Documents/notes/hyperreals.md ~/dev/apps/wasp/wiki/hyperreals.md 
diff ~/Documents/notes/hyperreals.md ~/dev/script/lean4/hyper/Readme.md 
⚠️ if not in sync, re-link hard:
ln ~/Documents/notes/hyperreals.md ~/dev/apps/wasp/wiki/hyperreals.md 
ln ~/Documents/notes/hyperreals.md ~/dev/script/lean4/hyper/Readme.md 
 -->
  
In mathematics, the system of hyperreal numbers is a way of treating infinite and infinitesimal (infinitely small but non-zero) quantities. The hyperreals, or nonstandard reals ℝ⋆ are an extension of the real numbers ℝ with algebraic spanning elements ω ≈ ∞ and ε ≈ 1/∞.  

In 1960 Abraham Robinson (1918–1974) solved the three hundred year old problem of giving a rigorous development of the calculus based on infinitesimals.

The simple set of axioms for the hyperreal number system given here (and in Elementary Calculus) make it possible to present infinitesimal calculus at the college freshman level, avoiding concepts from mathematical logic. (It is shown in Chapter 15 of [hkeisler] that these axioms are equivalent to Robinson’s approach.)

(The following axioms are slightly different to Keislers, in that R∗ being an ordered field extension of R follows from the basic axioms: R∗ with the relation <∗ and the functions +,−,·,⁻¹ is an extension of R which satisfies the Trichotomy Law. (Proposition 1.18 in HKeisler))

Also for us ε is not an arbitrary infinitesimally small number but a fixed chosen one, similar to i:

The canonical infinitesimal ε has the property of being bigger than 0 and smaller than all positive standard numbers:  
0 < ε < r ∀r∊ℝ⁺  

Any infinitesimal a*ε has the property of being bigger than 0 and smaller than all positive standard numbers:  
0 < a*ε < r ∀a,r∊ℝ⁺

The canonical infinite ω has the property of being bigger than all standard numbers:  
r < ω   ∀r∊ℝ  
  
These two symbols can be linked via canonical gauging:  
  
ω := 1/ε     

1/∞ = 0 # ∞ is not part our field, just for illustration
1/0 = ∞  # not ω!    
ω/∞ =〚1〛?

⚠️ r * ω ≠ ω for 1≠r in ℝ ;unlike classical infinity notation where ∞=r·∞ ∀r>0 in ℝ  
In fact ∞ is not a number but may be the equivalence class ∞=〚ω〛 or ∞=〚ωᵚ〛wrt '≈' see below

We are mostly interested in applicative usage of Hyperreal numbers, defined axiomatically similar to the simple field extension of ℂ=ℝ(ⅈ)=ℝ+ⅈℝ or Dedekind–Peano axioms for Natural numbers.  
  
ℝ⋆ = ℝ(ε, ω)  # ordered field extension  
ℝ⋆ = R∗ = *R notation*, last one easiest to type
ℝ⋆ ≈ "algebraic-span / algebraic-closure(ℝ,ε)" # see term axioms # ω not needed because ω=1/ε
ℝ⋆ ≅ vectorial-span(1,ε,ω,ε²,ω²,…)   # 1/ε not needed because ω=1/ε

Definition 1.1. An element x∊R∗ is
• finite if |x| < r for some real r
• infinite if |x|>r for all real r
• infinitesimal if |x| < r for all positive real r

Notice that a positive infinitesimal is hyperreal but not real, and that the
only real infinitesimal is 0.

𝕀 infinitesimal small nonstandard numbers 《ε》 span including ε*ε … order -∞ or 1/∞   
𝕀⁻¹ infinitesimal small nonstandard numbers ℝ·ε = {a*ε a∊ℝ} outer span order -1    
𝕀⁻² infinitesimal small nonstandard numbers ℝ·ε² = {a*ε² a∊ℝ} outer span order -2  
𝔽 finite standard ℝ and nonstandard ℝ+𝕀 numbers <ℝ,ε>  {x: |x| < r for some r in ℝ}  
𝕐 unlimited infinite nonstandard numbers 《ω》 order ∞   
𝕐¹ unlimited infinite nonstandard numbers ℝ·ω = {a*ω a∊ℝ} order 1  
𝕐² unlimited infinite nonstandard numbers ℝ·ω² = {a * ω² a∊ℝ} order 2

ℝ⋆ ≅ ℝ×𝕀×𝕐  
  
Pure reals in ℝ⋆ are sometimes called 'appreciable' but should just be called 'real'.  

# Dual numbers
As shown below, using hyperreals allows any function to be differentiated in a very simple way, the derivative of the step function is ω at 0 which is our algebraic dirac delta.
Hyperreals convey information of higher derivatives, so the derivative of a ω 'jump' is a ω² 'shock' (jerk) ω³ 'snap' …
Sometimes we are not interested in higher order derivatives and are satisfied with first order nonstandard analysis. In this case we can introduce an 
## extra axiom ε² = 0
These special hyperreals are called "dual numbers".

https://en.wikipedia.org/wiki/Dual_number

This simplification yields "Smooth infinitesimal analysis". Terence Tao has referred to this concept under the name "cheap nonstandard analysis. “Calculus Made Easy” is a book on infinitesimal calculus originally published in 1910 which is now fully vindicated!

⚠️ since we have 1/ε = ω and 0 < ε < R  our theory slightly diverges from Dual numbers, 
instead may call them Dial numbers 𝔻 and adding i² = -1 iDial numbers 𝕀𝔻.

These "Dial numbers" do need an extra field in the class definition, 
one for each basis element (1,ε,ω) and they could thus be called Trial numbers (for 3).
Over the complex field (i²=-1) one would have six entries 
𝕊 := « 1, ε, ω, 𝕚, ε𝕚, ω𝕚 » Sick numbers (special supernumbers).
They are not superfluous, but could be tremendously useful, e.g. ω as dirac delta.
What about the spurious 𝕚ε * 𝕚ω = -1 , are they superfluous? This needs fruitful investigation!

## ω² = ∞
From ε² = 0 and ω:=1/ε and 1/∞:=0 follows ω² = ∞

A generalisation different to hyperreals are Grassmann numbers or supernumbers. Now widely used as a foundation for superspace, on which supersymmetry is constructed. 
https://en.wikipedia.org/wiki/Grassmann_number

The fermionic direction earns this name from the fact that fermions obey the Pauli exclusion principle: under the exchange of coordinates, the quantum mechanical wave function changes sign, and thus vanishes if two coordinates are brought together; this physical idea is captured by the algebraic relation ε² = 0

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
halo(x) = x+𝕀 = {x + a * ε for a in ℝ}  
halo(x) = x+𝕀 = {x + e for e in 𝕀}  

ε-disc(x) < halo(x)

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
∫(0,ω)(ε)  = 1   # ω * ε = 1
∫(-ω,ω)(ε) = 2/1 # infinite line AND/OR  
∫(-∞,∞)(ε) = ƒ   # -''-  can't be because 2ω=ω+ω and linear ∫
∫(-ε,ε)(ω) = 2/1 # spike  
∫(0,ε)(ω) =    1 # => dirac delta δ
∫1 = ω over ℝ for interval (-∞,∞)   
∫1 = √ω for interval [0,1] ?  
  
Similar to π vs τ we have ∫1 = 2ω over (-∞,∞) vs (0,∞) => ω 
Similar to π vs τ we have ∫ε = 2  over (-∞,∞) vs (0,∞) => 1
We use ⨍ or ƒ as integral over positives ∫(0,∞) as opposed to finite part integral
ƒ1 = ω  
∫1 = 2ω

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
ε * ∞ = ∞ ?  
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

where ω₀(x):= ω iff x≈0 # support in the halo of 0!

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
P(x in [0,1])=ε ? ε/2 ? or  
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
3 * 1/3 = 1 = 0.9̂ + 3ε ≠ 0.9̂ + ε  
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

# power

to define hˣ for arbitrary real numbers we can use exp and log
hˣ = exp(x·log(h))  
we need h² ≈ h * h as expected

This works in the julia implementation https://github.com/pannous/hyper-lean/blob/main/hyper.jl

# exponentiation

exp(h::Hyper) = ∑(0,∞) hⁿ/n!  
log(h::Hyper) = ∫(1,h) 1/x dx # or if we don't have integral yet:
log(h::Hyper) = ∑(1,h) (1-x)/x

  
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
ε * δ and ε * b are infinitesimal b * c is appreciable b * H and H * K are unlimited  
  
  
∫(0,ω)ε dx = 1/epsilon * epsilon - 0* epsilon = 1 # unabhängig von Eichung  

# Gamma and Zeta

n! = ∫tⁿ/eᵗ = Γ(n+1) = ∮1/τi·tⁿeᵗ

see

# [[Riemann]] conjecture

# Gauge Theory

Unfortunately, the gauge theory in physics has nothing to do with our epsilon gauge:

Gauge theories associate each point x on the spacetime manifold M with a (usually complex)
vector space Vx. A basis for each Vx is called a gauge.

"Gauge Theories and Fiber Bundles: Definitions, Pictures, and Results" by Adam Marsh

# Recent developments

• discovery of Kanovei and Shelah [KS 2004] that
the hyperreal number system, like the real number system, can be built as an explicitly definable mathematical
structure. Earlier constructions of the hyperreal number system depended on an arbitrarily chosen parameter such as an
ultrafilter.

The basic concepts of the calculus were originally developed in the seven-
teenth and eighteenth centuries using the intuitive notion of an infinitesimal,
culminating in the work of Gottfried Leibniz (1646-1716) and Isaac Newton
(1643-1727).

[hkeisler]
a) Elementary Calculus /
https://people.math.wisc.edu/~hkeisler/calc.html
https://people.math.wisc.edu/~hkeisler/keislercalc-03-01-24.pdf
b) FOUNDATIONS OF INFINITESIMAL CALCULUS H. JEROME KEISLER
Department of Mathematics University of Wisconsin, Madison, Wisconsin, USA
keisler@math.wisc.edu
https://people.math.wisc.edu/~hkeisler/foundations.pdf#:~:text=R%20%E2%88%97%20is%20an%20ordered,However%2C%20the%20algebraic%20facts

"In the nineteenth century, infinitesimals were rejected in favor of the ε,δ approach, because
mathematicians had not yet discovered a correct treatment of infinitesimals.
Since then generations of students have been taught that infinitesimals do not
exist and should be avoided."

In the optional Section 1G at the end of this chapter we build a hyperreal number system as an ultrapower of the real
number system. This proves that there exists a structure which sat-
isfies the axioms.

# galaxy

galaxy(x) = {y∈R∗ : x−y is finite}
galaxy(x) == {x+y, where y is finite}
galaxy(0) = 𝔽 = "The Finites"
Theorem 1.3. galaxy(0) = 𝔽 is subring of R∗  (|x+y| < r+s, |x−y| < r+s, |xy| < rs)
Corollary 1.4. Any two galaxies are either equal or disjoint.

monad(0)=halo(0) = {y∈R∗ : x−y is infinitesimal}
monad(0) == {x+y, where y is infinitesimal}
Theorem 1.5
a) halo(0) = 𝕀 is subring of R∗
b) 𝕀 is an ideal in 𝔽 = ℝ+𝕀 :  ε * r in monad(0) for r in ℝ
(a) Sums, diﬀerences, and products of infinitesimals are infinitesimal.
(b) The product of an infinitesimal and a finite element is infinitesimal.

Proof
Let b be finite, say |b| < t, 1≤t∈R. Then for any positive real r we have
|ε| < r/t,|εb| < (r/t)t= r. Therefore εb is infinitesimal

Corollary 1.6. Any two monads are equal or disjoint.
The relation x≈y is an equivalence relation on R∗

Theorem 1.9. (Standard Part Principle) Every finite x∈R∗ is infinitely
close to a unique real number r ∈R. That is, every finite monad contains a
unique real number.

Corollary 1.11. Let x and y be finite.
(i) x≈y if and only if st(x) = st(y).
(ii) x≈st(x).
(iii) If r∈R then st(r) = r.
(iv) If x≤y then st(x) ≤st(y).
Theorem 1.12. The standard part function is a homomorphism of the ring
galaxy(0) onto the field of real numbers. That is, for finite x and y,
(i) st(x+ y) = st(x) + st(y),
(ii) st(x−y) = st(x)−st(y),
(iii) st(xy) = st(x)st(y).
Corollary 1.13. Let x and y be finite.
(i) If st(y) ̸= 0 then st(x/y) = st(x)/st(y).
(ii) If x≥0 and y= n √x then st(y) =n st(x).

1C. Axioms for the Hyperreal Numbers (§Epilogue)
The properties of a hyperreal number system are given by five axioms. The
first three of these axioms were stated in Section 1A. Before giving a precise
statement of the remaining two axioms, we describe the intuitive idea. The
real and hyperreal numbers are related by a ∗mapping such that:
(1) With each relation X on R there is a corresponding relation X∗on R∗ , called the natural extension of X.
(2) The relations on R have the same “elementary properties” as their nat-
ural extensions on R∗

The diﬃculty in making (2) precise is that we must explain exactly what an
“elementary property” is. The properties “X ⊆Y”, “X is a function”, and
“X is a symmetric binary relation” are elementary. On the other hand, the
Archimedean Property and the Completeness Property must not be elemen-
tary, because no proper extension of R is an Archimedean or complete ordered
field. In most expositions of the subject an “elementary property” is taken to
be any sentence in first order logic. However, it is not appropriate to begin
a calculus course by explaining first order logic to the students because they
have not yet been exposed to the right sort of examples. It is better to learn
calculus first, and at some later time use the ε,δ conditions from calculus as
meaningful examples of sentences in first order logic. Fortunately, the notion
of a sentence of first order logic is not necessary at all in stating the axioms. It
turns out that a simpler concept which is within the experience of beginning
students is suﬃcient. This is the concept of a (finite) system of equations and
inequalities. We shall see in Chapter 15 at the end of this monograph that we
get equivalent sets of axioms using either the simple concept of a system of
equations and inequalities or the more sophisticated concept of a sentence of
first order logic.

# TERM AXIOMS

A term is an expression which can be built up using the following rules:
• Every variable is a term.
• Every real constant is a term.
• If τ1,... ,τn are terms and f is a real function of n variables, then
f(τ1,... ,τn) is a term.
A term which contains no variables is called a constant term.

The following axioms describe a hyperreal number system as a triple (∗,R,R∗),
where R is called the field of real numbers, R∗the field of hyperreal num-
bers, and ∗the natural extension mapping.

Axiom A
R is a complete ordered field.
Axiom B
R∗ is an ordered field extension of R.
Axiom C
R∗ has a positive infinitesimal.
Axiom D (Function Axiom)
For each real function f of n variables there is a corresponding hyperreal
function f∗ of n variables, called the natural extension of f. The field
operations of R∗ are the natural extensions of the field operations of R.

By a hyperreal solution of a system of formulas S with the variables
x1,... ,xn we mean an n-tuple (c1,... ,cn) of hyperreal numbers such that
all the formulas in S are true when each function is replaced by its natural
extension and each xi is replaced by ci.

Axiom E (Transfer Axiom)
Given two systems of formulas S,T with the same variables, if every real
solution of S is a solution of T, then every hyperreal solution of S is a solution
of T.

Corollary 1.15. Any two systems of formulas with the same variables
which have the same real solutions have the same hyperreal solutions. (This
was called the Solution Axiom in the 1976 edition).

Corollary 1.16. (i) If a system S of formulas is true for all real numbers,
it is also true for all hyperreal numbers.
(ii) If a system of formulas has no real solutions, it has no hyperreal solu-
tions.

# Function Extension

Corollary 1.17. Let f be a real function of n variables and let c1,... ,cn
be real constants. If f(c1,... ,cn) is defined then f∗(c1,... ,cn) = f(c1,... ,cn)

Proposition 1.18. Assume Axioms A, C, D, E, and also that R∗ with the
relation <∗ and the functions +,− ,· ,−1 is an extension of R which satisfies
the Trichotomy Law. Then R∗ is an ordered field, so Axiom B holds.

# Limes via ≈

Definition 3.1. Let L, c be real numbers. L is the limit of f(x) as x approaches c, in symbols
L = lim x→c f(x), if whenever x≈c but x̸≠c, we have f(x)≈L.
If there is no such L we say that the limit does not exist.

Definition 3.12. Let Y be a subset of the domain of f. f is continuous
on Y if whenever c∈Y, x≈c, and x∈Y∗, we have f(x) ≈f(c).

ε,δ Conditions for Limits

………………………………………………………………………………………………………………………………………………………………………………………………………
… GOES ON TO PROOF ALL standard Facts of Elementary Analysis via Hyperreals
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

Like y=ln(x) x=e(y) => dx/dy=x dy/dx=1/x

# infinite partial sum

The partial sum sequence ⟨Sₙ⟩ is defined by
Sₙ = a0 + a1 +···+ aₙ = ∑k=0￫n aₖ

By the Function Axiom, the natural extension of the function Sn has a value SH for each positive infinite hyperinteger
H, which we call the infinite partial sum
SH = a0 + a1 +···+ aH = ∑k=0￫H aₖ

That is, for every positive infinite hyperinteger H,
S ≈ a0 + a1 +···+ aH

# The infinite Riemann sum is the natural extension
S∗(dx) = ∑ f(x) dx as extension to partition of [a,b]
S(△x) = ∑f(x)△x = f(x0=a)△x+ f(a+△x)△x+···+ f(a+△x·(n−1))△x+ f(xn)(b−xn) wlog evenly
∫f(x) dx = st ( ∑ f(x) dx )  for dx in Hyperreals
Looks like cheating because S(△x) has hidden variable n depending on △x BUT
Since the finite Riemann sum is defined for all real △x > 0,
the infinite Riemann sum is defined for all hyperreal dx > 0.

∫f := ∑f(.)ε wlog (Theorem 4.7)  set of all antiderivatives of f "indefinite integral"
⚠️ ε is not purely a 'multiplier' as it appears in f(nε) thus ∫fε=∫x,2ε !!! ⚠️

Theorem 4.6. Properties of integral ∫[a,b]c=c(b-a) …

Formerly definition, now
Corollary 4.8. ∫[a,b] f(x) dx == lim △x→0+ ∫ a b f(x)△x

Fundamental Theorem of Calculus (§4.2)
The definite integral is the only area function for f

Second Fundamental Theorem of Calculus (§4.2)
f(c) = F′(c)

The length of a smooth parametric curve is the integral
s=∫√(x'(t)²+y'(t)²) dt

# Vectors

Natural extension of ℝ⋆ = R∗ = * R to dimension n => * R^n ℝ⋆ⁿ basis remains the same
unit vector A/|A|
A hyperreal vector A has real length if |A|is real.
A unit vector is a hyperreal vector of length 1.
If A ̸= 0, the unit vector of A is the unit vector U=1 |A|A.
A has real direction if A ̸= 0 and the unit vector of A is a real vector.
Two nonzero hyperreal
vectors A and B are said to be almost parallel if their unit vectors U and
V are such that either U ≈V or U ≈−V.

halo/monad(A) and galaxy(A) transfer via |A|

Proposition 10.2.
(i) A is infinitesimal if and only if all its components are infinitesimal.
(ii) A is finite if and only if all its components are finite.
(iii) A is infinite if and only if at least one of its components is infinite.
(iv) A ≈B if and only if a1 ≈b1,... ,an ≈bn

standard part
st(A) is defined as the real vector(!) st(A) = st(a1)j1 +···+ st(an)jn , j real basis
Thus st(A) is the unique real vector infinitely close to A.

Two nonzero hyperreal vectors A and B are said to be almost parallel if their
unit vectors U and V are such that either U≈V or U≈−V.

Ai almost linearly dependent if there is a c such that ∑cAi≈[0]

# PARTIAL DIFFERENTIATION

distance between two hyperreal points
P(x1,y1) and Q(x2,y2) is |P−Q|= (x2−x1)² + (y2−y1)²

total diﬀerential of z = f(x,y)
dz given by dz = fx(x,y)△x+ fy(x,y)△y= ∂z/∂x·△x+ ∂z/∂y·△y

Chain Rule and Implicit Functions

Hyperreal Mean Value Theorem

MULTIPLE INTEGRATION

VECTOR CALCULUS

Line Integrals along smooth curve

DIFFERENTIAL EQUATIONS (existence and uniqueness of solutions)

LOGIC AND SUPERSTRUCTURES

# Random notes

√(ε + ω) ≈ ∑ωⁿ/2ⁿn! ~ … + 0.020833̅ω^3 + 0.125ω² + 0.5ω + 1   
Maclaurin expansion coefficient of e^{x/2} ??
