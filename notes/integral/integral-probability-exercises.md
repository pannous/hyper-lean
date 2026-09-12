# Twenty exercises in algebraic probability on ordinary intervals

These exercises use the framework of
[`integral-probability-foundations.md`](integral-probability-foundations.md):
ordinary real intervals, an integral with `dx = epsilon`, and densities that
may take the infinite value `omega` at an atom. Nothing is counted, and no
hyperfinite sample space is constructed.

Two rules generate almost everything below. The integral is the hyperfinite
left-endpoint Riemann sum with `dx = epsilon`,

\[
\int_{[a,b)} f(x)\,dx
:=\sum_{k=0}^{(b-a)\omega-1} f(a+k\epsilon)\,\epsilon ,
\]

and a probability is the integral of a density over the event,

\[
P(E)=\int_E p(x)\,dx .
\]

Since the point `y` is the single dot `[y, y+epsilon)`, the first rule
specializes to the one identity used over and over:

\[
P(\{y\})=p(y)\,\epsilon .
\]

An atom of mass `a` is not a separate ingredient but the density value
`p(y) = a*omega`, so that `P({y}) = a*omega*epsilon = a`. The standard part
`st` is applied only where it is explicitly requested.

The readiness labels say what the present Lean~4 development supports:

- **Now:** the value and its derivation use only single-dot integrals and
  `R*` arithmetic, which the concrete representation already has.
- **Partial:** the closed form is exact and short, but the derivation needs a
  hyperfinite sum over the `(b-a)*omega` dots of an interval, which has no
  index type yet.
- **Research:** additionally needs transcendental densities, a proved
  `st`-compatibility theorem, or a genuine conditional-law construction.

⚠️ No part of this framework is formalized in Lean yet. Unlike the counting
curriculum in `notes/counting/`, these exercises have **no checked solution
kernels**; the labels describe distance from the current code, not achieved
proofs.

## Exercise 1 — The probability of hitting an exact number

**Problem.** Let `X` be uniform on `[0,1)`, so `p(x) = 1`. Compute `P(X = y)`
for a specified `y`, prove that it is positive, and give its standard part.

**Why this framework.** This is the question the whole construction exists to
answer. Classically the answer is `0`, which then has to be explained away as
"probability zero but not impossible". Here the answer is an ordinary
algebraic value, and the classical `0` is recovered as its shadow.

**Solution.** The point `y` is one dot of width `epsilon`, so the integral has
a single term:

\[
P(X=y)=\int_{[y,y+\epsilon)} 1\,dx=1\cdot\epsilon=\epsilon>0,
\qquad \operatorname{st}(\epsilon)=0 .
\]

No limit and no counting argument is involved: `epsilon` appears because
`dx = epsilon`.

**Ingredients and readiness.** The integral axiom on one dot, positivity of
`epsilon`, and `st(epsilon) = 0`. **Now.**

## Exercise 2 — Finitely many targets

**Problem.** With `X` uniform on `[0,1)`, let `A` be a set of `r` specified
points, `r` a standard positive natural number. Find `P(A)` and the ratio
`P(A)/P({y})`.

**Why this framework.** Both events are classically null, so their shadows
cannot be compared. The algebraic values differ by exactly the factor one
expects.

**Solution.** The dots are disjoint, so the integral is additive over them:

\[
P(A)=r\epsilon,\qquad \frac{P(A)}{P(\{y\})}=r .
\]

**Ingredients and readiness.** Finite additivity over disjoint dots and
cancellation of `epsilon`. **Now.**

## Exercise 3 — Intervals are unharmed, and the total is exactly one

**Problem.** For `X` uniform on `[0,1)` and standard `0 <= c < d <= 1`,
compute `P([c,d))` and verify `P([0,1)) = 1` exactly.

**Why this framework.** A reformulation that changed ordinary interval
probabilities would be useless. The point of the `epsilon`-resolution is that
it is invisible at finite scale.

**Solution.** The interval `[c,d)` consists of `(d-c)*omega` dots, each
contributing `epsilon`:

\[
P([c,d))=(d-c)\omega\cdot\epsilon=d-c ,
\]

and with `c = 0`, `d = 1` this is `omega*epsilon = 1`. The gauging axiom is
exactly what makes the total mass come out without an error term.

**Ingredients and readiness.** A hyperfinite sum of a constant over the dots
of an interval, and `epsilon*omega = 1`. **Partial.**

## Exercise 4 — Half-open versus closed, and what a normalization costs

**Problem.** Integrate the constant `1` over the *closed* interval `[0,1]`. Then
find the density of the uniform law on `[0,1]` and recompute `P({0})`.

**Why this framework.** Classically `[0,1)` and `[0,1]` have the same measure
and the distinction is pedantry. Here they differ by exactly one dot, and the
difference is the size of a point.

**Solution.** The closed interval contains one more dot than the half-open
one, so

\[
\int_{[0,1]} 1\,dx=(\omega+1)\epsilon=1+\epsilon\neq 1 .
\]

A genuine density on `[0,1]` must therefore be renormalized,

\[
p=\frac1{1+\epsilon}=1-\epsilon+\epsilon^{2}-\cdots,
\qquad
P(\{0\})=p\,\epsilon=\epsilon-\epsilon^{2}+\cdots .
\]

Both conventions are consistent; only the half-open one gives `p = 1`.

**Ingredients and readiness.** Dot counting of an interval, inversion of
`1 + epsilon`, and series expansion. **Partial;** the inversion of a
multi-term denominator is the same gap recorded in the counting curriculum.

## Exercise 5 — Conditioning on an ordinary interval

**Problem.** With `X` uniform on `[0,1)` and `y` in `[a,b) subset [0,1)`,
compute `P(X = y given a <= X < b)`.

**Why this framework.** Classically the numerator is `0` and the quotient is
undefined; here the infinitesimal cancels against a finite denominator and
returns the answer one expects, an infinitesimal rescaled by the width.

**Solution.**

\[
P(X=y \mid a\le X<b)=\frac{\epsilon}{b-a},
\]

which is the point probability of the uniform law on `[a,b)`, as conditioning
should give.

**Ingredients and readiness.** Conditional probability as field division and
division of `epsilon` by a nonzero standard number. **Now.**

## Exercise 6 — A nonuniform density is read off at the point

**Problem.** Let `X` have the triangular density `p(x) = 2x` on `[0,1)`.
Verify the normalization, compute `P(X = y)`, and compare two points `y1` and
`y2`.

**Why this framework.** The classical statement "all points have probability
zero" hides that some points are more likely than others. Here the likelihood
ratio of two points is finite, visible, and equal to the density ratio.

**Solution.** Normalization is Exercise 13's sum with a factor `2`, giving
`1 - epsilon`; on the half-open convention the exactly normalized triangular
density is `p(x) = 2x/(1-epsilon)`. In either case

\[
P(X=y)=p(y)\,\epsilon,
\qquad
\frac{P(X=y_1)}{P(X=y_2)}=\frac{p(y_1)}{p(y_2)}=\frac{y_1}{y_2}.
\]

Every point still has infinitesimal probability, but their ratios are ordinary
real numbers.

**Ingredients and readiness.** Single-dot integration and division of
infinitesimals of equal order. **Now** for the ratio; **Partial** for the exact
normalizing constant.

## Exercise 7 — An atom is a density value, not a second mechanism

**Problem.** Let `p` be the density that equals `omega/2` on the dot at `0`
and `1/2` on `(0,1)`. Show that `p` is a probability density, compute
`P({0})` and `P({y})` for `y != 0`, and compare their orders.

**Why this framework.** Classical theory needs two different objects — a
density plus a discrete point mass — and a case split in every formula. Here
one density carries both, because an infinite value is available.

**Solution.** The total mass splits into the atom's single dot and the rest:

\[
\int p=\frac\omega2\cdot\epsilon+\frac12\cdot 1=\frac12+\frac12=1 .
\]

Then

\[
P(\{0\})=\frac\omega2\cdot\epsilon=\frac12,
\qquad
P(\{y\})=\frac\epsilon2 \quad (y\neq0),
\qquad
\frac{P(\{0\})}{P(\{y\})}=\omega .
\]

The atom is infinitely more likely than an ordinary point, which is the exact
algebraic content of the word "atom".

**Ingredients and readiness.** An `omega`-valued density, splitting an
integral over disjoint regions, and order comparison. **Now** for the two point
values; **Partial** for the normalization integral.

## Exercise 8 — The Dirac delta is the derivative of the step, exactly

**Problem.** Let `H` be the Heaviside step, `H(x) = 1` for `x >= 0` and `0`
otherwise. Compute the algebraic derivative `dH(x) = (H(x+epsilon)-H(x))/epsilon`
at every `x`, and integrate the result over `[-1,1)`.

**Why this framework.** Classically `dH` is not a function and the identity
`integral of dH = 1` needs distribution theory. Here `dH` is an ordinary
function taking the value `omega` on one dot.

**Solution.** The difference quotient vanishes unless the dot straddles the
jump, and

\[
\partial H(x)=\omega \quad\text{for } x\in[-\epsilon,0),
\qquad \partial H(x)=0 \text{ otherwise},
\]

so `dH = delta_{-epsilon}` and

\[
\int_{[-1,1)}\partial H(x)\,dx=\omega\cdot\epsilon=1 .
\]

The fundamental theorem of calculus therefore holds for the step function on
the nose, with no distributions and no limits.

**Ingredients and readiness.** The algebraic derivative, a one-dot integral,
and `epsilon*omega = 1`. **Now.**

## Exercise 9 — Three orders of point probability

**Problem.** At a point `y`, consider densities `p(y) = a*omega`, `p(y) = b`,
and `p(y) = c*epsilon` with standard positive `a,b,c`. Compute `P({y})` in
each case and order the three results.

**Why this framework.** The classical shadow assigns `0` to the last two and
`a` to the first, collapsing an entire ordered scale into two values.

**Solution.** By `P({y}) = p(y)*epsilon`,

\[
a\omega\cdot\epsilon=a,
\qquad
b\cdot\epsilon=b\epsilon,
\qquad
c\epsilon\cdot\epsilon=c\epsilon^{2},
\]

so `a > b*epsilon > c*epsilon^2` regardless of the standard coefficients. A
point's rarity order is exactly the negative of the density's order.

**Ingredients and readiness.** Multiplication by `epsilon`, and comparison by
leading exponent. **Now.**

## Exercise 10 — The dart, with no grid at all

**Problem.** Let `(X,Y)` be uniform on the unit square, `p = 1`. Compute the
probability of one specified point.

**Why this framework.** The counting treatment of the dart needs an
`omega` by `omega` grid convention. Here the same answer comes from doing two
integrations instead of one.

**Solution.** The area element is `dA = dx*dy = epsilon^2`, so a single dot of
the plane has

\[
P(\{(x_0,y_0)\})=1\cdot\epsilon^{2}=\epsilon^{2}.
\]

**Ingredients and readiness.** A product integral and `epsilon^2`. **Partial**
for the product construction; the value itself is **Now**.

## Exercise 11 — A segment beats a point by exactly `omega`

**Problem.** In the same square, compute `P(Y = X)`, the probability that the
two coordinates agree, and compare it with Exercise 10.

**Why this framework.** Both events are classically null. The framework must
explain why hitting a line is infinitely easier than hitting a point without
appealing to a chosen grid.

**Solution.** Condition on `X` and integrate the one-dimensional point
probability:

\[
P(Y=X)=\int_0^1 P(Y=x)\,dx=\int_0^1 \epsilon\,dx=\epsilon,
\qquad
\frac{P(Y=X)}{P(\{(x_0,y_0)\})}=\omega .
\]

Each integration that is *not* performed costs one factor of `epsilon`; this
is the codimension law of the counting model, derived instead of postulated.

**Ingredients and readiness.** Iterated integration and monomial division.
**Partial.**

## Exercise 12 — A uniform law on the whole line

**Problem.** Take the ambient line to be `[-omega, omega)`. Find the uniform
density on it, compute `P({y})` and `P([a,b))`, and compare `P({y})` with the
point probability of the uniform law on `[0,1)`.

**Why this framework.** Classically there is no uniform distribution on `R` at
all. Here there is one, and its point probability lands in a strictly rarer
order than that of the unit interval.

**Solution.** The ambient length is `2*omega`, so normalization forces
`p = 1/(2*omega) = epsilon/2` and

\[
P(\{y\})=\frac\epsilon2\cdot\epsilon=\frac{\epsilon^{2}}2,
\qquad
P([a,b))=(b-a)\frac\epsilon2 .
\]

Comparing with Exercise 1,

\[
\frac{P_{\mathbb R}(\{y\})}{P_{[0,1)}(\{y\})}=\frac\epsilon2 ,
\]

infinitesimal: a point is infinitely rarer when the target is the whole line.
Any finite interval likewise gets only infinitesimal probability, which is the
correct and previously unavailable statement.

**Ingredients and readiness.** The ambient-line convention, inversion of
`2*omega`, and order comparison. **Partial;** the choice of `[-omega, omega)`
over the one-sided convention must be stated, not derived.

## Exercise 13 — Exact moments of the uniform law

**Problem.** For `X` uniform on `[0,1)`, compute `E[X]`, `E[X^2]`, and
`Var(X)` from the integral, without taking any limit.

**Why this framework.** Classically the answers are `1/2` and `1/12`. The
exact values record, in addition, the bias of the integral convention that
produced them.

**Solution.** With `x = k*epsilon` and the finite power-sum identities,

\[
E[X]=\sum_{k<\omega}k\epsilon\cdot\epsilon
=\epsilon^{2}\frac{\omega(\omega-1)}2=\frac12-\frac\epsilon2,
\]

\[
E[X^{2}]=\frac13-\frac\epsilon2+\frac{\epsilon^{2}}6,
\qquad
\operatorname{Var}(X)=\frac1{12}-\frac{\epsilon^{2}}{12}.
\]

Taking `st` recovers `1/2` and `1/12` only after the exact corrections have
been displayed.

**Ingredients and readiness.** Hyperfinite power sums and substitution
`omega = 1/epsilon`. **Research:** an index genuinely ranging over `omega`
dots does not exist in the current Lean model, even though the closed forms
are ordinary `R*` values.

## Exercise 14 — The integral convention is visible at order `epsilon`

**Problem.** For a standard `f` on `[0,1)`, compare the left-endpoint,
right-endpoint, and midpoint sums. Apply the result to `f(x) = x`.

**Why this framework.** Classically all three converge to the same number and
the choice is irrelevant. Here they are different hyperreal values, and their
difference is exactly the information the limit destroys.

**Solution.** The right and left sums differ only in their end terms,

\[
\int^{\text{right}}f-\int^{\text{left}}f=\epsilon\,(f(1)-f(0)),
\]

and for `f(x) = x` the midpoint rule gives exactly `1/2`, against
`1/2 - epsilon/2` and `1/2 + epsilon/2`. All three agree after `st`.

Conclusion: "the integral" is not one object in this framework. A convention
must be fixed, and every exercise above uses the left-endpoint one.

**Ingredients and readiness.** Telescoping of a hyperfinite sum and
`st`-invariance. **Research** for the general statement; **Now** for the
`f(x) = x` instance, whose three values are explicit `R*` numbers.

## Exercise 15 — A mixed law needs no case split

**Problem.** With the density of Exercise 7 — mass `1/2` at the point `0` and
`1/2` spread uniformly — compute `E[X]` and the distribution function
`F(t) = P(X < t)`.

**Why this framework.** Classical treatment of a mixed law splits every
formula into a discrete sum plus an integral. Here `F = integral of p` with no
case distinction, and the jump appears automatically.

**Solution.** The atom contributes at `x = 0` and the continuous part is
Exercise 13 halved:

\[
E[X]=0\cdot\frac12+\frac12\left(\frac12-\frac\epsilon2\right)
=\frac14-\frac\epsilon4 ,
\]

\[
F(t)=\frac12+\frac t2 \quad\text{for } 0<t\le1,
\qquad F(0)=0,\quad F(\epsilon)=\frac12 .
\]

The jump of `F` at `0` is the atom's mass, produced by integrating an
`omega`-valued density over one dot rather than by adding a point weight.

**Ingredients and readiness.** Integration of a density with an `omega` value,
and the moment computation of Exercise 13. **Research,** for the same reason
as Exercise 13.

## Exercise 16 — Point probability is not invariant, and should not be

**Problem.** Let `X` be uniform on `[0,1)` and `Y = 2X`. Find the density of
`Y`, compute `P(Y = y)`, and reconcile it with `P(X = y/2) = epsilon`.

**Why this framework.** A reader meeting `P({y}) = epsilon` for the first time
usually asks whether `epsilon` is an absolute "size of a point". It is not,
and the change-of-variables rule shows exactly what it is relative to.

**Solution.** `Y` is uniform on `[0,2)`, so `p_Y = 1/2` and

\[
P(Y=y)=\frac12\epsilon .
\]

There is no contradiction: the event `{Y = y}` is `{X = y/2}` only up to
resolution, since the map doubles dot widths, so one dot of `Y` corresponds to
half a dot of `X`. In general `p_Y(y) = p_X(x)/|g'(x)|` for `y = g(x)`, with
the algebraic derivative, and `P({y}) = p_Y(y)*epsilon` follows.

**Ingredients and readiness.** Change of variables with the algebraic
derivative, and the observation that dots are not preserved by non-isometries.
**Now** for the linear case; **Partial** in general.

## Exercise 17 — An exponential law

**Problem.** Let `p(x) = lambda*e^{-lambda*x}` on `[0, omega)` with standard
`lambda > 0`. Compute `P(X = y)` and `P(X >= t)` for standard `t`, and discuss
the normalization.

**Why this framework.** The tail of an exponential law on an infinite domain
is where the ambient-line convention and the transcendental functions have to
agree; the framework should not need a separate limiting argument.

**Solution.** Pointwise the rule is immediate,

\[
P(X=y)=\lambda e^{-\lambda y}\epsilon ,
\]

so a point far out in the tail is still infinitesimal but by an ordinary
factor `e^{-lambda*y}` less likely than one near `0`. The tail and the total
are hyperfinite geometric sums, and both carry a discretization correction:

\[
\int_{[0,\omega)} p
=\frac{\lambda\epsilon}{1-e^{-\lambda\epsilon}}\left(1-e^{-\lambda\omega}\right)
=1+\frac{\lambda\epsilon}2+O(\epsilon^{2}),
\qquad
P(X\ge t)=e^{-\lambda t}\left(1+\frac{\lambda\epsilon}2+O(\epsilon^{2})\right).
\]

So the left-endpoint convention *over*-counts by `lambda*epsilon/2`, and the
density must be renormalized by that factor to be exact; the truncation at
`omega` costs only `e^{-lambda*omega}`, an infinitesimal smaller than every
power of `epsilon`. The classical answers `1` and `e^{-lambda*t}` are the
standard parts.

**Ingredients and readiness.** A transcendental density, hyperfinite geometric
summation, and comparison of `e^{-lambda*omega}` with all powers of `epsilon`.
**Research:** `Hyper/HyperTranscendental.lean` has `hexp` but it is not
connected to any integral.

## Exercise 18 — Bayes with an atom and a density in one formula

**Problem.** A parameter `T` is `0` with probability `1/2` and otherwise
uniform on `(0,1)`. Given `T = t`, an observation `Z` has a standard density
`f(z | t)`. Compute the posterior `P(T = 0 given Z = z)`.

**Why this framework.** This is the classical "mixed prior" nuisance, where
the discrete and continuous parts of the prior must be handled by different
machinery and the observation `{Z = z}` is itself a null event.

**Solution.** Write the prior as one density: `pi = (omega/2)` on the dot at
`0` and `1/2` on `(0,1)`. Every term of Bayes' rule then carries one factor
`epsilon` from the observed event `{Z = z}`, which cancels, and the atom's
`omega` cancels the `epsilon` of its own dot, leaving

\[
P(T=0\mid Z=z)
=\frac{\tfrac12 f(z\mid 0)}
       {\tfrac12 f(z\mid 0)+\tfrac12\int_0^1 f(z\mid t)\,dt } .
\]

The answer is finite and ordinary — the infinitesimals cancel — but it was
obtained without ever conditioning on a classically null event by fiat.

**Ingredients and readiness.** Joint densities, cancellation of `epsilon`
between numerator and denominator, and inversion of a finite value.
**Research:** needs a joint-density construction and the `st`-compatibility of
the inner integral.

## Exercise 19 — The Borel–Kolmogorov paradox dissolves

**Problem.** For `(X,Y)` uniform on the unit square, condition on the diagonal
`D = {Y = X}`. Compute `P(X in [a,b) given D)` and explain why the classical
paradox does not arise.

**Why this framework.** Classically `P(D) = 0`, conditioning on `D` requires
choosing a parametrization, and different parametrizations give different
answers — the Borel–Kolmogorov paradox. Here `P(D) = epsilon > 0`, so the
elementary definition applies and the answer is unique.

**Solution.** By Exercise 11, `P(D) = epsilon`. The part of the diagonal over
`[a,b)` has probability `(b-a)*epsilon`, so

\[
P\big(X\in[a,b)\mid D\big)=\frac{(b-a)\epsilon}{\epsilon}=b-a .
\]

The conditional law is uniform, and there was no choice to make: the diagonal
is an ordinary event of positive probability, so `P(·|D)` is the ordinary
quotient. A different description of the same set of dots gives the same
value, because it is the same event. The paradox was an artifact of dividing
by zero.

⚠️ The dissolution is real but narrow: it holds for the dot resolution fixed
in the foundations note. A *different* resolution convention describes a
different event, and the classical ambiguity reappears as the choice of
convention — now explicit and stated, instead of hidden.

**Ingredients and readiness.** Conditioning on an infinitesimal-probability
event, and the diagonal integral of Exercise 11. **Research** as a general
theorem; the displayed algebra is **Partial**.

## Exercise 20 — What must be proved before this is a measure theory

**Problem.** Identify precisely what is needed to prove: (a) that the standard
part of the hyperfinite integral is the classical Riemann integral, for every
standard Riemann-integrable `f`; (b) that `P` is finitely additive over arbitrary disjoint unions of dots;
(c) that `P` is *not* countably additive in the classical sense, and why that
is not a defect.

**Why this framework.** An honest curriculum has to state where the
reformulation stops being elementary. The framework's own advertising —
"probability is just an integral" — is only justified once these are settled.

**Solution sketch.** (a) needs either a transfer principle or an explicit
uniform-continuity estimate: the hyperfinite sum differs from every finite
Riemann sum of mesh `>= epsilon` by an infinitesimal, which requires control of
the modulus of continuity, exactly the content the classical limit hides.
(b) holds by construction for unions of dots, since the integral is a sum over
disjoint dots; the work is in defining which sets are unions of dots.
(c) a countable union of dots is *not* a hyperfinite sum, so the classical
countable-additivity axiom is not available and must not be assumed. This is
the same boundary documented in `notes/counting/sigma-algebra-not-needed.md`:
the framework computes exactly on constructed events and makes no claim about
an arbitrary sigma-algebra.

**Ingredients and readiness.** Transfer or explicit estimates, a theory of
dot-unions, and a Loeb-style comparison with classical measure.
**Research:** this is the capstone, and none of its prerequisites exist in the
repository today.
