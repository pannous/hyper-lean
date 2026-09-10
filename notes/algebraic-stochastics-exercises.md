# Twenty algebraic stochastics and statistics exercises over `R*`

These exercises follow the philosophy of `Hyper/DartPointProbZero.lean`, with
one deliberate change of language and foundation. A probability is an
algebraic value in `R*`. On a uniform hyperfinite sample space `Omega`, it is
computed by

\[
P(A)=\frac{\#A}{\#\Omega}.
\]

In the general symbolic counting pattern, if the ambient experiment has
`A*omega^n` outcomes and an event has `c*omega^d` favorable outcomes, then

\[
P(E)=\frac{c\omega^d}{A\omega^n}
=\frac cA\epsilon^{n-d}.
\]

This normalized ratio, rather than a geometry-specific primitive, is the
foundation used below.

More general probabilities are built from these ratios with addition,
multiplication, complements, and division. We fix a positive infinitesimal
`epsilon`, put `omega = 1/epsilon`, and use `st` only when we explicitly want
the ordinary real shadow of an answer. The exercises do not claim that
classical methods cannot obtain related real-valued results. Their advantage
is that they retain positive infinitesimal probabilities, comparisons between
different orders of rarity, and finite-resolution corrections that the
classical shadow turns into zero or discards.

The readiness labels distinguish the intended framework from the present Lean
implementation:

- **Now:** the result reduces to arithmetic and order facts already available
  for the concrete `R*` representation, although a polished event API may
  still be absent.
- **Partial:** the scalar answer is representable now, but reusable random
  variables, hyperfinite counts, or finite-sum infrastructure is missing.
- **Research:** the exercise deliberately requires a substantive extension of
  the framework.

## Exercise 1 — One exact outcome

**Problem.** Let `Omega = {0, 1, ..., omega - 1}` be uniform, and let `j` be
one specified outcome. Compute `P({j})`, prove that it is positive, and compute
its standard part.

**Why this framework.** An ordinary continuum model records only the shadow
`P({j}) = 0`. Hyperfinite counting records simultaneously that the outcome is
possible and that its ordinary shadow is zero.

**Solution.** There is one favorable outcome among `omega`, so

\[
P(\{j\})=\frac1\omega=\epsilon>0,
\qquad \operatorname{st}(P(\{j\}))=0.
\]

**Ingredients and readiness.** Hyperfinite cardinality, `epsilon * omega = 1`,
positivity, and `st(epsilon) = 0`. **Now** for the scalar theorem; a literal
`Omega` with `omega` elements still needs a hyperfinite-set interface.

## Exercise 2 — A finite target

**Problem.** In the same `Omega`, let `A` contain exactly `r` specified
outcomes, where `r` is a positive standard natural number. Find `P(A)` and
compare it with a singleton probability.

**Why this framework.** The ordinary shadow assigns zero to both events. The
algebraic answer retains the finite likelihood ratio between them.

**Solution.** Direct counting gives

\[
P(A)=\frac r\omega=r\epsilon,
\qquad \frac{P(A)}{P(\{j\})}=r.
\]

Thus `A` is exactly `r` times as probable as a specified singleton even though
both standard parts vanish.

**Ingredients and readiness.** Embedding standard naturals into `R*`, scalar
multiplication, monomial inversion, and standard part. **Now.**

## Exercise 3 — Union and overlap without collapsing to zero

**Problem.** Suppose finite events `A,B subset Omega` satisfy `#A = a`,
`#B = b`, and `#(A intersect B) = c`, with standard finite `a,b,c`. Compute
the probability of their union.

**Why this framework.** Taking standard parts first turns all four small-event
probabilities into zero, hiding the overlap correction. Algebra in `R*` keeps
ordinary inclusion-exclusion informative at infinitesimal scale.

**Solution.** Since `#(A union B) = a + b - c`,

\[
P(A\cup B)=(a+b-c)\epsilon
=P(A)+P(B)-P(A\cap B).
\]

For disjoint `A` and `B`, this becomes `(a+b)epsilon`.

**Ingredients and readiness.** Event cardinalities, addition and subtraction
in `R*`, and finite inclusion-exclusion. **Now** for the algebra; **Partial**
as a reusable theorem about encoded events.

## Exercise 4 — The dart: point versus segment

**Problem.** Discretize the unit square by an `omega` by `omega` uniform grid.
A specified point occupies one grid site. A horizontal segment of standard
length `L > 0` contains `L*omega` sites (choose a compatible hyperfinite grid).
Compute both probabilities and their ratio.

**Why this framework.** In the ordinary square both events have probability
zero, so their very different rarity orders become indistinguishable. The
algebraic grid explains the distinction by counting, without introducing a
separate set-valued foundation.

**Solution.** The square has `omega^2` sites, hence

\[
P(\text{point})=\epsilon^2,
\qquad
P(\text{segment})=L\epsilon,
\qquad
\frac{P(\text{segment})}{P(\text{point})}=L\omega.
\]

The ratio is positive infinite, so the segment is infinitely more probable
than the point.

**Ingredients and readiness.** Products of hyperfinite grids, powers of
`epsilon` and `omega`, monomial division, and order comparison by leading
exponent. **Now;** this is the counting interpretation of the existing dart
theorems.

## Exercise 5 — Coefficients cannot defeat a rarity order

**Problem.** On the same square, let `A` consist of `M = 10^100` specified
points and let `B` be one complete row, disjoint from `A`. Compare `P(A)` and
`P(B)`, and compute `P(A union B)`.

**Why this framework.** Both events again have ordinary shadow zero. Merely
saying that `A` has an enormous finite number of outcomes misses that one full
row belongs to a strictly larger infinitesimal order.

**Solution.** Counting yields

\[
P(A)=M\epsilon^2,
\qquad P(B)=\epsilon,
\qquad P(A\cup B)=\epsilon+M\epsilon^2.
\]

Moreover `P(B)/P(A) = omega/M`, which is infinite because `M` is standard.
Thus `P(A) < P(B)` regardless of the size of the standard coefficient `M`.

**Ingredients and readiness.** Multi-term addition, lexicographic order by
exponent, and comparison of `omega` with every standard number. **Now.**

## Exercise 6 — Near certainty with visible failure

**Problem.** From the one-dimensional `Omega`, choose uniformly after marking
`r` excluded outcomes. Find the probability `G` of choosing an allowed
outcome and the probability of failure.

**Why this framework.** The ordinary shadow reports `P(G)=1` and failure
probability zero. The algebraic value distinguishes certainty from an event
that can fail in exactly `r` exceptional ways.

**Solution.** There are `omega-r` allowed outcomes, so

\[
P(G)=\frac{\omega-r}{\omega}=1-r\epsilon<1,
\qquad P(G^c)=r\epsilon>0.
\]

The identity `P(G)+P(G^c)=1` holds exactly in `R*`.

**Ingredients and readiness.** Complements, subtraction, gauging, positivity,
and finite additivity. **Now.**

## Exercise 7 — Conditioning on a finite rare event

**Problem.** Let `C` consist of `k > 0` specified outcomes of the
one-dimensional `Omega`, and let `j in C`. Compute `P({j} given C)` using the
algebraic definition `P(A given B) = P(A intersect B)/P(B)`.

**Why this framework.** After taking ordinary shadows, numerator and
denominator are both zero and the elementary ratio is unavailable. The
infinitesimal factors cancel before any information is discarded.

**Solution.** Since `P({j}) = epsilon` and `P(C) = k*epsilon`,

\[
P(\{j\}\mid C)=\frac{\epsilon}{k\epsilon}=\frac1k.
\]

Rare-event conditioning recovers the expected uniform law on `C`.

**Ingredients and readiness.** Intersection, conditional probability as field
division, and cancellation of a nonzero monomial. **Now** because the present
inverse handles a single monomial denominator.

## Exercise 8 — Conditioning a point on a line

**Problem.** In the `omega` by `omega` square, let `R` be a specified complete
row and let `p` be one specified point on it. Find `P({p} given R)`.

**Why this framework.** The ordinary two-dimensional shadows of both `R` and
`{p}` are zero, so a direct real-valued quotient reads `0/0`. Algebraic
probability retains their codimension difference and cancels it correctly.

**Solution.** We have `P({p} intersect R)=epsilon^2` and `P(R)=epsilon`.
Therefore

\[
P(\{p\}\mid R)=\frac{\epsilon^2}{\epsilon}=\epsilon.
\]

Conditioning reduces the ambient grid dimension by one, exactly as counting
the `omega` sites in the row predicts.

**Ingredients and readiness.** Product grids, intersections, monomial
division, and exponent arithmetic. **Now.**

## Exercise 9 — Independence of coordinate events

**Problem.** Choose `(X,Y)` uniformly from the `omega` by `omega` grid. Let
`A = {X=x0}` and `B = {Y=y0}`. Verify independence algebraically.

**Why this framework.** Ordinary shadows turn `P(A)`, `P(B)`, and
`P(A intersect B)` into zero, so the equation `0 = 0*0` cannot explain the
finite-grid structure. The infinitesimal equality is nontrivial.

**Solution.** Each coordinate slice contains `omega` points and their
intersection contains one:

\[
P(A)=\epsilon,
\quad P(B)=\epsilon,
\quad P(A\cap B)=\epsilon^2
=P(A)P(B).
\]

Equivalently, `P(A given B)=epsilon=P(A)`.

**Ingredients and readiness.** Cartesian counts, multiplication, intersection,
and conditional probability. **Now** for the algebraic theorem; **Partial**
for a generic independence API.

## Exercise 10 — Dependence among equally rare events

**Problem.** Work on the toroidal `omega` by `omega` grid. Let
`D0 = {Y=X}` and `D1 = {Y=X+1}`, and put `A=D0`, `B=D0 union D1`. Are `A` and
`B` independent? Compute `P(A given B)`.

**Why this framework.** All of `A`, `B`, and their intersection have ordinary
shadow zero. Those shadows erase both the strong dependence and the exact
conditional probability.

**Solution.** The two diagonals are disjoint and each contains `omega` points:

\[
P(A)=\epsilon,
\quad P(B)=2\epsilon,
\quad P(A\cap B)=\epsilon.
\]

Since `epsilon != 2epsilon^2`, the product criterion fails. Also

\[
P(A\mid B)=\frac{\epsilon}{2\epsilon}=\frac12,
\]

whereas `P(A)=epsilon`.

**Ingredients and readiness.** Disjoint unions, products, monomial division,
and equality/order in `R*`. **Now.**

## Exercise 11 — Moments of a rare Bernoulli variable

**Problem.** Let `X` equal `1` with probability `q=c*epsilon` and `0`
otherwise, for a positive standard `c`. Compute `E[X]` and `Var(X)` exactly.

**Why this framework.** Replacing `q` by its ordinary shadow makes `X`
identically zero and deletes its first- and second-order behavior. Algebraic
moments retain both.

**Solution.** Since `X^2=X`,

\[
E[X]=c\epsilon,
\qquad
\operatorname{Var}(X)=E[X^2]-E[X]^2
=c\epsilon-c^2\epsilon^2.
\]

The leading variance order is `epsilon`, with a visible order-`epsilon^2`
correction.

**Ingredients and readiness.** A finite-valued random variable, finite sums,
products, and subtraction. **Now** as an explicit two-outcome calculation;
**Partial** as a generic expectation/variance library.

## Exercise 12 — An infinitesimal chance with finite expectation

**Problem.** A payoff `Y` equals `omega/c` when the rare event from Exercise 11
occurs and equals zero otherwise. Compute its expectation and variance.

**Why this framework.** Sending the event probability to zero before
multiplying by the infinite payoff gives an indeterminate or misleading
picture. The gauged algebra performs the cancellation exactly and also shows
that finite expectation need not imply finite variance.

**Solution.** Using `epsilon*omega=1`,

\[
E[Y]=(c\epsilon)\frac{\omega}{c}=1,
\]

while

\[
E[Y^2]=(c\epsilon)\frac{\omega^2}{c^2}=\frac{\omega}{c},
\qquad
\operatorname{Var}(Y)=\frac{\omega}{c}-1.
\]

Thus the mean is exactly finite and the variance is positive infinite.

**Ingredients and readiness.** Random-variable scaling, `epsilon*omega=1`,
negative exponents, and moment arithmetic. **Now** as a scalar calculation;
**Partial** for the random-variable definitions.

## Exercise 13 — Exact finite-resolution corrections to uniform moments

**Problem.** Let `J` be uniform on `{0,...,omega-1}` and set
`X=J/omega`. Compute `E[X]`, `E[X^2]`, and `Var(X)` without taking a limit.

**Why this framework.** The ordinary uniform law gives only `1/2` and `1/12`.
The algebraic result also records how the chosen grid convention approaches
those values.

**Solution.** Substitute the finite identities for `sum j` and `sum j^2`,
then simplify algebraically:

\[
E[X]=\frac{\omega-1}{2\omega}
=\frac12-\frac\epsilon2,
\]

\[
E[X^2]=\frac{(\omega-1)(2\omega-1)}{6\omega^2}
=\frac13-\frac\epsilon2+\frac{\epsilon^2}{6},
\]

\[
\operatorname{Var}(X)=\frac1{12}-\frac{\epsilon^2}{12}.
\]

Taking `st` recovers the familiar continuous answers only after the exact
corrections have been displayed.

**Ingredients and readiness.** Hyperfinite sums, polynomial sum identities,
substitution `omega=epsilon^-1`, and standard part. **Partial:** the final
`R*` expressions are available, but an index genuinely ranging to `omega`
is not present in the current Lean model.

## Exercise 14 — Collision statistic

**Problem.** Draw `n` independent labels uniformly from an `omega`-element
set, where `n` is standard and finite. Let `C` count equal unordered pairs.
Find `E[C]` and `Var(C)`.

**Why this framework.** A continuous classical shadow says that ties never
occur and makes both answers zero. The algebraic answer retains the leading
collision rate and its correction, which matters when comparing rare data
quality failures.

**Solution.** Write
`C = sum_(i<j) 1_{Xi=Xj}`. Each indicator has probability `epsilon` and
variance `epsilon(1-epsilon)`. Two distinct pair indicators have zero
covariance: for a shared index the triple-match probability is `epsilon^2`,
equal to the product, and disjoint pairs are independent. Hence

\[
E[C]={n\choose2}\epsilon,
\qquad
\operatorname{Var}(C)={n\choose2}\epsilon(1-\epsilon).
\]

**Ingredients and readiness.** Indicator variables, finite linearity of
expectation, covariance, and independent product counts. **Partial:** every
fixed `n` reduces to current arithmetic, but general finite sums and a random
variable API are missing.

## Exercise 15 — An estimator with infinitesimal contamination

**Problem.** Let `X1,...,Xn` be independent Bernoulli variables with
`P(Xi=1)=q=theta+a*epsilon`, where `0<theta<1`, `a` is standard, and `n` is
standard and positive. For the sample mean `T`, compute its expectation and
variance through order `epsilon^2`.

**Why this framework.** The ordinary shadow cannot distinguish contamination
`+a*epsilon` from none at all. Algebraic statistics retains its direction and
its effect on both bias and uncertainty.

**Solution.** Independence and Bernoulli arithmetic give

\[
E[T]=\theta+a\epsilon,
\]

and

\[
\operatorname{Var}(T)
=\frac{q(1-q)}n
=\frac{\theta(1-\theta)}n
 +\frac{a(1-2\theta)}n\epsilon
 -\frac{a^2}{n}\epsilon^2.
\]

Thus `st(E[T])=theta`, but the full expectation exposes the signed
infinitesimal bias `a*epsilon`.

**Ingredients and readiness.** Independent Bernoulli variables, finite sums,
expectation, variance scaling, and multi-term normalization. **Partial:** the
scalar identity is within the current algebra; the statistical abstractions
are not yet implemented.

## Exercise 16 — An infinitesimal likelihood comparison

**Problem.** A Bernoulli sample has `s` successes and `f` failures, both
standard finite. Compare the candidate parameters `q` and `q+epsilon`, where
`0<q<1`, by their exact likelihood ratio. Which candidate wins when the first
nonzero infinitesimal coefficient is of order `epsilon`?

**Why this framework.** Their real shadows are the same parameter `q`, so a
classical parameter representation declares an immediate tie. The algebraic
likelihood orders candidates that differ below ordinary resolution.

**Solution.** The exact ratio is

\[
R=\left(\frac{q+\epsilon}{q}\right)^s
  \left(\frac{1-q-\epsilon}{1-q}\right)^f.
\]

Its first correction is

\[
R=1+\left(\frac{s}{q}-\frac{f}{1-q}\right)\epsilon
  +\text{terms of order }\epsilon^2\text{ and smaller}.
\]

Therefore `q+epsilon` wins if the displayed score is positive and loses if it
is negative. If it vanishes, compare the next nonzero coefficient; at the
interior maximum `q=s/(s+f)`, moving by `+epsilon` decreases likelihood at
second order.

**Ingredients and readiness.** Finite natural powers, division by nonzero
standard values, normalization, and leading-term order. **Now** for each fixed
`s,f`; **Partial** for a reusable symbolic likelihood and coefficient API.

## Exercise 17 — Bayes conditioning when every observed route is rare

**Problem.** A condition `D` has probability `epsilon`. A test is always
positive under `D` and has false-positive probability `c*epsilon` under
`D^c`, for standard `c>0`. Compute `P(D given +)` exactly and find its
standard part.

**Why this framework.** If both prevalence and false-positive probability are
replaced by zero first, the elementary Bayes quotient loses their relative
scale. Keeping them algebraic produces a finite, informative posterior from
two rare routes to the observation.

**Solution.** We have

\[
P(D\cap +)=\epsilon
\]

and

\[
P(+)=\epsilon+(1-\epsilon)c\epsilon
=(1+c)\epsilon-c\epsilon^2.
\]

Thus

\[
P(D\mid +)=\frac{1}{1+c-c\epsilon},
\qquad
\operatorname{st}(P(D\mid +))=\frac1{1+c}.
\]

As a series, its first correction is
`1/(1+c) + c*epsilon/(1+c)^2 + ...`.

**Ingredients and readiness.** Bayes' rule as field division, complements,
mixed-order addition, inversion of `a+b*epsilon`, and standard part.
**Research:** the present finite Laurent-polynomial representation does not
have exact general inversion for a multi-term denominator. This exercise is a
direct specification for extending `R*` to a suitable series field or adding
a rigorously scoped leading-order inverse.

## Exercise 18 — An extreme exact test with `omega` trials

**Problem.** Under a fair Bernoulli null hypothesis, conduct `omega` trials
and observe success every time. Give the exact one-sided probability of an
outcome at least this extreme and compare it with `epsilon^k` for every
standard natural `k`.

**Why this framework.** The usual infinite-trial limit reports zero. An
algebraic extension should retain a strictly positive value and show that
exponential rarity is smaller than every fixed polynomial order of
`epsilon`.

**Solution.** Only the all-success sequence is at least as extreme, so

\[
p=2^{-\omega}>0.
\]

For every standard `k`, exponential growth eventually dominates the
polynomial `omega^k`; transferred to the hyperfinite index this gives

\[
2^{-\omega}<\omega^{-k}=\epsilon^k.
\]

Thus this exact significance value occupies a rarity class beyond all finite
powers currently represented by the basic examples.

**Ingredients and readiness.** Exponentiation at an infinite exponent,
positivity, comparison with all standard powers, and a transfer or equivalent
algebraic growth principle. **Research:** current `R*` supports finite formal
powers but not `2^omega` or this growth theorem.

## Exercise 19 — Poisson probabilities from one hyperfinite experiment

**Problem.** Perform `omega` independent Bernoulli trials with success
probability `lambda*epsilon`, where `lambda>0` is standard. For fixed standard
`k`, compute `P(K=k)` algebraically and identify its standard part.

**Why this framework.** Classical derivations introduce a sequence of
binomial experiments and then take a limit. The hyperfinite formulation puts
the large count and tiny probability into one experiment, with
`omega*epsilon=1`, and retains corrections beyond the limiting law.

**Solution.** Hyperfinite counting gives the exact expression

\[
P(K=k)={\omega\choose k}(\lambda\epsilon)^k
       (1-\lambda\epsilon)^{\omega-k}.
\]

For fixed `k`,

\[
{\omega\choose k}\epsilon^k\simeq\frac1{k!},
\qquad
(1-\lambda\epsilon)^\omega\simeq e^{-\lambda},
\]

where `simeq` means equality up to an infinitesimal. Therefore

\[
\operatorname{st}(P(K=k))=e^{-\lambda}\frac{\lambda^k}{k!}.
\]

Expanding both factors further would expose explicit corrections in powers of
`epsilon`.

**Ingredients and readiness.** Hyperfinite binomial coefficients, an
`omega`-fold product, exponential/logarithmic algebra, infinitesimal
closeness, and standard part. **Research:** this needs hyperfinite indexing and
transcendental functions compatible with `st`.

## Exercise 20 — Local asymptotic likelihood in one algebraic scale

**Problem.** Let `N=omega` Bernoulli observations have null parameter
`theta0 in (0,1)`. Compare the null with the local alternative
`theta1=theta0+h*sqrt(epsilon)`, where `h` is standard. Suppose the observed
success count satisfies

\[
S=N\theta_0+z\sqrt{N\theta_0(1-\theta_0)}
\]

for standard finite `z` and a compatible hyperfinite count `S`. Find the
standard part of the log-likelihood ratio of
`theta1` against `theta0`.

**Why this framework.** The two parameters have the same ordinary shadow, yet
`omega` observations accumulate their `sqrt(epsilon)` separation into finite
evidence. Classical local-asymptotic-normality proofs express this through a
limit of experiments; the algebraic version exposes the balancing scales in
one calculation.

**Solution.** Write `delta=h*sqrt(epsilon)` and expand

\[
\log R
=S\log\left(1+\frac\delta{\theta_0}\right)
 +(N-S)\log\left(1-\frac\delta{1-\theta_0}\right).
\]

The order-`sqrt(N)` terms cancel at the null center. Since
`N*delta^2=h^2`, the surviving finite terms give

\[
\operatorname{st}(\log R)
=\frac{hz}{\sqrt{\theta_0(1-\theta_0)}}
 -\frac{h^2}{2\theta_0(1-\theta_0)}.
\]

With `u=h/sqrt(theta0(1-theta0))`, this is `u*z-u^2/2`, the Gaussian local
likelihood form. A complete proof must also bound the discarded
infinitesimal remainder uniformly for finite `z`.

**Ingredients and readiness.** Rational powers such as `sqrt(epsilon)`,
hyperfinite products, logarithm and its controlled expansion, finite/random
decomposition of `S`, standard part, and a remainder theorem. **Research:**
this is a capstone specification for hyperfinite random sequences, analytic
functions on `R*`, and rigorous asymptotic control.

## Suggested framework development order

The exercises point to a practical implementation sequence: first introduce
events with hyperfinite cardinalities and prove the finite probability laws;
then add finite-valued random variables, finite sums, expectation, variance,
and independence; next make mixed-term division exact or explicitly
leading-order; finally add genuine hyperfinite indices, exponentials,
logarithms, and controlled standard-part theorems. Exercises 1–12 test the
algebraic core, 13–16 drive the statistics API, and 17–20 specify the larger
extensions without pretending that the current representation already proves
them.
