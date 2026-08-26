# All *unconditionally-executed* @assert / @asserts checks from hyper.jl, split out
# here for readability. Included from inside `module HyperReals` (see the end of
# hyper.jl), so every non-exported helper (real, sign, isreal, dominant,
# taylor_series, ...) is in scope exactly as if these lines were still inline.
#
# NOT included: @assert lines inside hyper.jl's dead `if test_again`,
# `if test_symbolics`, and `if TERM_PRECISION == 12` blocks — those never ran in the
# original file either (the guarding flags are false / TERM_PRECISION is 60), so
# they were left untouched in place rather than hoisted out and accidentally
# turned live.
#
# Two lines were made self-contained: the originals referenced a local `x` that
# hyper.jl later reassigns (first to a second Hyper value, then to `id`); splicing
# every assertion in at one point means a bare `x` here would resolve to whatever
# `x` is by the end of the file, not what it was at the original call site.

@assert 1.0 + 0.0im == 1.0 - 0.0im

@assert (ω + 3.0 - 4.0 * ω + 2.0 * ε * ε + 1 - ε^2) == 4.0 + ε^2 + -3.0ω

@assert 0~0
@assert 0~0.0
@assert 0~ε
@assert 0~0
@assert 0.0~0
@assert ε~0
@assert 1~1
@assert 1~1.0
@assert 1~1+ε
@assert 1~1.0+2ε
@assert 1~1.0+3.0ε
@assert 1≈1
@assert 1≈1.0
@assert 1==1
@assert 1==1.0
@assert 1.0~1
@assert 1+ε~1
@assert 1.0+2ε~1
@assert 1.0+3.0ε~1
@assert 2 + ε ~ 2
@assert 2.0 + ε ~ 2.0

@assert !isinfinite(0)
@assert !isinfinite(0.0)
@assert !isinfinite(ε)
@assert !isfinite(ω)
@assert 1/ε == ω
@assert 1/ω == ε
@assert ε*ω == 𝟙
@assert +0.0im == -0.0im
@assert 1 + 0.0im == 1 - 0.0im
@assert 1 + 0.0im == 1 + -0.0im
@assert 1 / ε == ε ^ -1
@assert 1/ε ≈ ω
@assert ω ≈ ε^-1
@assert 1/ω == ω^-1
@assert 𝟙+𝟙-𝟙 == 𝟙
@assert 1+ε == ε+1
@assert 1+ω == ω+1
@assert ε*ε == 1/(ω*ω)
@assert isinfinite(ω)
@assert isinfinitesimal(ε)
@assert isfinite(ε)
@assert isfinite(0)
@assert isfinite(1)
@assert 0 ∈ Monad(0)
@assert ε ∈ Monad(0)
@assert 0 ∈ Monad(ε)
@assert ε ∈ Monad(ε)
@assert !(0.1 ∈ Monad(0))
@assert 0.1 ∉ Monad(0)
@assert 1.1 ∉ Monad(1)
@assert ε ∉ Monad(1)

@assert 0 ≈ 𝟘
@assert 0.0 ≈ 𝟘
@assert [(0,0)] ≈ 𝟘
@assert [(0.0,0.0)] ≈ 𝟘

@assert 1 ≈ 𝟙
@assert 1.0 ≈ 𝟙
@assert [(1.0,0.0)] ≈ 𝟙
@assert [(1,0)] ≈ 𝟙

@assert standard(𝟘) == 0
@assert standard(𝟙) == 1
@assert standard(ω) == ∞
@assert standard(ε) == 0
@assert standard(𝟙+ε) == 1

@assert real((ω + 3.0 - 4.0 * ω + 2.0 * ε * ε + 1 - ε^2)) == 4.0
@assert standard((ω + 3.0 - 4.0 * ω + 2.0 * ε * ε + 1 - ε^2)) == -∞

@assert √(ε) == ε^(1/2)
@assert √(ε) == ε^.5
@assert √(ε) ≈ ε^.5
@assert √(ε) ~ ε^.5
@assert √ε ~ ε^.5 # OK! good tokenizer

@assert least(√(ε + ω)) ~ 1

@assert √ω ~ ω^.5 # definition
@assert √ω ~ ω^(1/2) # same

@assert ω ~ ω+1 # ignore lower orders!
@assert 1 ~ 1+ε # ignore lower orders!
@assert 1/(1/(ω+1)) ~ ω+1 # precision inv would be too hard!
@assert 1/(1/(ε+1)) ~ ε+1
@assert (ω+1)*(1/(ω+1)) ~ 1
@assert (ω^2)*(1/(ω^2)) ~ 1
@assert (ω^2+1)*(1/(ω^2+1)) ~ 1
@asserts (ω^2 + ω + 1)*(1/(ω^2 + ω + 1)) ~ 1
@assert (ω^2 + ω + 1)*(1/(ω^2 + ω + 1)) ~ 1

@assert 0<ε
@assert ε<ω
@assert 1<ω
@assert ε<1
@assert 0>-ε
@assert ε>-ω
@assert 1>-ω
@assert ε>-1

@assert √(2+ε)*√(2+ε) ~ 2+ε
@assert (√(2+ε))^2 ~ 2+ε
@assert st(√(2+ε)) ≈ √2

@assert (√(0))^2 == 0
@assert ε^0 == 1
@assert ω^0 == 1

@assert((c+1)(1.0) == 2.0)
@assert((c*2)(2.0) == 4.0)
@assert((c-1)(1.0) == 0.0)  # new assertion for subtraction
@assert((c/2)(2.0) == 1.0)  # new assertion for division

@assert ∂(1) ≈ 0 # derivative of a constant
@assert ∂(ε) ~ 0 # derivative of an infinitesimal
@assert ∂(ω) ≈ 1 # derivative of an infinite

@assert ∂(id)(1.0) == 1
@assert ∂(x -> x)(1.0) == 1
@assert ∂(id) ≈ 1
@assert ∂(x -> x) ≈ 1
@assert ∂(id) ≈ x -> 1.0

@assert ∂(square)(1.0) ~ 2 + ε # not with central derivative!?
@assert ∂(square)(2.0) ~ 4 + ε
@assert ∂(square) ≈ x -> 2x

@assert dsquare(-2.0) ~ -4
@assert dsquare(-1.0) ~ -2
@assert dsquare(2.5) ~ 5
@assert dsquare(3.0) ~ 6
@assert dsquare(0.0) ~ 0 # OK IFF using central derivative
@assert dsquare(1.0) ~ 2
@assert dsquare(2.0) ~ 4

@assert ∂(square)(1.0) == 2  # oh wow why?
@assert ∂(square)(2.0) == 4  # oh wow why?
@assert ∂(square)(1.0) ~ 2 + ε  # no longer == because of exp approximation
@assert ∂(square)(2.0) ~ 4 + ε
@assert ∂(square)(1.0) ~ 2
@assert ∂(square)(2.0) ~ 4

@assert ∂(id) ≈ 1

@assert ∂(linear) ≈ 1.0
@assert ∂(linear) ≈ x -> 1.0

@assert sin(ϵ) ~ 0
@asserts sin(ϵ+π) ~ 0
@assert sin(ϵ+π) ~ 0
@assert sin(ϵ+π/2) ~ 1 # needs  NEAR_TOLERANCE = 1e-9 or higher precision
@assert sin(ϵ+π/4) ~ 0.7071067811865475
@assert sin(ϵ+π/3) ~ 0.8660254037844387 # added assertion for sin(ϵ + π/3)
@assert sin(ϵ+π/6) ~ 0.5
@assert sin(ϵ-π/2) ~ -1 # needs  NEAR_TOLERANCE = 1e-9 or higher precision
@assert sin(ϵ-π/4) ~ -0.7071067811865475
@assert sin(ϵ-π/3) ~ -0.8660254037844387 # added assertion for sin(ϵ + π/3)
@assert sin(ϵ-π/6) ~ -0.5
@assert ∂(sin)(0) ~ 1
@assert ∂(sin)(π/2) ~ 0
@asserts ∂(sin)(π) ~ -1
@assert ∂(sin)(π) ~ -1

@assert ∂(sin)(-π/2) ~ 0
@assert ∂(sin)(1.0) ~ cos(1.0)
@assert ∂(sin)(2.0) ~ cos(2.0)
@assert ∂(sin)(3.0) ~ cos(3.0)

@assert ∂(sin) isa Function || ∂(sin) isa Closure

@assert ∂(sin) ≈ cos
@assert ∂(exp) ≈ exp

@assert step(1) == 1
@assert step(-1) == 0
@assert step(0) == 0 || step(0) == 1 # depending on > / < or <=
@assert step(ε) == 1
@assert step(-ε) == 0
@assert ∂(step)(1) ≈ 0
@assert ∂(step)(-1) ≈ 0
@assert ∂(step)(2ε) ≈ 0
@assert ∂(step)(-2ε) ≈ 0
@assert ∂(step)(ε) ~ ω/2
@assert ∂(step)(-ε) ~ 0 # Todo WHY?
@assert ∂(step0)(ε) ~ 0 # in case of <=
@assert ∂(step0)(-ε) ~ ω/2 # Todo WHY?
@assert ∂(step) ≈ x -> x==0 ? ω/2 : 0
@assert ∂(step)(0) ~ ω/2 # NICE, Dirac! jump from 0 to 1
@assert ∂(sign)(0) ≈ ω # nice, FULL(double) dirac from -1 to 1

@assert st(δ(0)) == ∞
@assert ∂(step) ≈ δ # derivative of step function

@assert ∂(∂(step))(1) ≈ 0
@assert ∂(∂(step))(-1) ≈ 0
@assert ∂(∂(step0))(0) ≈  -ω²/4 # TODO: WHY negative for Heaviside 0⁻ ? FIX?!
@assert ∂(∂(step))(0) ≈  ω²/4
@assert ∂(∂(step))(0) ≈  ω*ω/2/2
@assert sign(1) == 1
@assert sign(-1) == -1
@assert sign(0) == 0
@assert sign(ϵ) == 1
@assert sign(-ϵ) == -1
@assert sign(ω) == 1
@assert sign(-ω) == -1
@assert ∂(sign)(1) ≈ 0
@assert ∂(sign)(-1) ≈ 0
@assert ∂(sign)(0) ≈ ω # nice, FULL Dirac!

@assert abs(2) == 2
@assert abs(1) == 1
@assert abs(1-ϵ) == 1-ϵ # keep signs of minor order(s)!
@assert abs(ϵ) == ϵ
@assert abs(0) == 0
@assert abs(-ϵ) == ϵ
@assert abs(-1) == 1
@assert abs(-2) == 2
@assert abs(-1-ϵ) == 1+ϵ # flip all signs!
@assert abs(-1+ϵ) == 1-ϵ # flip all signs!
@assert ∂(abs)(2) ≈ 1
@assert ∂(abs)(1) ≈ 1
@assert ∂(abs)(-1) ≈ -1
@assert ∂(abs)(-2) ≈ -1
@assert ∂(abs)(0) ≈ 0 # holup! information still there??
@assert ∂(abs)(ϵ) ~ 1 # strange encoding of “kink” but ok
@assert ∂(abs)(-ϵ) ~ -1 # strange encoding of “kink” but ok  Δ≈2 => ∂∂≈ẟ hopefully
@assert ∂(abs) ≈ sign # ignore the ϵ part
@assert ∂(∂(abs))(1) ≈ 0
@assert ∂(∂(abs))(-1) ≈ 0
@assert ∂(∂(abs))(0) ≈ ω # dirac! just like double-step ≈ sign function

@assert ∑(x -> ϵ) ≈ 1
@assert ∑(x -> 1) ≈ ω #cheap trick!
@assert ∑(x -> 1/(2^x)) ≈ 1

@assert ∫(1) == ω # definition
@assert ∫(ε) == 𝟙
@assert ∫(ε) ≈ 1
@assert ∫(ω) == ω^2 # definition
