module HyperReals
import Base: sqrt

# Trying to make Stacktrace clickable in visual studio but it does not fucking work
Base.Filesystem.homedir() = "/Users/me"
cd(abspath("/Users/me/dev/script/julia/"))
ENV["JULIA_STACKTRACE_PATH"] = "absolute"


# todo infinite and infinitesimal are too similar words, consider renaming 
#  infinite:        •transfinite •divergent •omega •unbounded
#  infinitesimal:      •epsilon •micro •tiny •minis

const ∞ = Inf
# const ⧞ = -Inf
# const ⧞ = NaN # unknown unicode character HUH?



# const Float = Float32
const Float = Float64
# const Float = Real

# const Term = Tuple{Real, Real}
const Term = Tuple{Float, Float} # (coefficient, exponent/order) 
# e.g. Real has order 0, ε has order -1, ω has order 1

const Hyper = Vector{Term}
const RStar = Hyper

const ε = [(1.0, -1.0)]
const ω = [(1.0, 1.0)]
const 𝟘 = Term[]
const 𝟙 = [(1.0, 0.0)]

Base.one(::Type{Hyper}) = 𝟙
Base.zero(::Type{Hyper}) = 𝟘
Base.iszero(x::Hyper) = isempty(simplify(x))

Base.convert(::Type{Hyper}, x::Integer) = [(Float(x), 0.0)]
Base.convert(::Type{Hyper}, x::Real) = [(x, 0.0)]
Hyper(x::Real) = convert(Hyper, x)
hyper(x::Real) = Hyper(x)
Hyper(x::Vector{Tuple{R, R}}) where {R<:Real} = [(Float(r), Float(e)) for (r, e) in x]
# Hyper(x::Vector{Tuple{R, Float64}}) where {R<:Real} = [(Float64(r), e) for (r, e) in x]


function simplify(x::Hyper)::Hyper
    acc = Dict{Float, Float}()
    for (r, e) in x
        acc[e] = get(acc, e, 0.0) + r
    end
    return [(r, e) for (e, r) in acc if r ≠ 0.0]
end

simplify(x::Vector{Tuple{R, S}}) where {R<:Real, S<:Real} = simplify(Hyper(x))


Base.:+(x::Hyper, y::Hyper)::Hyper = simplify(vcat(x, y))
Base.:+(x::Hyper, y::Real) = x + convert(Hyper, y)
Base.:+(x::Real, y::Hyper) = convert(Hyper, x) + y
Base.:-(x::Hyper)::Hyper = [(-r, e) for (r, e) in x]
Base.:-(x::Hyper, y::Hyper)::Hyper = x + (-y)
Base.:-(x::Hyper, y::Real) = x - convert(Hyper, y)
Base.:-(x::Real, y::Hyper) = convert(Hyper, x) - y
Base.:*(x::Hyper, y::Hyper)::Hyper = simplify([(r1*r2, e1+e2) for (r1, e1) in x for (r2, e2) in y])
Base.:*(a::Real, x::Hyper)::Hyper = [(a * r, e) for (r, e) in x]
Base.:*(x::Hyper, a::Real) = [(r * a, e) for (r, e) in x]
Base.:/(x::Hyper, y::Hyper) = x * inv(y)
Base.:/(x::Hyper, y::Real) = x / convert(Hyper, y)
Base.:/(x::Real, y::Hyper) = convert(Hyper, x) / y
Base.inv(x::Hyper)::Hyper = [(1.0/r, -e) for (r, e) in x if r ≠ 0.0]
# Base.:^(x::Hyper, p::Real) = p == 0 ? 𝟙 : p == 1 ? x : simplify([(r^p, e*p) for (r, e) in x])
Base.:^(x::Hyper, p::Real) = p == 0 ? 1 : p == 1 ? x : simplify([(r^p, e*p) for (r, e) in x])
# Base.:^(x::Hyper, p::Integer) = p == 0 ? 𝟙 : p == 1 ? x : simplify([(r^p, e*p) for (r, e) in x])
Base.:*(x::Real, y::Hyper) = convert(Hyper, x) * y
Base.:*(x::Hyper, y::Real) = x * convert(Hyper, y)
# Base.:*(x::Hyper, a::Real) = [(r * a, e) for (r, e) in x]
Base.:*(a::Int, x::Hyper) = Float(a) * x
Base.:*(x::Hyper, a::Int) = x * Float(a)



function Base.show(io::IO, x::Hyper)
    terms = simplify(x)
    isempty(terms) && return print(io, "0")
    str = join(termstr.(terms), " + ")
    print(io, str)
end

termstr(t::Term) = begin
    c, e = t
    if e == 0.0
        string(c)
    elseif e == 1.0
        c == 1.0 ? "ω" : "$(c)ω"
    elseif e == -1.0
        c == 1.0 ? "ε" : "$(c)ε"
    elseif e > 1.0
        c == 1.0 ? "ω^$(Int(e))" : "$(c)ω^$(Int(e))"
    elseif e < -1.0
        c == 1.0 ? "ε^$(Int(-e))" : "$(c)ε^$(Int(-e))"
    else
        "0"
    end
end



# @assert 0.0 == 𝟘  FAILS
# import Base:≅

# ≅(x::Real, y::Hyper) = HyperReals.simplify(convert(Hyper, x)) == HyperReals.simplify(y)
# ≅(x::Hyper, y::Real) = y ≅ x
# ≅(x::Hyper, y::Hyper) = HyperReals.simplify(x) == HyperReals.simplify(y)

import Base: ≈

Base.:(==)(x::Hyper, y::Hyper) = isequal(simplify(x), simplify(y))

≈(x::Real, y::Hyper) = isequal(HyperReals.simplify([(x, 0.0)]) , HyperReals.simplify(y))
≈(x::Int, y::Hyper) = isequal(HyperReals.simplify([(Float(x), 0.0)]) , HyperReals.simplify(y))
≈(x::Hyper, y::Real) = isequal(HyperReals.simplify(x), HyperReals.simplify([(y, 0.0)]))
≈(x::Hyper, y::Hyper) = isequal(HyperReals.simplify(x), HyperReals.simplify(y))


# Absolute value: termwise |r|, preserve order
abs(x::Hyper)::Hyper = [(abs(r), e) for (r, e) in x]

# Helper: construct scalar multiple of ε or ω
εr(r::Real) = [(r, -1.0)]
ωr(r::Real) = [(r, 1.0)]

# Predicates

isreal(x::Hyper) = all(e == 0.0 for (_, e) in simplify(x))
isfinite(x::Hyper) = all(e ≤ 0.0 for (_, e) in simplify(x))
isinfinite(x::Hyper) = any(e > 0.0 for (_, e) in simplify(x))
isinfinitesimal(x::Hyper) = all(e < 0.0 for (_, e) in simplify(x)) # excluding 0 !?

isreal(x::Real) = true
isfinite(x::Real) = true
isinfinite(x::Real) = false 
isinfinitesimal(x::Real) = false # excluding 0 !?


# Optional: stricter variants (ε or ω only, no higher orders than -1 / 1)
isfinite1(x::Hyper) = begin r = standard(abs(x)); simplify(x) == [(r, 1.0)] end
isinfinitesimal1(x::Hyper) = begin r = standard(abs(x)); simplify(x) == [(r, -1.0)] end

# Proximity relations

near(x::Hyper, y::Hyper) = isinfinitesimal(x - y)
cofinite(x::Hyper, y::Hyper) = isfinite(x - y)

import Base: ~
~(x::Real, y::Real) = x==y
~(x::Hyper, y::Hyper) = near(x, y)
~(x::Hyper, y::Real) = near(x, Hyper(y))
~(x::Real, y::Hyper) = near(Hyper(x), y)

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

@assert 1~1
@assert 1.0~1
@assert 1+ε~1
@assert 1.0+2ε~1
@assert 1.0+3.0ε~1


# Monad and galaxy


struct Monad
    center::Hyper
end
Halo = Monad  # alias

# monad(x::Hyper) = Monad(x)
# in_monad(x::Hyper) = y -> near(x, y) # turns Hyper into predicate function!
# in_galaxy(x::Hyper) = y -> isfinite(x - y)
# in_halo = in_monad  # alias
# halo = monad  # alias
# monad(x::Real) = Monad(hyper(x))
# monad(x::Int) = Monad(Hyper(x))  # idiomatic and clean
# monad(x::Real) = Monad(Hyper(x))  # idiomatic and clean
# monad(x::Real) = Monad(convert(Hyper, x))

Base.:∈(y::Hyper, M::Monad) = near(M.center, y)
Base.:∈(x::Real, M::Monad) = Hyper(x) ∈ M

@assert !isinfinite(0)
@assert !isinfinite(0.0)
@assert !isinfinite(ε)
@assert !isfinite(ω)

# == equality only works if BOTH ARE Hyper! For mixed Hyper, Real use ≈
@assert 1/ε == ε^-1
@assert 1/ε == ω
@assert 1/ω == ω^-1
@assert 1/ω == ε

@assert isinfinite(ω)
@assert isinfinitesimal(ε)
@assert isfinite(ε)
@assert isfinite(0)
@assert isfinite(1)

@assert 0 ∈ Monad(0)
@assert ε ∈ Monad(0)
@assert 0 ∈ Monad(ε)
@assert ε ∈ Monad(ε)
# @assert @not 0.1 ∈ Monad(0)
@assert !(0.1 ∈ Monad(0))
@assert 0.1 ∉ Monad(0)
@assert 1.1 ∉ Monad(1)
@assert ε ∉ Monad(1)


# @assert 0 ∈ monad(0)
# @assert ε ∈ monad(0)
# @assert 0 ∈ monad(ε)
# @assert ε ∈ monad(ε)
# @assert not 0.1 ∈ monad(0)


# @assert 0.0 == 𝟘 "FAILS"
@assert 0 ≈ 𝟘  
@assert 0.0 ≈ 𝟘  
@assert [(0.0,0.0)] ≈ 𝟘  
# @assert [] ≈ 𝟘  
# @assert [(0,0)] ≈ 𝟘  
@assert 1 ≈ 𝟙
@assert 1.0 ≈ 𝟙
@assert [(1.0,0.0)] ≈ 𝟙
@assert 𝟙+𝟙-𝟙 == 𝟙
# @assert [(1,0)] ≈ 𝟙

# real part of a hyperreal EVEN IF contains ω≈∞
real(x::Hyper)::Real = sum((r for (r, e) in simplify(x) if e == 0.0), init=0.0)
# standard(x::Hyper)::Real = if isreal(x) real(x) else NaN end
standard(x::Hyper)::Real = if isfinite(x) real(x) else ∞ end
infinitesimal(x::Hyper)::Hyper = [(r, e) for (r, e) in simplify(x) if e < 0.0]


# aliases for standard part
const re = standard
const st = standard
const eps = infinitesimal

@assert standard(𝟘) == 0
@assert standard(𝟙) == 1
@assert standard(ω) == ∞
@assert standard(ε) == 0
@assert standard(𝟙+ε) == 1

@assert eps(ε) == ε


# x = ω
# x = 2ε
x = ω + 3.0 - 4.0 * ω + 2.0 * ε * ε + 1 - ε^2
println(x)
println(x*x)
println(real(x))
println(standard(x))

# sqrt(x::Hyper)::Hyper = [ (sqrt(r), e/2) for (r, e) in x if r > 0.0 ]
sqrt(x::Hyper)::Hyper = [ (sqrt(r), e/2) for (r, e) in x if r ≥ 0.0 ]

# @assert √(ε) == ε^(1/2)
@assert √(ε) == ε^.5
# @assert √(ε) == εr(1.0)
@assert st(√(2+ε)) == √2
@assert (√(0))^2 == 0
@assert ε^0 == 1
@assert ω^0 == 1
# @assert (√(2+ω))^2 == 2+ω # todo define x^y better


∫(x::Hyper) = [(r, e+1) for (r, e) in x]
∫(x::Real) = [(Float(x), 1.0)] # ∫1=ω
∂(x::Hyper) = [(r, e-1) for (r, e) in x]
∂(x::Real) = 0 # ∂1=0

@assert ∫(1) == ω # definition
@assert ∫(ε) ≈ 1 # can't use == because of julia limitations
@assert ∂(1) ≈ 0 # derivative of a constant
println(∂(ε)) # ε^2 !
@assert ∂(ε) ~ 0 # derivative of an infinitesimal
@assert ∂(ω) ≈ 1 # derivative of an infinite
@assert ∫(ω) == ω^2

∂(f::Function) = f'
∂(f::Function) = x -> f(x+ε) - f(x-ε) / (2*ε) # central difference
# ∂(f::Function) = x -> f(x+ε) - f(x) / (ε) # forward difference
# ∂(f::Function) = x -> f(x) - f(x-ε) / (ε) # backward difference

@assert ∂(sin)(x::Hyper) == cos(x)
@assert ∂(cos)(x::Hyper) == -sin(x)
@assert ∂(tan)(x::Hyper) == sec(x)^2
@assert ∂(exp)(x::Hyper) == exp(x) # derivative of exponential function
@assert ∂(log)(x::Hyper) == 1/x # derivative of logarithm function
# Exports
export Hyper, ε, ω, standard
export abs, isfinite, isinfinite, isinfinitesimal, near, cofinite, monad, galaxy, halo, ∂, ∫


end