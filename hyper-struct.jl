module HyperReals
import Base: sqrt
import Base: log
import Base: abs
import Base: round
import Base: ≈ # aka Base.isapprox 0.1 + 0.2 ≈ 0.3  # true 
# import Base:≅

const TERM_PRECISION = 40 # MAX_ORDER for calculations
# 20 -> √2=1.4142135623730954
# 12 -> √2=1.4142135623730951
const NEAR_TOLERANCE = 1e-10 # x ≈ 0 for near ~ relation USUALLY ONLY ε halo !!! Todo: use ≊ ⩰ ⸛ ⸞ ⸟ ?
const MAX_ORDER=6 # for display only
const CUTTOFF=1e-10 #!!
const ROUNDING_DIGITS=8 # only for display, not for calculations

setprecision(BigFloat, 256)  # ~77 decimal digits
log2_h = log(BigFloat(2))

# Trying to make Stacktrace clickable in visual studio but it does not fucking work
# Base.Filesystem.homedir() = "/Users/me"
# cd(abspath("/Users/me/dev/script/julia/"))
# ENV["JULIA_STACKTRACE_PATH"] = "absolute"


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


# const Hyper = Vector{Term} # NO WORKAROUND can turn this into a Number!
struct Hyper <: Number
    terms::Vector{Term}
end
Base.@pure Hyper <: Number # "no side effects", for compile‐time optimization
Base.promote_rule(::Type{Hyper}, ::Type{<:Number}) = Hyper #  whenever Hyper appears with another Number, the result type should be Hyper

const RStar = Hyper

const 𝟘 = Hyper([])
const 𝟙 = Hyper([(1.0, 0.0)])
const ω = Hyper([(1.0, 1.0)]) # better infinite ∞
const ε = Hyper([(1.0, -1.0)]) # infinitesimal 1/ω
const ε² = Hyper([(1.0, -2.0)])
const ε³ = Hyper([(1.0, -3.0)])
const ω² = Hyper([(1.0, 2.0)]) 
const ω³ = Hyper([(1.0, 3.0)])

Base.one(::Type{Hyper}) = 𝟙
Base.zero(::Type{Hyper}) = 𝟘
Base.iszero(x::Hyper) = isempty(simplify(x))

Base.convert(::Type{Hyper}, x::Hyper) = x
Base.convert(::Type{Hyper}, x::Number) = Hyper([(Float(x), 0.0)])
Base.convert(::Type{Hyper}, x::Vector{<:Tuple{<:Real, <:Real}}) = Hyper(x)


Hyper(x::Hyper) = x
hyper(x::Real) = Hyper(x)
Hyper(x::Real) = convert(Hyper, x)
Hyper(x::Vector{<:Tuple{<:Real, <:Real}}) = Hyper([(Float(r), Float(e)) for (r, e) in x])

function simplify(x::Hyper)::Hyper
    acc = Dict{Float, Float}()
    for (r, e) in x.terms
        acc[e] = get(acc, e, 0.0) + r
    end
    return Hyper([(r, e) for (e, r) in acc if r ≠ 0.0])
end

simplify(x::Vector{Tuple{R, S}}) where {R<:Real, S<:Real} = simplify(Hyper(x))
round(x::Hyper) = Hyper([(round(r; digits=ROUNDING_DIGITS), e) for (r, e) in x.terms if abs(r) > CUTTOFF])

Base.:+(x::Hyper, y::Hyper)::Hyper = simplify(vcat(x.terms, y.terms))
Base.:+(x::Hyper, y::Real) = x + convert(Hyper, y)
Base.:+(x::Real, y::Hyper) = convert(Hyper, x) + y
Base.:-(x::Hyper)::Hyper = [(-r, e) for (r, e) in x.terms]
Base.:-(x::Hyper, y::Hyper)::Hyper = x + (-y)
Base.:-(x::Hyper, y::Real) = x - convert(Hyper, y)
Base.:-(x::Real, y::Hyper) = convert(Hyper, x) - y
Base.:*(x::Hyper, y::Hyper)::Hyper = simplify([(r1*r2, e1+e2) for (r1, e1) in x.terms for (r2, e2) in y.terms])
Base.:*(a::Real, x::Hyper)::Hyper = [(a * r, e) for (r, e) in x.terms]
Base.:*(x::Hyper, a::Real) = [(r * a, e) for (r, e) in x.terms]
Base.:/(x::Hyper, y::Hyper) = x * inv(y)
Base.:/(x::Hyper, y::Real) = x / convert(Hyper, y)
Base.:/(x::Real, y::Hyper) = convert(Hyper, x) / y
Base.inv(x::Hyper)::Hyper = [(1.0/r, -e) for (r, e) in x.terms if r ≠ 0.0]
Base.:*(x::Real, y::Hyper) = convert(Hyper, x) * y
Base.:*(x::Hyper, a::Real) = x * convert(Hyper, a)
# Base.:*(x::Hyper, a::Real) = [(r * a, e) for (r, e) in x]
Base.:*(a::Int, x::Hyper) = Float(a) * x
Base.:*(x::Hyper, a::Int) = x * Float(a)

function ipow(x::Hyper, n::Integer)::Hyper
    n < 0  && return inv(ipow(x, -n))
    n == 0 && return Hyper([(1.0, 0.0)])  # 1
    n == 1 && return x
    if iseven(n)
        half = ipow(x, n ÷ 2)
        return half * half
    else
        return x * ipow(x, n - 1)
    end
end


Base.:^(x::Hyper, p::Integer) = p == 0 ? 𝟙 : p == 1 ? x : ipow(x, p) # recursive x * x * x
Base.:^(x::Hyper, p::Real) = simplify(exp(p * log(x)))

const LOG2_H = Hyper([(log2_h, 0.0)])  # approximate ln(2)
# log(ω^n) = n*ω ?
# log(ε) = -ω = -1/ε can't be ?
function log(u::Hyper; terms=TERM_PRECISION)
    stv = standard(u)
    if stv < 0.0
        throw(DomainError(u, "log of negative hyperreal"))
    elseif stv == 0.0 # handle positive infinitesimals 
        if u == ε
            return -ω
        end
        print("u=", u, " stv=", stv)
        return -ω
    #     # The approach is naive: if u = c * ε^k, log(u) ≈ log(c) + k*(log(ε)),
    #     # We'll identify the leading (smallest) exponent among terms:
    #     e_min = minimum(t[2] for t in u.terms)
    #     c_sum = sum(t[1] for t in u.terms if t[2] == e_min)
    #     if c_sum <= 0.0
    #         throw(DomainError(u, "log of non-positive hyperreal"))
    #     end
    #     realpart = log(c_sum)
    #     return realpart - ω * e_min # log(ε) = -ω !
    #     # return Hyper([(realpart, 0.0), (1.0, e_min * 100)]) # ω^100 hack
    end
    # If stv > 0, do the usual argument reduction.
    n = 0
    v = u
    while standard(v) > 1.5
        v = v / 2
        n += 1
    end
    while standard(v) < 0.666
        v = v * 2
        n -= 1
    end
    # Now v is near 1, do naive log expansion.
    z = v - 𝟙
    s = 𝟘
    t = z
    sign = 1.0
    # Taylor series expansion for log(1+z) 
    # log(1+z) = ∑±zⁿ/n = z - z²/2 + z³/3 - z⁴/4 + ...
    # 1-log(1+z)  = 1 - z + z²/2 - z³/3 + z⁴/4 + ... ≠ Ein(z)  entire exponential integral   shifted like Riemann ?
    for k in 1:terms
        s += (sign * t) / k
        t *= z
        sign = -sign
    end
    # Combine adjustments for factors of 2:
    return Hyper([(Float(n), 0.0)]) * LOG2_H + s
end

# exp(h::Hyper) =  ∑(0,∞) hⁿ/n! 
function exp(h::Hyper; terms=TERM_PRECISION)
    sum = 𝟙
    t = 𝟙 # term cumulating hⁿ and n!
    for n in 1:terms
        t = (t * h) / n
        sum = sum + t
    end
    return sum
end


function common(x::Hyper)::Hyper
    return Hyper([(r,e) for (r,e) in simplify(x).terms if abs(e) < MAX_ORDER && abs(r) > CUTTOFF])
end

function Base.show(io::IO, x::Hyper)
    # terms = simplify(x).terms
    # terms = simplify(round(x)).terms # rounding but keep high 
    terms = common(x).terms
    isempty(terms) && return print(io, "0")
    str = join(termstr.(terms), " + ")
    print(io, str)
end

termstr(t::Term) = begin
    c, e = t
    c=round(c; digits=ROUNDING_DIGITS) # coefficient
    e=round(e; digits=ROUNDING_DIGITS) # exponent
    c = (c == floor(c)) ? string(Int(c)) : string(c) # 1.0 => 1
    e1 = (e == floor(e)) ? string(Int(e)) : string(e ) # 1.0 => 1
    if e == 0.0 
        c
    elseif e == 1.0
        c == "1" ? "ω" : "$(c)ω"
    elseif e == -1.0
        c == "1" ? "ε" : "$(c)ε"
    elseif e == 2.0
        c == "1" ? "ω²" : "$(c)ω²"
    elseif e == -2.0
        c == "1" ? "ε²" : "$(c)ε²"
    elseif e > 2.0
        c == "1" ? "ω^$(e1)" : "$(c)ω^$(e1)"
    elseif e < -1.0
        c == "1" ? "ε^$(e1)" : "$(c)ε^$(e1)"
    else
        "0"
    end
end

Base.:(==)(x::Hyper, y::Hyper) = isequal(simplify(x).terms, simplify(y).terms)

x = ω + 3.0 - 4.0 * ω + 2.0 * ε * ε + 1 - ε^2
# println(x)
@assert x == 4.0 + ε^2 + -3.0ω

# @assert 0.0 == 𝟘  FAILS

# ≅(x::Real, y::Hyper) = simplify(convert(Hyper, x)) == simplify(y)
# ≅(x::Hyper, y::Real) = y ≅ x
# ≅(x::Hyper, y::Hyper) = simplify(x) == simplify(y)


# ⸟(x::Hyper, y::Hyper) unknown unicode character '⸟'
# ⸞(x::Hyper, y::Hyper) unknown unicode character '⸞'

≡(x::Hyper, y::Hyper) = x==y # \\equiv ≡ ≢ ≡⃥ 
≣(x::Hyper, y::Hyper) = x==y # \\Equiv ≣
⩮( x::Hyper, y::Hyper) = x==y # \\eqcirc ≈ near!?
⩶( x::Hyper, y::Hyper) = x==y # \\eqeqeq ≈
⩰(x::Hyper, y::Hyper) = round(x)==round(y)
≅(x::Hyper, y::Hyper) = round(x)==round(y) # \\cong  congruent
≊(x::Hyper, y::Hyper) = round(x)==round(y) # \\approxeq
≌(x::Hyper, y::Hyper) = x≈y # \\allequal ALL EQUAL TO Unicode: U+224C, UTF-8: E2 89 8C
⩯(x::Hyper, y::Hyper) = x≈y # \\hatapprox
≋(x::Hyper, y::Hyper) = x≈y # TRIPLE TILDE Unicode: U+224B, UTF-8: E2 89 8B
⩭(x::Hyper, y::Hyper) = x≈y # \\congdot overkill! ⩸ ⇌
≍(x::Hyper, y::Hyper) = x≈y # \\asymp asymptotic EQUIVALENCE  ω≍ω+1
≃(x::Hyper, y::Hyper) = near(x,y) # \\simeq similar ASYMPTOTICALLY EQUAL TO Unicode: U+2243, UTF-8: E2 89 83
≙(x::Hyper, y::Hyper) = near(x,y) # ESTIMATES	≙ \\wedgeq and-equal
≚(x::Hyper, y::Hyper) = near(x,y)  # EQUIANGULAR TO	≚ \\veeeq or-equal
# ≠(x::Hyper, y::Hyper) = x!=y # per default
# see https://github.com/ojsheikh/unicode-latex/blob/master/src/latex.ts

# ⚠️ we can't use == for mixed Hyper, Real THAT's why we define ≈ !!
# todo better use ≅ instead of ≈ ! but we can't type it THAT's why we use ≈
# ≅ Use LaTeX tab completion: Type ≅ and press TAB
# ⚠️ use ≈ only if you expect IDENTITY! h == h'   
# ⚠️ use ~ to check PROXIMITY ε ~ 0 but not identity! 
# ⚠️ use ≈ for approximation
# ≈(x::Hyper, y::Hyper) = isequal(simplify(x).terms, simplify(y).terms)
≈(x::Hyper, y::Hyper) = x == y #
≈(x::Real, y::Hyper) = Hyper(x) ≈ y
≈(x::Int, y::Hyper) = Hyper(x) ≈ y
≈(x::Hyper, y::Real) = x ≈ Hyper(y)
≈(x::Vector{<:Tuple{<:Real, <:Real}}, y::Hyper) = Hyper(x) ≈ y
≈(x::Hyper,y::Vector{<:Tuple{<:Real, <:Real}}) = x ≈ Hyper(y)
# ≈(x::Hyper, y::Hyper) = isequal(simplify(x).terms, simplify(y).terms)
# ≈(x::Vector{<:Tuple{<:Real, <:Real}}, y::Hyper) = isequal(simplify(x), simplify(y))
# ≈(x::Vector{Tuple{Float64, Float64}}, y::Hyper) = isapprox(Hyper(x), y)
# ≈(x::Hyper, y::Vector{Tuple{Float64, Float64}}) = isapprox(x, Hyper(y))

# Absolute value: termwise |r|, preserve order
abs(x::Hyper)::Hyper = [(abs(r), e) for (r, e) in x.terms]

# Helper: construct scalar multiple of ε or ω ??
# εr(r::Real) = [(r, -1.0)]
# ωr(r::Real) = [(r, 1.0)]

# Predicates

isreal(x::Hyper) = all(e == 0.0 for (_, e) in simplify(x).terms)
isfinite(x::Hyper) = all(e ≤ 0.0 for (_, e) in simplify(x).terms)
isinfinite(x::Hyper) = any(e > 0.0 for (_, e) in simplify(x).terms)
isinfinitesimal(x::Hyper) = all(e < 0.0 for (_, e) in simplify(x).terms) # excluding 0 !?
# isinfinitesimal(x::Hyper) = all(e < 0.0 || (e == 0.0 && abs(r)<NEAR_TOLERANCE) for (r, e) in simplify(x).terms) # with ≈ 0

isreal(x::Real) = true
isfinite(x::Real) = true
isinfinite(x::Real) = false 
isinfinitesimal(x::Real) = false # excluding 0 !?


# Optional: stricter variants (ε or ω only, no higher orders than -1 / 1)
isfinite1(x::Hyper) = begin r = standard(abs(x)); simplify(x).terms == [(r, 1.0)] end
isinfinitesimal1(x::Hyper) = begin r = standard(abs(x)); simplify(x).terms == [(r, -1.0)] end

# Proximity relations

near(x::Hyper, y::Hyper) = isinfinitesimal(x - y)
near(x::Vector{Tuple{Float64, Float64}}, y::Hyper) = near(Hyper(x), y)
near(x::Hyper, y::Vector{Tuple{Float64, Float64}}) = near(x, Hyper(y))

cofinite(x::Hyper, y::Hyper) = isfinite(x - y)

~(x::Real, y::Real) = x==y
~(x::Hyper, y::Hyper) = near(x, y)
# ~(x::Hyper, y::Real) = near(x, Hyper(y))
# ~(x::Hyper, y::Real) = near(x, Hyper(y))
~(x::Real, y::Hyper) = near(Hyper(x), y)
~(x::Int, y::Hyper) = near(Hyper(x), y)
# ~(x::Real, y::Hyper) = near(Hyper(x), y)
~(x::Number, y::Number) = near(Hyper(x), Hyper(y))

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
@assert ε*ω == 𝟙
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


# @assert 0.0 == 𝟘 "FAILS because can't overload 'highjack' == for float. USE ≈"
@assert 0 ≈ 𝟘  
@assert 0.0 ≈ 𝟘  
@assert [(0,0)] ≈ 𝟘  
@assert [(0.0,0.0)] ≈ 𝟘  
# @assert [] ≈ 𝟘  
# @assert 𝟘 ≈ []  

@assert 1 ≈ 𝟙
@assert 1.0 ≈ 𝟙
@assert [(1.0,0.0)] ≈ 𝟙
@assert [(1,0)] ≈ 𝟙

# PART functions
# real part of a hyperreal EVEN IF contains ω≈∞
real(x::Hyper)::Real = sum((r for (r, e) in simplify(x).terms if e == 0.0), init=0.0)
standard(x::Hyper)::Real = isfinite(x) ? real(x) : sign(leading(x)[1])*∞
infinitesimal(x::Hyper)::Hyper = [(r, e) for (r, e) in simplify(x).terms if e < 0.0]
infinite(x::Hyper)::Hyper = [(r, e) for (r, e) in simplify(x).terms if e > 0.0]
finite(x::Hyper)::Hyper = [(r, e) for (r, e) in simplify(x).terms if e <= .0]

# aliases 
const re = real
const st = standard
const eps = infinitesimal
const epsilon = infinitesimal
const omega = infinite

# •(x::Hyper) = standard(x) # unknown unicode character '•'
# ·(x::Hyper) = standard(x) # NOT indicative for real or standard part!
# @assert ·(𝟙) == 1  # type · via alt+shift+9

leading(x::Hyper) = begin
    terms = simplify(x).terms
    isempty(terms) && return (0.0, 0.0)
    order, index = findmax(x -> x[2], terms) # x[2] is the exponent, [2] is index
    return terms[index]
end

Base.getproperty(x::Hyper, sym::Symbol) = begin
    hyper_synonyms = Dict(
        :real => [:re, :º, :r],
        :standard => [:st, :s],
        :epsilon => [:e, :ep, :eps, :infinitesimal, :low, :small],
        :omega => [:o, :om, :high, :big, :infinite],
        :finite => [:f, :finitepart],
    )
    synonym_lookup = Dict{Symbol,Symbol}()
    for stdname in keys(hyper_synonyms), alias in hyper_synonyms[stdname]
        synonym_lookup[alias] = stdname
    end
    stdsym = haskey(synonym_lookup, sym) ? synonym_lookup[sym] : sym
    # if stdsym != sym
    #     @warn "Accessing property `$(sym)` via synonym for `$(stdsym)`."
    # end
    if stdsym === :real
        return real(x)
    elseif stdsym === :standard
        return standard(x)
    elseif stdsym === :epsilon
        return infinitesimal(x)
    elseif stdsym === :omega
        return infinite(x)
    elseif stdsym === :finite
        return finite(x)
    else
        return getfield(x, sym)
    end
end

@assert 𝟙.re == 1
@assert 𝟙.º == 1  # type º via alt+0

y = 4 + ε² + -3ω
println(leading(y)) # should be [(-3.0, 1.0)]
@assert y.re == 4
@assert leading(y) == (-3.0, 1.0) # leading term -3ω with highest order 1
@assert y.st == -∞

@assert y.eps == ε²
@assert y.epsilon == ε²
@assert y.infinitesimal == ε²
@assert y.low == ε²
@assert y.high == -3ω
@assert y.small == ε²
@assert y.big == -3ω
@assert y.omega == -3ω
@assert y.infinite == -3ω
@assert y.finite == 4 + ε²


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
println(real(x)) # 4.0 just the real part
println(standard(x)) # Inf ∞ because of ω
println(x*x)

# sqrt(x::Hyper)::Hyper = [ (sqrt(r), e/2) for (r, e) in x if r > 0.0 ]
# sqrt(x::Hyper)::Hyper = [(sqrt(r), e/2) for (r, e) in x.terms if r ≥ 0.0]
sqrt(x::Hyper)::Hyper = x^.5


# @assert √(ε) == ε^(1/2)
@assert √(ε) == ε^.5 
@assert √(ε) ≈ ε^.5
@assert √(ε) ~ ε^.5

# @assert √(ε) == εr(1.0)
println(st(√(2+ε))) 
@assert st(√(2+ε)) ≈ √2
# @assert st(√(2+ε)) ~ √2
# @assert st(√(2+ε)) == √2 # only for precision 12, NOT HIGHER WHY??
@assert (√(0))^2 == 0
@assert ε^0 == 1
@assert ω^0 == 1
# @assert (√(2+ω))^2 == 2+ω # todo define x^y better

# Riemann sum/integral
# ∑(x::Hyper, f::Function) = sum(f(x))

# ∂(f::Function) = f'
# ∂(f::Function) = x -> f(x) - f(x-ε) / (ε) # backward difference
# ∂(f::Function) = x -> f(x+ε) - f(x-ε) / (2*ε) # central difference
∂(f::Function) = x -> simplify( (f(x+ε) - f(x)) / ε )

(h::Hyper)(x) = h  # treats Hyper as constant function, but no automatic cast to Hyper / Function :

# should follow from definitions of ∫ and ∂ if we treat number h as constant function h(x)=h
∂(x::Hyper) = Hyper([(r, e-1) for (r, e) in x.terms])
∂(x::Real) = 𝟘 # ∂1=0  

# todo: check f≈g on more sample points (or use a better test;)
≈(f::Function, y::Number) = all(f(x) ≈ y for x in (-1.0, 0.0, 1.0)) # lol
≈(f::Function, y::Hyper) = all(f(x) ~ y for x in (-1.0, 0.0, 1.0)) # lol
≈(h::Hyper, f::Function) = all(h ~ f(x) for x in (-1.0, 0.0, 1.0)) # lol
≈(f::Function, g::Function) = f==g || all(f(x) ~ g(x) for x in (-1.0, 0.0, 1.0)) # lol
# ≈(f::Function, g::Function) = f==g || all(f(x) ≈ g(x) for x in (-1.0, 0.0, 1.0)) # lol

@assert ∂(1) ≈ 0 # derivative of a constant
println(∂(ε)) # ε^2 !
@assert ∂(ε) ~ 0 # derivative of an infinitesimal
@assert ∂(ω) ≈ 1 # derivative of an infinite


id(x) = x
@assert ∂(id)(1.0) == 1
@assert ∂(x -> x)(1.0) == 1
@assert ∂(id) ≈ 1
@assert ∂(x -> x) ≈ 1
@assert ∂(id) ≈ x -> 1.0

square(x) = x * x  # uses Hyper * Hyper, which does include cross terms
# square(x) = x^2 # uses recursive x * x so the same
# square(x) = x^2.0 # uses exponential function via exp and log approximations!


# println("∂(square)(1.0) is ",∂(square)(1.0)) # derivative of x^2 at x=2
# println("∂(square)(2.0) is ",∂(square)(2.0)) # derivative of x^2 at x=2 == 4
@assert ∂(square)(1.0) == 2 + ε 
@assert ∂(square)(2.0) == 4 + ε
@assert ∂(square) ≈ x -> 2x
# @assert ∂(square) ≈ 2*id

square(x) = x^2.0 # uses exponential function via exp and log approximations!
dsquare(x)=st(∂(square)(x)) 

# using Plots
# plot(square, -5, 5, label="x²")
# plot!(dsquare, -5, 5, label="∂x²/∂x", linestyle=:dash)

# gui()  # hält Fenster offen
# readline()  # blockiert bis Enter gedrückt wird


# println("∂(square)(1.0) is ",∂(square)(1.0)) # 100 terms lol
# println("∂(square)(2.0) is ",∂(square)(2.0)) # 
println("∂(square)(1.0) is ", common(∂(square)(1.0))) # derivative of x^2 at x=2
println("∂(square)(2.0) is ", common(∂(square)(2.0))) # derivative of x^2 at x=2 == 4
@assert ∂(square)(1.0) ~ 2 + ε  # no longer == because of exp approximation
@assert ∂(square)(2.0) ~ 4 + ε

@assert ∂(square)(1.0) ~ 2
@assert ∂(square)(2.0) ~ 4
@assert ∂(square) ≈ x -> 2.0
@assert ∂(square) ≈ 2x
@assert ∂(square)(x::Hyper) == 2x



x = id # only temporary! we had variable x = ω +1  before lol
println(∂(x)) # derivative of x ??
@assert ∂(x) ≈ 1

linear(x::Hyper) = x
linear(x::Number) = x
@assert ∂(linear) ≈ 1.0
@assert ∂(linear) ≈ x -> 1.0

println(∂(sin)) # derivative of sin
@assert ∂(sin) ≈ cos
# @assert ∂(sin) == cos
@assert ∂(sin)(x::Hyper) == cos(x)
@assert ∂(cos)(x::Hyper) == -sin(x)
@assert ∂(tan)(x::Hyper) == sec(x)^2
@assert ∂(exp)(x::Hyper) == exp(x) # derivative of exponential function
@assert ∂(log)(x::Hyper) == 1/x # derivative of logarithm function


# ∫(f::Function) = x -> f(x) * ε  # dot integral 
# ∫(f::Function) = x -> ∑(i in xω) f(x+i) * ε
# ∫(f::Function) = x -> ∑(xω,f,x) * ε
# ∫(f::Function) = x -> ∑(i in -ωx:xω) f(x+i) * ε

# @assert ∫x ≈ x²/2

# follows from definitions of ∫ and ∂ if we treat number h as constant function h(x)=h
∫(x::Hyper) = Hyper([(r, e+1) for (r, e) in x.terms])
∫(x::Real) = Hyper([(Float(x), 1.0)]) # ∫1=ω

#  if we treat ε as constant function ε(x)=ε
@assert ∫(1) == ω # definition
println(∫(ε)) # 1.0 OK
@assert 1.0 ≈ 1
@assert ∫(ε) == 𝟙
@assert ∫(ε) ≈ 1 # FAIL !?
# @assert ∫(ε) == 1 # can't use == because of julia limitations
@assert ∫(ω) == ω^2


# Exports
export Hyper, ε, ω, standard
export abs, isfinite, isinfinite, isinfinitesimal, near, cofinite, monad, galaxy, halo, ∂, ∫


end