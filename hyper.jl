# make sure julia extension is installed and enabled

# # julia12 --output-o test.o --sysimage sysimage.so --startup-file=no test.jl
# New --trace-compile-timing option to report how long each method reported by --trace-compile took to compile, in ms (#54662).

module HyperReals
import Base: sqrt
import Base: log
import Base: abs
import Base: exp
import Base: round
import Base: ≈ # aka Base.isapprox 0.1 + 0.2 ≈ 0.3  # true 
import Base: <
import Base: isless

const TERM_PRECISION = 60 #30 # 12 # 40 # MAX_ORDER for calculations MAX 64 because 2^x
const TAYLOR_TERMS = 5 # 10 TODO WHY SO SLOOOW?
const ROUNDING_DIGITS=8 # only for display, not for calculations SYNC WITH:
# todo, set HIGHER yet get sin(ϵ + π) ~ 0
# const 
NEAR_TOLERANCE = 1e-6 # x ≈ 0 ~ 0 for Todo: near relation / ε halo use ≊ ⩰ ⸛ ⸞ ⸟ ?
# atol = NEAR_TOLERANCE # absolute tolerance for comparisons
const CUTOFF=1e-10 #! for display
const CALC_CUTOFF=1e-20 #! for simplification (why? to reduce calculations?)

const MAX_ORDER=10 # for display only
const MIN_ORDER=-10 # for display AND calculations  TODO sure?
# const ROUNDING_DIGITS=12 # only for display, not for calculations

# ⚠️ we use ~ for permissive approximation ε~0 0~1e-10 ( rounded numbers! ) 
# we use ≈ either for ~ or ==  TODO! ;)
# for strict near-ness in halo use ⩭ on demand , for equality use == or ≡, for strict equivalence ⩶

# setprecision(BigFloat, 256)  # ~77 decimal digits  TODO reuse for us?
# log2_h = log(BigFloat(2))
log2_h = log(Float64(2))

# todo infinite and infinitesimal are too similar words, consider renaming 
#  infinite:        •transfinite •divergent •omega •unbounded
#  infinitesimal:      •epsilon •micro •tiny •minis •ε

setprecision(BigFloat, 256)
# const π² = π^2
const π² = big(π)^2 # needed for ∑ !
const ∞ = Inf
# const ⧞ = NaN # unknown unicode character HUH?

# const Field = Float32
# const Field = Float64
# const Field = Complex
const Field = ComplexF64 
# const Field = Real

const Term = Tuple{Field, Float32} # (coefficient, exponent/order) 
# e.g. any real number has order 0, ε has order -1, ω has order 1
const Terms = Vector{Term}

struct Hyper <: Number
    terms::Vector{Term}
end
# const Hyper = Vector{Term} # NO WORKAROUND can turn this into a Number!
Base.@pure Hyper <: Number # "no side effects", for compile‐time optimization
Base.promote_rule(::Type{Hyper}, ::Type{<:Number}) = Hyper #  whenever Hyper appears with another Number, the result type should be Hyper
Base.promote_rule(::Type{Hyper}, ::Type{<:Real}) = Hyper

# AVOID TO define Hyper as method, as it may cause hard to debug MethodError: UndefVarError: `methodswith`
(h::Hyper)(x) = h  # treats Hyper as constant function, but no automatic cast to Hyper / Function 
Base.Broadcast.broadcastable(::Hyper) = Ref(x)


const RStar = Hyper

const 𝟘 = Hyper([])
const 𝟙 = Hyper([(1.0, 0.0)])
const zero = 𝟘
const one = 𝟙
const ω = Hyper([(1.0, 1.0)]) # better infinite ∞
const ε = Hyper([(1.0, -1.0)]) # infinitesimal 1/ω    \\upepsilon 'upright' U+03B5 ε GREEK SMALL LETTER
const ɛ = ε  # \\varepsilon WTF UNICODE / font curly variant ɛ == e in FF lol 
const ϵ = ε  # \\epsilon ϵ ≠ ∊ ∈ element
# const 𝓔 = ε # \\mathscr{E}  \\mathcal{E}
const ε² = Hyper([(1.0, -2.0)])
const ε³ = Hyper([(1.0, -3.0)])
const ω² = Hyper([(1.0, 2.0)]) 
const ω³ = Hyper([(1.0, 3.0)])

Base.one(::Type{Hyper}) = 𝟙 # \\Bbbone big bold one
Base.zero(::Type{Hyper}) = 𝟘 # \\Bbbzero big bold zero
Base.iszero(x::Hyper) = isempty(simplify(x))

Base.convert(::Type{Hyper}, x::Hyper) = x
Base.convert(::Type{Hyper}, x::Number) = Hyper([(Field(x), 0.0)])
Base.convert(::Type{Hyper}, x::Real) = Hyper([(Field(x), 0.0)])
# Base.convert(::Type{Hyper}, x::Vector{<:Tuple{<:Real, <:Real}}) = Hyper(x)
Base.convert(::Type{Hyper}, x::Vector{<:Tuple{<:Field, <:Float32}}) = Hyper(x)
Base.convert(::Type{Hyper}, x::Terms) = Hyper(x) # same ^^

Base.size(h::Hyper) = size(h.terms)
# Base.getindex(h::Hyper, i::Int) = h.terms[i] # only make sense if sorted?
# Base.setindex!(h::Hyper, val::Term, i::Int) = (h.terms[i] = val) # Todo: find order or add order
# Base.setindex!(h::Hyper, val, i::Int) = (h.terms[i] = Term(val))
Base.iterate(h::Hyper, s...) = iterate(h.terms, s...)

a=𝟘
for i in a println(i) end
# for i in 1:10 a[i] = (i, i) end # Todo: find order or add order
# exit()

Hyper(x::Hyper) = x
Hyper(x::Real) = convert(Hyper,x)
Hyper(x::Field) = convert(Hyper,x)
# Hyper(x::Vector{<:Tuple{<:Field, <:Float32}}) = Hyper([(r, e) for (r, e) in x])
# Hyper(x::Vector{<:Tuple{<:Real, <:Real}}) = Hyper([(Field(r), Field(e)) for (r, e) in x])

function sort1(x::Hyper)::Hyper
    if length(x.terms) <= 1 return x end
    sorted = sort(x.terms; by = t -> t[2], rev = true)
    return Hyper(sorted)
end

function order(x::Hyper)::Hyper
    return sort1(simplify(x))
end

# function simplify(x::Vector{Any})::Hyper
#     throw(MethodError(simplify, (x,)))
# end

# function simplify(x::Vector{Any})::Hyper
#     if length(x) == 0
#         return zero
#     elseif length(x) == 1
#         return Hyper([Field(x[1], 0.0)])
#     elseif length(x) == 2
#         throw(MethodError(simplify, (x,)))
#     end
# #         return zero
# #     # return Hyper([])
# #     # return Hyper([(0.0, 0.0)])
# #     # println("simplify(::Vector{Any})::Hyper")
# end

function simplify(x::Number)::Hyper
    return Hyper([(Field(x), 0.0)])
end

function simplify(x::Hyper)::Hyper
    acc = Dict{Float32, Field}()
    # ⚠️ e, r REVERSED in dict DONT-FIX!!!
    for (r, e) in x.terms
        acc[e] = get(acc, e, 0.0) + r
    end
    return Hyper([(r, e) for (e, r) in acc if r ≠ 0.0 && e>MIN_ORDER ]) # && e<MAX_ORDER
    # return sort1(Hyper([(r, e) for (e, r) in acc if r ≠ 0.0]))
end

# simplify(x::Vector{Tuple{R, S}}) where {R<:Real, S<:Real} = simplify(Hyper(x))
simplify(x::Vector{Tuple{R, S}}) where {R<:Field, S<:Float32} = simplify(Hyper(x))
 
real(x::Real) = x

denoise(x::Hyper) = Hyper([(r, e) for (r, e) in x.terms if abs(r) > CALC_CUTOFF]) # denoise !
# function denoise(x::Hyper; ω_cutoff=1e-12) Hyper([(r,e) for (r,e) in x.terms if !(e > 0.0 && abs(r) < ω_cutoff)]) end

Base.:+(x::Hyper, y::Hyper)::Hyper = simplify(vcat(x.terms, y.terms))
Base.:+(x::Hyper, y::Real) = x + Hyper(y)
Base.:+(x::Hyper, y::Field) = x + Hyper(y)
Base.:+(x::Field, y::Hyper) = Hyper(x) + y
Base.:+(x::Real, y::Hyper) = Hyper(x) + y
Base.:+(x::Hyper, y::Terms) = x + Hyper(y)
Base.:-(x::Hyper)::Hyper = Hyper([(-r, e) for (r, e) in x.terms])
# Base.:-(x::Hyper)::Hyper = [(-r, e) for (r, e) in x.terms]
Base.:-(x::Hyper, y::Hyper)::Hyper = x + (-y)
Base.:-(x::Hyper, y::Real) = x - Hyper(y)
Base.:-(x::Real, y::Hyper) = Hyper(x) - y
Base.:*(x::Hyper, y::Hyper)::Hyper = simplify([(r1*r2, e1+e2) for (r1, e1) in x.terms for (r2, e2) in y.terms])
Base.:*(a::Real, x::Hyper)::Hyper = [(a * r, e) for (r, e) in x.terms]
Base.:*(x::Hyper, a::Real) = [(r * a, e) for (r, e) in x.terms]
Base.:/(x::Hyper, y::Hyper) = x * inv(y)
Base.:/(x::Hyper, y::Real) = x / Hyper(y)
Base.:/(x::Real, y::Hyper) = Hyper(x) / y
Base.:*(x::Real, y::Hyper) = Hyper(x) * y
Base.:*(x::Hyper, a::Real) = x * convert(Hyper, a)
# Base.:*(x::Hyper, a::Real) = [(r * a, e) for (r, e) in x]
Base.:*(a::Int, x::Hyper) = Field(a) * x
Base.:*(x::Hyper, a::Int) = x * Field(a)

Base.:(==)(x::Hyper, y::Hyper) = simplify(x).terms == simplify(y).terms
# Base.:(==)(x::Hyper, y::Hyper) = isequal(simplify(x).terms, simplify(y).terms)

# Works for simple cases but too simplistic for full 
# Base.inv(x::Hyper)::Hyper = Hyper([(1.0/r, -e) for (r, e) in x.terms if r ≠ 0.0])

function Base.inv(h::Hyper)::Hyper
    (iszero(h) || length(h.terms) == 0 ) &&  return ∞ # not ω! throw(DivideError()) 
    # a₀, e₀ = findmax(h.terms) do (r, e) e end
    a₀, e₀ = sort(h.terms, by = t -> -t[2])[1] 
    x = Hyper([(1 / a₀, -e₀)]) # invert leading term
    # Newton iteration! Absolutely genius!
    for _ in 1:3  # Increase for higher precision
        x = x*(2-h*x)
    end
    return x
end


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
Base.:^(x::Hyper, p::Real) = denoise(order(simplify(exp(p * log(x)))))
Base.:^(x::Hyper, p::Hyper) = denoise(order(simplify(exp(p * log(x))))) # pray?



sign(x::ComplexF64) = isreal(x) ? (x.re > 0 ? 1.0 : x.re < 0 ? -1.0 : 0.0) : 1.0 # sign(im) shall be 1.0 

# PART functions
# real part of a hyperreal EVEN IF contains ω≈∞
real(x::Hyper)::Field = sum((r for (r, e) in simplify(x).terms if e == 0.0), init=Field(0.0))
standard(x::Hyper)::Field = isfinite(denoise(x)) ? real(x) : sign(leading(x)[1]) * ∞
infinitesimal(x::Hyper)::Hyper = [(r, e) for (r, e) in simplify(x).terms if e < 0.0]
infinite(x::Hyper)::Hyper = [(r, e) for (r, e) in simplify(x).terms if e > 0.0]
finite(x::Hyper)::Hyper = [(r, e) for (r, e) in simplify(x).terms if e <= 0.0]

standard(b::Bool) = b ? 1.0 : 0.0
standard(x::Real) = x
standard(f::Function) = x -> standard(f(x)) # broadcastable!

# aliases 
const re = real
const st = standard
# const eps = infinitesimal name exists in julia! eps()==2.220446049250313e-16 !
const epsilon = infinitesimal #ε
const omega = infinite


const LOG2_H = Hyper([(log2_h, 0.0)])  # approximate ln(2)

function <(x::ComplexF64, y::Float64) 
    x.im != 0 && throw(ArgumentError("< on Complex number with imaginary part")) || x.re < y 
end
function <(x::ComplexF64, y::Int64) 
    x.im != 0 && throw(ArgumentError("< on Complex number with imaginary part")) || x.re < y 
end
function <(x::Float64, y::ComplexF64)
    return x < y.re
end


# log(ω^n) = n*ω ?
# log(ε) = -√ω = -1/√ε 
function log(u::Hyper; terms=TERM_PRECISION)
    if isreal(u) return log(real(u)) end
    stv = standard(u)
    if !isreal(stv)
        println("handle complex numbers")
        return log(real(u)) + im * log(imag(u))
    end
    if stv < 0.0
        # println("handle negative infinitesimals")
        return log(-u) + im * π # complex !
    elseif stv == 0.0 # handle positive infinitesimals 
        if u == ε || u == -ε
            return -ω
        end
        println("u=", u, " stv=", stv)
        return -ω
         # The approach is naive: if u = c * ε^k, log(u) ≈ log(c) + k*(log(ε)),
    #     # return Hyper([(realpart, 0.0), (1.0, e_min * 100)]) # ω^100 hack
    end
    if stv == Inf return ω end
    if stv <=0  return zero end # hack?
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
        term = sign * t
        term = term / Hyper(k)  # ensure proper overload
        s += term
        t *= z
        sign = -sign
    end
    # Combine adjustments for factors of 2:
    return Hyper([(Field(n), 0.0)]) * LOG2_H + s
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
    return Hyper([(r,e) for (r,e) in x if e > MIN_ORDER && e < MAX_ORDER && abs(r) > CUTOFF])
end

function Base.show(io::IO, x::Hyper)
    x = common(x) # only up to order 10
    terms = order(simplify(x)).terms
    isempty(terms) && return println(io, "0")
    str = join(termstr.(terms), " + ")
    println(io, str)
end

isreal(x::ComplexF64) = round(x.im) ≈ 0.0
real(x::ComplexF64) = x.re

# Predicates

isreal(x::Hyper) = all(e == 0.0 for (_, e) in simplify(x).terms) # do NOT round here for high precision Taylor!
isfinite(x::Hyper) = all(e ≤ 0.0 for (_, e) in simplify(x).terms)
isinfinite(x::Hyper) = any(e > 0.0 for (_, e) in simplify(x).terms)
# isinfinitesimal(x::Hyper) = all(e < 0.0 for (_, e) in simplify(x).terms) # excluding 0 !?
isinfinitesimal(x::Hyper) = all(e < 0.0 || (e == 0.0 && abs(r)<NEAR_TOLERANCE) for (r, e) in simplify(x).terms) # with ≈ 0

isreal(x::Real) = true
isfinite(x::Real) = true
isinfinite(x::Real) = false 
isinfinitesimal(x::Real) = false # excluding 0 !?


# Optional: stricter variants (ε or ω only, no higher orders than -1 / 1)
isfinite1(x::Hyper) = begin r = standard(abs(x)); simplify(x).terms == [(r, 1.0)] end
isinfinitesimal1(x::Hyper) = begin r = standard(abs(x)); simplify(x).terms == [(r, -1.0)] end


termstr(t::Term) = begin
    c, e = t
    c=round(c; digits=ROUNDING_DIGITS) # coefficient
    e1 = (e == floor(e)) ? string(Int(abs(e))) : string(abs(e)) # 1.0 => 1
    if !isreal(c) 
        return "($(string(c)))ω^$(e1)"
    end
    c = real(c)
    c = (c == floor(c)) ? string(Int(c)) : string(c) # 1.0 => 1
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

raw(x::Number) = string(x)
function raw(x::Hyper) # debug: avoid rounding etc
    return string(x.terms)
end



@assert 1.0 + 0.0im == 1.0 - 0.0im

x = ω + 3.0 - 4.0 * ω + 2.0 * ε * ε + 1 - ε^2
# println(x)
@assert x == 4.0 + ε^2 + -3.0ω

# @assert 0.0 == 𝟘  FAILS

# ≅(x::Real, y::Hyper) = simplify(Hyper(x)) == simplify(y)
# ≅(x::Hyper, y::Real) = y ≅ x
# ≅(x::Hyper, y::Hyper) = simplify(x) == simplify(y)


# ⸟(x::Hyper, y::Hyper) unknown unicode character '⸟'
# ⸞(x::Hyper, y::Hyper) unknown unicode character '⸞'

≡(x::Hyper, y::Hyper) = simplify(x)==simplify(y) # \\equiv ≡ ≢ ≡⃥ 
≣(x::Hyper, y::Hyper) = x==y # \\Equiv ≣
⩮( x::Hyper, y::Hyper) = x==y # \\eqcirc ≈ near!?
⩶( x::Hyper, y::Hyper) = x==y # \\eqeqeq ≈
⩰(x::Hyper, y::Hyper) = round(x)==round(y)
≅(x::Hyper, y::Hyper) = round(x)==round(y) # \\cong  congruent
≊(x::Hyper, y::Hyper) = round(x)==round(y) # \\approxeq
≌(x::Hyper, y::Hyper) = x≈y # \\allequal ALL EQUAL TO Unicode: U+224C, UTF-8: E2 89 8C
≋(x::Hyper, y::Hyper) = x≈y # TRIPLE TILDE Unicode: U+224B, UTF-8: E2 89 8B
≍(x::Hyper, y::Hyper) = x≈y # \\asymp asymptotic EQUIVALENCE  ω≍ω+1
⩭(x::Hyper, y::Hyper) = near(x,y) # \\congdot overkill! ⩸ ⇌
⩯(x::Hyper, y::Hyper) = near(x,y) # \\hatapprox
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
# abs(x::Hyper)::Hyper = Hyper([(abs(r), e) for (r, e) in x.terms])
abs(x::Hyper)::Hyper = x>=0 ? x : -x # FLIP ALL signs! -1+ϵ => 1-ϵ ! may contain negative terms!

# Helper: construct scalar multiple of ε or ω ??
# εr(r::Real) = [(r, -1.0)]
# ωr(r::Real) = [(r, 1.0)]

# Proximity relations

near(x::Hyper, y::Hyper) = isinfinitesimal(x - y)
near(x::Vector{Tuple{Float64, Float64}}, y::Hyper) = near(Hyper(x), y)
near(x::Hyper, y::Vector{Tuple{Float64, Float64}}) = near(x, Hyper(y))

cofinite(x::Hyper, y::Hyper) = isfinite(x - y)


# highest order term of x
function lead(x::Hyper)::Hyper
    if length(x.terms) <= 1 return x end
    sorted = order(x).terms
    return Hyper([sorted[1]])
end

# ~(x::Hyper, y::Hyper) = near(x, y) use ⩯ for exact nearness
# ~(x::Hyper, y::Hyper) = near(round(x), round(y)) 
# ~(x::Hyper, y::Hyper) = near(denoise(x), denoise(y)) 
~(x::Hyper, y::Hyper) = lead(x) ≈ lead(y) || near(x,y)
~(x::Hyper, y::Real) = x ~ Hyper(y)
~(x::Real, y::Hyper) = Hyper(x)~(y)
~(x::Int, y::Hyper) = Hyper(x)~(y)
~(x::Number, y::Number) = isapprox(x, y, atol=NEAR_TOLERANCE)
# ~(x::Real, y::Real) = isapprox(x, y, atol=NEAR_TOLERANCE)
# ~(x::Number, y::Number) = round(x)≈round(y)

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
# monad(x::Real) = Monad(Hyper(x))

Base.:∈(y::Hyper, M::Monad) = near(M.center, y)
Base.:∈(x::Real, M::Monad) = Hyper(x) ∈ M

@assert !isinfinite(0)
@assert !isinfinite(0.0)
@assert !isinfinite(ε)
@assert !isfinite(ω)

# == equality only works if BOTH ARE Hyper! For mixed Hyper, Real use ≈
@assert 1/ε == ω
@assert 1/ω == ε
@assert ε*ω == 𝟙
println(1/ε)
println(ε^-1)
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

# •(x::Hyper) = standard(x) # unknown unicode character '•'
# ·(x::Hyper) = standard(x) # NOT indicative for real or standard part!
# @assert ·(𝟙) == 1  # type · via alt+shift+9

leading(x::Hyper) = begin
    terms = simplify(x).terms
    isempty(terms) && return (0.0, 0.0)
    order, index = findmax(x -> x[2], terms) # x[2] is the exponent, [2] is index
    return terms[index]
end

# DON'T USE THIS! CAUSES subtle ERRORs!!!
# Base.getproperty(x::Hyper, sym::Symbol) = begin
#     hyper_synonyms = Dict(
#         :real => [:re, :º, :r],
#         :standard => [:st, :s],
#         :epsilon => [:e, :ep, :eps, :infinitesimal, :low, :small, :ε],
#         :omega => [:o, :om, :high, :big, :infinite],
#         :finite => [:f, :finitepart],
#     )
#     synonym_lookup = Dict{Symbol,Symbol}()
#     for stdname in keys(hyper_synonyms), alias in hyper_synonyms[stdname]
#         synonym_lookup[alias] = stdname
#     end
#     stdsym = haskey(synonym_lookup, sym) ? synonym_lookup[sym] : sym
#     # if stdsym != sym
#     #     @warn "Accessing property `$(sym)` via synonym for `$(stdsym)`."
#     # end
#     if stdsym === :real
#         return real(x)
#     elseif stdsym === :standard
#         return standard(x)
#     elseif stdsym === :epsilon
#         return infinitesimal(x)
#     elseif stdsym === :omega
#         return infinite(x)
#     elseif stdsym === :finite
#         return finite(x)
#     else
#         return getfield(x, sym)
#     end
# end

# @assert 𝟙.re == 1
# @assert 𝟙.º == 1  # type º via alt+0

# y = 4 + ε² + -3ω
# @assert y.re == 4
# @assert leading(y) == (-3.0, 1.0) # leading term -3ω with highest order 1
# @assert y.st == -∞

# @assert y.eps == ε²
# @assert y.epsilon == ε²
# @assert y.infinitesimal == ε²
# @assert y.low == ε²
# @assert y.high == -3ω
# @assert y.small == ε²
# @assert y.big == -3ω
# @assert y.omega == -3ω
# @assert y.infinite == -3ω
# @assert y.finite == 4 + ε²


@assert standard(𝟘) == 0
@assert standard(𝟙) == 1
@assert standard(ω) == ∞
@assert standard(ε) == 0
@assert standard(𝟙+ε) == 1

# @assert eps(ε) == ε


# x = ω
# x = 2ε
x = ω + 3.0 - 4.0 * ω + 2.0 * ε * ε + 1 - ε^2
@assert real(x) == 4.0
@assert standard(x) == -∞
println(x)
# println(real(x)) # 4.0 just the real part
# println(standard(x)) # Inf ∞ because of ω
println(x*x)

# sqrt(x::Hyper)::Hyper = [ (sqrt(r), e/2) for (r, e) in x if r > 0.0 ]
# sqrt(x::Hyper)::Hyper = [(sqrt(r), e/2) for (r, e) in x.terms if r ≥ 0.0]
sqrt(x::Hyper)::Hyper = x^.5
# sqrt(x::Hyper)::Hyper = order(x^.5)  FAILS √ε == ε ^ (1 / 2)

@assert √(ε) == ε^(1/2)
@assert √(ε) == ε^.5 
@assert √(ε) ≈ ε^.5
@assert √(ε) ~ ε^.5
@assert √ε ~ ε^.5 # OK! good tokenizer


# leading() term of x PLUS one smaller order term!
function dominant(x::Hyper)::Hyper
    if length(x.terms) <= 1 return x end
    sorted = order(x).terms
    return Hyper([sorted[1], sorted[2]])
end

function least(x::Hyper)::Hyper
    if length(x.terms) <= 1 return x end
    sorted = order(x).terms
    return Hyper([sorted[end]])
end


#:$(__source__.line)
# Expression: $(string($(QuoteNode(lhs)))) == $(string($(QuoteNode(rhs))))
macro asserts(expr)
    if expr.head == :call && (expr.args[1] == :(==) || expr.args[1] == :(≈) || expr.args[1] == :(~))
        lhs = expr.args[2]
        rhs = expr.args[3]
        exact = expr.args[1] == :(==) 
        return quote
            res1 = $(esc(lhs))
            res2 = $(esc(rhs))
            if $exact
                if !(res1 == res2) 
                    msg = """
                    FAILED @asserts $(string($(QuoteNode(lhs)))) == $(string($(QuoteNode(rhs))))
                    Left:  $(res1)
                    Right: $(res2)
                    """
                    println(msg) # assert again to get the line number
                end
            end
            if !$exact
                if !(res1 ~ res2)
                    msg = """
                    FAILED @asserts $(string($(QuoteNode(lhs)))) ~ $(string($(QuoteNode(rhs))))
                    Left:  $(res1)
                    Right: $(res2)
                    """
                    # Left:  $(raw(res1))
                    # Right: $(raw(res2))
                    # Left:  $(round(simplify(order(res1))))Right: $(round(simplify(order(res2))))
                    println(msg) # assert again to get the line number
                    # throw(AssertionError(msg))
                end
            end
            # println("✓ @is: ", $(string(lhs)), " == ", $(string(rhs)))
        end
    else
        error("@asserts expects an expression of the form `x == y`")
    end
end

# println("dominant($(x)) is ", dominant(x))
# println("dominant(y^2) is ", dominant(y*y))
println("dominant((ε + ω)^2) is ", dominant((ε + ω)^2)) # ω² + 2 / 2 + ω²
# @assert dominant((ε + ω)^2) ~ ω² + 2ω  TODO: sync display rounding with ~ rounding 

println("√(ε + ω) is ", √(ε + ω)) # ∑ωⁿ/2ⁿn! ~ … + 0.020833̅ω^3 + 0.125ω² + 0.5ω + 1   Maclaurin expansion coefficient of e^{x/2}.
# @assert lead(√(ε + ω)) ~ 2e-20ω^17  # Hyper[(1/2ⁿn!,n)] in limit?    TODO: changes with precision
@assert least(√(ε + ω)) ~ 1

# @assert √ω^2 ~ ω # TODO 
# @asserts √(ω^2) ~ ω # same
# @assert (√ω)^2 ~ ω # TODO 
@assert √ω ~ ω^.5 # definition
@assert √ω ~ ω^(1/2) # same

# Test full inverse
# @asserts (ω+1)*((ω+1)^-1) ~ 1
# @asserts 1/(1/(ω+1)) == ω+1

@assert ω ~ ω+1 # ignore lower orders!
@assert 1 ~ 1+ε # ignore lower orders!

@assert 1/(1/(ω+1)) ~ ω+1 # precision inv would be too hard!
@assert 1/(1/(ε+1)) ~ ε+1

@assert (ω+1)*(1/(ω+1)) ~ 1
@assert (ω^2)*(1/(ω^2)) ~ 1
@assert (ω^2+1)*(1/(ω^2+1)) ~ 1
@asserts (ω^2 + ω + 1)*(1/(ω^2 + ω + 1)) ~ 1
@assert (ω^2 + ω + 1)*(1/(ω^2 + ω + 1)) ~ 1


isless(x::Number, y::Hyper) = Hyper(x)<y
isless(x::Hyper, y::Number) = x<Hyper(y)
isless(x::Int64, y::ComplexF64) = isreal(y) ? x < real(y) : false # todo
isless(x::ComplexF64, y::ComplexF64) = real(x) < real(y) || (real(x) == real(y) && imag(x) < imag(y)) # Todo HACK!

function isless(x::Hyper, y::Hyper)
    tx = sort(simplify(x).terms; by = t -> -t[2])
    ty = sort(simplify(y).terms; by = t -> -t[2])
    nx, ny = length(tx), length(ty)
    if nx == 0 && ny == 0 return false end
    if nx == 0 return sign(ty[1][1]) > 0 end
    if ny == 0 return sign(tx[1][1]) < 0 end
    return tx<ty
end

@assert 0<ε
@assert ε<ω
@assert 1<ω
@assert ε<1
@assert 0>-ε
@assert ε>-ω
@assert 1>-ω
@assert ε>-1

# println("√(2+ε)", √(2+ε)) 
# println("√(2+ε)*√(2+ε) = ",√(2+ε)*√(2+ε)) # 2 + ε  NICE we get it back despite denoising !
println("√(2+ε)² = ",√(2+ε)^2.0) # 2 + ε  NICE we get it back despite denoising! 
println("√(2+ε)² = ",(√(2+ε))^2.0) # 2 + ε + 0ε^8  good enough!
@assert √(2+ε)*√(2+ε) ~ 2+ε
# @assert √(2+ε)*√(2+ε) ≈ 2+ε   # if ≈ like ~
# @assert √(2+ε)*√(2+ε) == 2+ε  # never!
@assert (√(2+ε))^2 ~ 2+ε

# println(st(√(2+ε))) 
@assert st(√(2+ε)) ≈ √2

if TERM_PRECISION == 12
@assert st(√(2+ε)) == √2 # TODO only for precision 12, NOT HIGHER WHY??
end
@assert (√(0))^2 == 0
@assert ε^0 == 1
@assert ω^0 == 1
# @assert (√(2+ω))^2 == 2+ω # todo define x^y better

# Riemann sum/integral
# ∑(x::Hyper, f::Function) = sum(f(x))




#  Julia doesn’t allow users to subtype Function directly, so we need to wrap our Closure (for print etc)
struct Closure{F} <: Function
    fun::F # Function, Closure or anonymous #var (julia closure)
    name::Symbol
end
guessname(f::Function) = Symbol(string(f))
guessname(f::Closure) = f.name
Closure(f::F) where {F} = Closure(f, guessname(f))
(c::Closure)(x) = c.fun(x) # make it callable, behave like a function!
Base.show(io::IO, w::Closure) = print(io, "ƒ(", w.name, ")")
Base.show(io::IO, ::Type{<:Closure}) = print(io, "Closure") # we don't want to show ugly type
Base.show(io::IO, ::MIME"text/plain", ::Type{<:Closure}) = print(io, "Closure") # "Closure $(getTypeOfDetails(t))"
# avoid (::Main.HyperReals.Closure{Main.HyperReals.var"#159#160"{Main.HyperReals.Closure{Main.HyperReals.var"#77#78"{typeof(Main.HyperReals.sign)}}}})(x::Int64)
Base.convert(::Type{Closure}, h::Number) = Closure(x->h,Symbol("const $(h)"))
Base.convert(::Type{Closure}, f::Function) = Closure(f)
Base.promote_rule(::Type{Function}, ::Type{Closure}) = Function
Base.promote_rule(::Type{Closure}, ::Type{Function}) = Function
Base.:+(f::Function, g::Function) = x -> f(x) + g(x)
Base.:+(c::Function, n::Number) = Closure(x -> c(x)+n)
Base.:-(c::Function, n::Number) = Closure(x -> c(x)-n)
Base.:*(c::Function, n::Number) = Closure(x -> c(x)*n)
Base.:/(c::Function, n::Number) = Closure(x -> c(x)/n)
Base.:-(c::Function) = Closure(x -> -c(x)) # negation for closures
c = Closure(x->x, Symbol("const x")) # closure for x
@assert((c+1)(1.0) == 2.0) 
@assert((c*2)(2.0) == 4.0) 
@assert((c-1)(1.0) == 0.0)  # new assertion for subtraction
@assert((c/2)(2.0) == 1.0)  # new assertion for division
# derivative ∂(f)
#################################################

# ∂(f::Function) = f'
# ∂(f::Function) = x -> (f(x) - f(x-ε)) / ε # backward difference
# ∂(f::Function) = x -> (f(x+ε) - f(x)) / ε  # forward difference
# ∂(f::Function) = x -> (f(x+ε) - f(x-ε)) / 2ε  # central difference
∂(f::Function) = Closure(x -> simplify((f(x+ε) - f(x-ε)) * ω / 2), guessname(f)) # central difference
∂(c::Closure) = Closure(x -> simplify((c(x+ε) - c(x-ε)) / 2ε), Symbol("∂$(c.name)"))
# should follow from definitions of ∫ and ∂ if we treat number h as constant function h(x)=h
∂(x::Hyper) = Hyper([(r, e-1) for (r, e) in x.terms])
# ∂(h::Hyper) = ∂(Closure(x, Symbol("const $(h)"))) # why not via convert?
∂(x::Real) = 𝟘 # ∂1=0  

# ∂(f::Function) = x -> denoise(simplify((f(x+ε) - f(x-ε)) / (2ε)))


# todo: check f≈g on more sample points (or use a better test;)
≈(f::Function, y::Number) = all(f(x) ≈ y for x in (-1.0, 0.0, 1.0)) # lol
≈(f::Function, y::Hyper) = all(f(x) ~ y for x in (-1.0, 0.0, 1.0)) # lol
≈(h::Hyper, f::Function) = all(h ~ f(x) for x in (-1.0, 0.0, 1.0)) # lol
≈(f::Function, g::Function) = f==g || all(f(x) ~ g(x) for x in (-1.0, 0.0, 1.0)) # lol
# julia does NOT have Closure <: Function, so we need to define it as our own wrapper
≈(f::Closure, y::Number) = all(f(x) ≈ y for x in (-1.0, 0.0, 1.0)) # lol
≈(f::Closure, y::Hyper) = all(f(x) ~ y for x in (-1.0, 0.0, 1.0)) # lol
≈(h::Hyper, f::Closure) = all(h ~ f(x) for x in (-1.0, 0.0, 1.0)) # lol
≈(f::Closure, g::Function) = f.fun==g || all(f(x) ~ g(x) for x in (-1.0, 0.0, 1.0)) # lol
≈(f::Closure, g::Closure) = f.fun≈g.fun 

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
Base.:/(f::Function, y::Hyper) = Closure(x -> f(x) / y)
Base.:/(f::Function, y::Int64) = Closure(x -> f(x) / y)
Base.:/(c::Closure, y::Hyper) = Closure(x -> c(x) / y)

# square(x) = x^2 # uses recursive x * x so the same
# square(x) = x^2.0 # uses exponential function via exp and log approximations!


# println("∂(square)(1.0) is ",∂(square)(1.0)) # derivative of x^2 at x=2
# println("∂(square)(2.0) is ",∂(square)(2.0)) # derivative of x^2 at x=2 == 4
# @assert ∂(square)(1.0) == 2 + ε # not with central derivative!?
# @assert ∂(square)(2.0) == 4 + ε
@assert ∂(square)(1.0) ~ 2 + ε # not with central derivative!?
@assert ∂(square)(2.0) ~ 4 + ε
@assert ∂(square) ≈ x -> 2x
# @assert ∂(square) ≈ 2*id

const e=Hyper(exp(1.0)) # Euler's number
# print(e^ω) # ∑ωⁿ/n!
# print(√ω) # ∑ωⁿ/2ⁿn! ~ … + 0.020833̅ω^3 + 0.125ω² + 0.5ω + 1   Maclaurin expansion coefficient of e^{x/2}.


square2(x) = x^2.0 # uses exponential function via exp and log approximations!
# dsquare(x)=st(∂(square)(x)) 
# dsquare(x)=∂(square2)(x)
dsquare0(x)=∂(square2)(x)
# dsquare(x)=st(∂(square2)(x)) 
# dsquare=st(∂(square2))
dsquare=∂(square2)


if TERM_PRECISION>20
@assert dsquare(-2.0) ~ -4  
@assert dsquare(-1.0) ~ -2  
@assert dsquare(2.5) ~ 5
# @asserts dsquare(3.0) ~ 6
@assert dsquare(3.0) ~ 6
end

@assert dsquare(0.0) ~ 0 # OK IFF using central derivative
# @assert dsquare(ϵ) ~ 0  # OK IFF NOT using forward derivative
@assert dsquare(1.0) ~ 2  
@assert dsquare(2.0) ~ 4 


# using Plots
# plot(square, -5, 5, label="x²")
# plot!(dsquare, 1, 5, label="∂x²/∂x", linestyle=:dash)
# gui()  # hält Fenster offen
# readline()  # blockiert bis Enter gedrückt wird


# println("∂(square)(1.0) is ",∂(square)(1.0)) # 100 terms if not denoised
# println("∂(square)(2.0) is ",∂(square)(2.0)) # 
@assert ∂(square)(1.0) == 2  # oh wow why?
@assert ∂(square)(2.0) == 4  # oh wow why?
@assert ∂(square)(1.0) ~ 2 + ε  # no longer == because of exp approximation
@assert ∂(square)(2.0) ~ 4 + ε

@assert ∂(square)(1.0) ~ 2
@assert ∂(square)(2.0) ~ 4
# @assert ∂(square) ≈ x -> 2.0
# @assert ∂(square) ≈ 2x
# @assert ∂(square)(x::Hyper) == 2x

# display(∂(square)) # derivative of square

x = id # only temporary! we had variable x = ω +1  before lol
println(∂(x)) # derivative of x ??
@assert ∂(x) ≈ 1

linear(x::Hyper) = x
linear(x::Number) = x
@assert ∂(linear) ≈ 1.0
@assert ∂(linear) ≈ x -> 1.0

# Base.sin(x::Hyper) = lift(sin, x)
# Base.cos(x::Hyper) = lift(cos, x)
# Base.exp(x::Hyper) = lift(exp, x)
# Base.log(x::Hyper) = lift(log, x)
# Base.sin(x::Hyper) = sin(standard(x)) 
# as explicit Taylor series sum
# @assert factorial(3)==3! not in julia
# Base.cos(x::Hyper) = cos(standard(x)) + 𝟘

Base.sin(x::Hyper) = sum((-1)^n * (x^(2n + 1)) / factorial(2n + 1) for n in 0:9)
Base.cos(x::Hyper) = sum((-1)^n * (x^(2n)) / factorial(2n) for n in 0:10)

function plot_ascii(f::Function; xlim=(-5,5), width=60, height=20)
    canvas = fill(' ', height, width)
    xvals = range(xlim[1], xlim[2], length=width)
    yraws = [st(f(x)) for x in xvals]
    ymin, ymax = minimum(yraws), maximum(yraws)
    delta = 0.05 * (ymax - ymin + eps()) # small padding
    ylim = (ymin - delta, ymax + delta)
    yscale = y -> try
        round(Int, (ylim[2] - real(y)) / (ylim[2] - ylim[1]) * (height - 1)) + 2
    catch
        height # setzt außerhalb der Sichtbarkeit
    end
    for (i, y) in enumerate(yraws)
        row = clamp(yscale(y), 1, height)
        canvas[row, i] = '*'
    end
    println(join([join(row) for row in eachrow(canvas)], "\n"))
end
function plot_ascii(f::Closure; xlim=(-5,5), width=60, height=20)
    plot_ascii(f.fun; xlim=xlim, width=width, height=height)
end

# plot_ascii(square; xlim=(-π, π))
# plot_ascii(∂(square); xlim=(-π, π))
# plot_ascii(sin; xlim=(-π, π))

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
# @asserts ∂(sin)(3π/2) ~ 0  # -1.1433e-5 Todo imprecise WHY
# @assert ∂(sin)(3π/2) ~ 0
# @asserts ∂(sin)(2π) ~ 1 # 0.99652139
# @assert ∂(sin)(2π) ~ 1
@assert ∂(sin)(-π/2) ~ 0
# @asserts ∂(sin)(-π) ~ 1 # -1.000000004 
# @assert ∂(sin)(-π) ~ 1
@assert ∂(sin)(1.0) ~ cos(1.0)
@assert ∂(sin)(2.0) ~ cos(2.0)
@assert ∂(sin)(3.0) ~ cos(3.0)

# plot_ascii(∂(sin); xlim=(-π, π))


@assert ∂(sin) isa Function || ∂(sin) isa Closure
println(typeof(∂(sin))) 
println(∂(sin)) # derivative of sin

@assert ∂(sin) ≈ cos
@assert ∂(exp) ≈ exp

# Base.log(x::Hyper) = sum(((-1)^(n-1)) * ((x-1)^n) / n for n in 1:TERM_PRECISION) # redefined
# logx(x::Hyper) = sum(((-1)^(n-1)) * ((x-1)^n) / n for n in 1:TERM_PRECISION) # redefined
# @assert ∂(logx) ≈ x->1/x # derivative of logarithm function
# @assert ∫(log) ≈ x -> x * log(x) - x # integral of logarithm function
# @assert ∂(tan) ≈ sec^2
# @assert ∂(tan) ≈ x->sec(x)^2

# step(x::Hyper) = x > 0 # promote bool to Hyper
# step(x::Hyper) = x > 0 ? 1 : 0
# step(x) = x > 0 ? 1 : 0
step(x) = x > 0 # aka positive, Heaviside 0⁺, unitstep …
step0(x) = x >= 0 # aka leftsided jump Heaviside 0⁻  HAS WRONG negative ∂² !! Todo WHY?
# plot_ascii(step; xlim=(-5, 5))
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

sign(x::Number) = x > 0 ? 1 : (x < 0 ? -1 : 0)
@assert ∂(sign)(0) ≈ ω # nice, FULL(double) dirac from -1 to 1


# Dirac delta function (or δ distribution)
# δ can be easily represented with Hyper numbers:
δ(x) = x == 0 ? ω/2 : 0 # Dirac delta function "spike activation"
# ⚠️ when integrating δ we get the Heaviside+ step function 
"we only jump AFTER the time starts running at t=ϵ / t>0 !  ω*0=0 ω*ϵ=1 !" 

@assert st(δ(0)) == ∞

@assert ∂(step) ≈ δ # derivative of step function

# @assert ∫(δ) ≈ step # integral of Dirac delta function TODO!

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

# println(∂(∂(sign))(0)) TODO!
# @assert ∂(∂(sign)) ≈  ω*ω/2 # ignore the ϵ part


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

# TODO: 3rd derivative
# Unfortunately we are losing information after the second derivative:
# @assert ∂(∂(∂(abs)))(0) ≈ ω*ω/2 # full circle SPIKE!

# @assert ∫₀(∂(abs))(x) ≈ abs(x) # integral of abs function
# @assert ∫(∂(abs))(x) ≈ x*abs(x) # check integral of derivative

# @assert ∫₀(∂(step))(x) ≈ step(x) # integral of step function
# @assert ∫(∂(step))(x) ≈ x*step(x) # check integral of derivative of step function

# Riemann sum
###########################################
# ∑(n) # may or may not be understood as n+n+n+…+n  ω times
# ∑(x::Number)=ω*x/2  # N*(N+1)/2 in the context of Hyper
# @assert ∑(0) == 0
# @assert ∑(ϵ) ≈ 1/2
# @assert ∑(1) == ω/2
# @assert ∑(ω) == ω^2/2 


# ∑(f::Function) = sum(f(ε * i) * ε/2 for i in 0:ω) # we can't do that directly =>
# ∑(x::Hyper, f::Function) = sum(f(x + ε * i) * ε for i in 0:ω) # we can't do that

# simpler version of repeated ∂(f)
function nth_derivative(f, n)
    if n == 0
        return f(0)
    else
        h = ε
        return (nth_derivative(x -> f(x + h), n - 1) - nth_derivative(x -> f(x - h), n - 1)) / (2h)
    end
end



function taylor_series(f::Function, N::Int=TAYLOR_TERMS)
    terms = Hyper[]
    for n in 0:N
        deriv = nth_derivative(f, n)
        deriv = simplify(deriv) 
        coeff = deriv / factorial(n) # max 20!!
        order = Float32(n)
        push!(terms, coeff)
    end
    return terms
end

# ∑(f::Function) = sum(f(ε * i) * ε for i in 0:ω) # we can't do that directly =>
# CHEAP TRICK!
∑(f::Function) = if f(TERM_PRECISION) >= f(TERM_PRECISION-1) return ω*f(1) else sum(f(i) for i in 1:TERM_PRECISION) end # OK >= 30  # simply divergent
∑₀(f::Function) = f(0) + ∑(f)
@assert ∑(x -> ϵ) ≈ 1
@assert ∑(x -> 1) ≈ ω #cheap trick!
@assert ∑(x -> 1/(2^x)) ≈ 1

# using SpecialFunctions 
# @assert zeta(2) ≈ π²/6
# ∑(f::Function) = sum(f(BigFloat(i)) for i in 1:100000) 
# @asserts ∑(x -> 1/(x^2)) ≈ π²/6
# @assert ∑(x -> 1/(x^2)) ~ π²/6 # needs 10^d steps for d digits accuracy 

# Riemann sum very differnt from the above
function ∑2(f::Function, b::Hyper=ω)
    # Assume f(x) = a₀ + a₁x + a₂x² + …, and f is polynomial-like (approximated by Taylor series)
    # Sum over x = i*ε for i=0:ω, i.e., x ∈ [0, ω*ε] = [0,1]
    sum = zero
    term = ε * b
    for n in 0:TAYLOR_TERMS
        coeff = taylor_series(f)[n+1]
        order = Float32(n)
        integral_coeff = coeff / (order + 1)
        term = term * b
        sum += integral_coeff * term 
        # push!(terms, (integral_coeff * ε * b, order + 1))  # ∫ x^n dx = x^{n+1}/(n+1)
    end
    return sum
end

test_again = false
if test_again

# ∫(f::Function) = Closure(x->(ε*∑(f)(x*ω)), Symbol("∫$(guessname(f))")) # anchored at 0
# const TAYLOR_TERMS = 10 #TODO WHY SO SLOOOW?
# @asserts ∫(sin)(0) ~ -1
# @asserts ∫(sin)(0) ~ -1


# @asserts ∑(x -> 1) ≈ ω     # sum of constant function over [0,ω]
# @asserts ∑(x -> x) ≈ ω^2/2    # sum of linear function over [0,ω]
# @asserts ∑(x -> ε) ≈ 1

@assert ∑(x -> 0) ≈ 0    
@assert ∑(x -> ε) ≈ 1 
@assert ∑(x -> 1) ≈ ω     # sum of constant function over [0,ω]
# @assert ∑(x -> x) ≈ ω^2/2    # sum of linear function over [0,ω]
# @asserts ∑(x -> x*x) ≈ ω^3/3 
# @assert ∑(x -> x*x) ≈ ω^3/3  
# @assert ∑(x -> x^n) ≈ ω^n/n  ?
# println(log(ω)) ≈ ∑±ⁿ√ω ?
# e^log(ω) = ω => log(ω) = ∫(1/x)dx x>1 
# @asserts ∑(x -> 1/x) ≈ ω * log(ω) # sum of 1/x over [0,ω]
# @assert ∑(x -> 1/x) ≈ -ω^8/36 + ω^4/2 # why?
# @asserts ∑(x -> 1/(x*x)) ≈ 2
# @assert ∑(x -> 1/(x*x)) ≈ 2

# ∑(x::Number) = ω * x / 2 # N*(N+1)/2 in the context of Hyper
# Solved where does factor 1/2 come from when using ε as const Function? ;)
# ∑(h::Hyper) = ∑(x->h) # constant
∑(n::Number) = ∑(x->n) # constant
@assert ∑(𝟘) ≈ 0    
@assert ∑(ε) ≈ 1 #/2
@assert ∑(𝟙) ≈ ω #/2     # sum of constant function over [0,ω]
@assert ∑(3) ≈ 3ω # linear!
# @assert ∑(x) ≈ ω^2/2   # makes no sense unless we define x via @variables x in Symbolics or @syms x in SymPy


f(x) = x^2 + 3x + 1
@assert taylor_series(f)[1:3] == [1.0, 3.0, 1.0] # f(0)=1, f'(0)=3, f''(0)=2 /2!

g(x) = x^3 + 2x^2 + 3x + 4
# @asserts taylor_series(g)[1:4] == [4.0, 3.0, 4.0, 1.0] # g(0)=4, g'(0)=3, g''(0)=4, g'''(0)=1
@assert taylor_series(g)[1:4] == [4.0, 3.0+ε², 2.0, 1.0] # g(0)=4, g'(0)=3, g''(0)=4, g'''(0)=1

~(xs::Vector{Hyper}, ys::Vector{Float64})= length(xs)==length(ys) && all(xs[i] ~ ys[i] for i in 1:length(xs))

# @asserts taylor_series(exp) ~ [1.0, 1.0, 1.0] # exp(0)=1, exp'(0)=1, exp''(0)=1/2
@assert taylor_series(exp)[1:3] ~ [1.0, 1.0, 1/2] # exp(0)=1, exp'(0)=1, exp''(0)=1/2
# @asserts taylor_series(sin) ~ [0.0, 1.0, 0.0, -1/6, 0, 1/120] # sin(0)=0, sin'(0)=1, sin''(0)=0, sin'''(0)=-1/6
@assert taylor_series(sin)[1:4] ~ [0.0, 1.0, 0.0, -1/6] # sin(0)=0, sin'(0)=1, sin''(0)=0, sin'''(0)=-1/6
@assert taylor_series(cos)[1:4] ~ [1.0, 0.0, -1/2, 0.0] # cos(0)=1, cos'(0)=0, cos''(0)=-1/2, cos'''(0)=0

# Todo: treat log as a special case  (-Inf + NaN*im)ω^0
# @asserts taylor_series(log)[1:2] ~ [0.0, 1.0] # log(1)=0, log'(1)=1
# @assert taylor_series(log)[1:2] ~ [0.0, 1.0] # log(1)=0, log'(1)=1
end


# INTEGRATION integral
##########################################

# ∫₀(f)(x) = ∫(f)(x) - ∫(f)(0) # anchor at 0 # invalid function name
# ∫˳(f)(x) = ∫(f)(x) - ∫(f)(-ω) # anchor at -ω
# ∫₋∞(f)(x) = ∫(f)(x) - ∫(f)(-ω) # anchor at -∞
# ∫∞(f)(x) = ∫(f)(ω) - ∫(f)(x) # anchor at ∞
# ∫₊∞(f)(x) = ∫(f)(x) - ∫(f)(ω) # anchor at +∞
# ∫⧞(f)(x) = ∫(f)(x) - ∫(f)(∞) Nope
# ∫ˬ

# ∫ₐ(f)(x) = ∫(f)(x) - ∫(f)(a)
# ∫(f::Function) = x -> f(x) * ε  # dot integral 
# ∫(f::Function) = x -> f(x+ε) * ε - f(x)
# ∫(f::Function) = Closure(x -> ∑f(x+i*ε) * ε - f(x))
# ∫(c::Closure) = Closure(x -> c(x+ε) * ε - c(x))
# ∫(f::Function) = Closure(x->ε*∑(f,Hyper(x*ω)-∑(f,Hyper(0))), guessname(f)) # anchored at 0
# ∫(f::Function) = Closure(x->(∑(f,Hyper(x))-∑(f,Hyper(0))), guessname(f)) # anchored at 0
# ∫(f::Function) = Closure(x->(∑(f,Hyper(x))), Symbol("∫$(guessname(f))")) # anchored at 0
# ∫(f::Function) = Closure(x->(ε*∑(f)(x*ω)), Symbol("∫$(guessname(f))")) # anchored at 0
# ∫(f::Function) = Closure(x -> ∑(y -> f(y)) * ε, Symbol("∫$(guessname(f))"))
∫(f::Function) = Closure(x -> ε * ∑(y -> f(y * x * ε)), Symbol("∫$(guessname(f))"))
lower(x::Hyper) = Hyper([(r,e-1) for (r,e) in x if e>0]) # remove all 0 exponents

INTEGRATION_TERMS = 10000
# NAIVE TOY integration (but with ω steps)
∫(f::Function) = Closure(x -> begin
    sum = zero
    dx = x / INTEGRATION_TERMS
    " we only jump AFTER the time starts running at t=ϵ / t>0 !  ω*0=0 ω*ϵ=1 !" 
    if x == 0 return 0 end  # TODO Heaviside- x>=0 <<< f(x-ϵ) ?
    for i in 0:INTEGRATION_TERMS-1
        val = f(i * dx) # todo find max in range
        if isinfinite(val)
            sum += sign(x) * lower(val) # no dx! dirac step!
        else
            sum += val * dx # TODO: we must not miss any jumps! val = max f([…]) ? ok, cause ∂ catches them!
        end
    end
    return sum
end, Symbol("∫$(guessname(f))")) # anchored at 0


# ∫(f::Function) = Closure(x -> (x / ω) * ∑(y -> f(y * x / ω)), Symbol("∫$(guessname(f))"))
# ∫(f::Function) = begin
#     F_raw = Closure(x -> ∑(y -> f(x * y / ω)) * x / ω, Symbol("∫$(guessname(f))"))
#     anchor = F_raw(0)
#     Closure(x -> F_raw(x) - anchor, Symbol("∫₀$(guessname(f))"))
# end


test_again = false
if test_again # sloow!
    
    @assert ∫(∂(sign)) ≈ sign # integral of derivative of sign function
    # But TODO: Heaviside- x>=0 NOT compatible with framework!

    
    ∫sin=∫(sin)-1 # anchor!
    # println("∫sin(0) is ", ∫sin(0)) 
    # println("∫sin(π/2) is ", ∫sin(π/2)) 
    # println("∫sin(π) is ", ∫sin(π)) 
    # println("∫sin(2π) is ", ∫sin(π)) 
    # println("∫sin(-π/2) is ", ∫sin(-π/2)) 
    # println("∫sin(-π) is ", ∫sin(-π)) 
    # println("∫sin(-2π) is ", ∫sin(-π)) 
# const TAYLOR_TERMS = 5 # 10 TODO WHY SO SLOOOW?
NEAR_TOLERANCE = 1e-3 # lol only 10000 INTEGRATION_TERMS
@asserts ∫sin(0) ~ -1
@assert ∫sin(0) ~ -1
@asserts ∫sin(-π/2) ~ 0 # -0.03277228ω^5 WAY OFF! 
@assert ∫sin(-π/2) ~ 0
@asserts ∫sin(π) ~ 1

@assert ∫sin(π) ~ 1
@assert ∫sin(0) ~ -1
@assert ∂(∫sin) ≈ sin 
# @assert ∂(∫(sin)) ≈ sin # no matter how we anchor it!

abs0 = ∫(sign) # can NOT apply numeric approximation to infinitesimals!
@assert abs0(0) ~ 0
@asserts abs0(1) ~ 1
@assert abs0(1) ~ 1
@assert abs0(-1) ~ 1
@assert abs0(2) ~ 2
@assert abs0(3) ~ 3
@assert abs0(-2) ~ 2
@assert ∫(sign) ≈ abs # ☑ !!
@assert ∂(∫(sign)) ≈ sign 
# @assert ∫(∂(sign)) ≈ sign # TODO! we need -lower(ω) in left step!
@assert ∂(∫(abs)) ≈ abs 
@assert ∫(∂(abs)) ≈ abs 
@assert ∂(∫(square)) ≈ square 
@assert ∫(∂(square)) ≈ square 

@assert ∫(∂(sin)) ≈ sin
@assert ∂(∫(sin)) ≈ sin
# functions with f(0)≠0 need to be re-anchored:
@assert ∫(∂(exp)) ≈ exp-1
@assert ∂(∫(exp)) ≈ exp
@assert ∫(∂(cos)) ≈ cos-1
@assert ∂(∫(cos)) ≈ cos
end

# Symbolics integral!
# of course this works:

test_symbolics = false
if test_symbolics
using SymPy
# @syms x # if test_symbolics!
∫(f::Function) = integrate(f(x), x)
∫(f::Closure) = integrate(f(x), x)
# ∫(f::Function) = Closure(x -> integrate(f(x), x), :∫)
println(∫(sin))
# println(∫(sin)(0))
# println(∫(sin)(π/2)) # -6.12323399573677e-17
# println(∫(sin)(π))
# @assert -6.12323399573677e-17 ≈ 0 # NOT using native julia Base.isapprox !!
@assert -6.12323399573677e-17 ~ 0 # OK atol

@assert ∫(sin)(π) ~ 1
@assert ∫(sin)(0) ~ -1
@assert ∫(sin)(-π/2) ~ 0
# @assert ∫(sin) ~ -cos
# @assert ∫(sin) ≈ -cos

@assert ∫(cos)(0) ≈ 0
@assert ∫(cos)(π/2) ≈ 1
@assert ∫(cos)(π) ≈ 0
@assert ∫(cos)(-π/2) ≈ -1
# @assert ∫(cos) ≈ sin
# @assert ∫(sin) ≈ x -> -cos(x)
end # if test_symbolics

# ∫a,b(f::Function) = ∑(k in 0,ω) f(a+k*ε*b) * ε
# ∫a,b(f::Function) = ∑(k in 0,ωb) f(a+k*ε) * ε
# ∫0,x(f::Function) = ∑(i in 0,ωb) f(i*ε) * ε
# ∫(f::Function) = Closure(x -> sum(f(x + ε * i) * ε for i in 0:ω))
# ∫(f::Function) = Closure(x -> sum(f(x + dx * i) * ε for i in 0:b/steps))
# ∫(f::Function) = x -> ∑(0, ωb, f(i*ε) * ε) # anchored at 0, that's why ∫(ε) == 𝟙 !
# e.g.
# ∫x  = ∑(i in 0,ωx) f(i*ε) * ε
#     = ε*ε ∑i  # ∑i = N*(N+1)/2
#     = ε*ε * ωx*(ωx+1)/2 
#     = x²/2 + ε*ε * ωx/2
#     = x²/2 + x/2·ε

# ∫(f::Function) = x -> ∑(i in xω) f(x+i) * ε
# ∫a,b(f::Function) = x -> ∑(i in xω) f(a+kb) * ε
# ∫(f::Function) = x -> ∑(xω,f,x) * ε
# ∫(f::Function) = x -> ∑(i in -ωx:xω) f(x+i) * ε

# follows from definitions of ∫ and ∂ if we treat number h as constant function h(x)=h
∫(x::Hyper) = Hyper([(r, e+1) for (r, e) in x.terms])
∫(x::Real) = Hyper([(Field(x), 1.0)]) # ∫1=ω

# ∫x = x²/2
# @assert ∫(id) ≈ square/2 # ok anchored at 0
# @assert ∂(∫(square)) ≈ square  
# @assert ∫(∂(square)) ≈ square  # ok anchored at 0

#  if we treat ε as constant function ε(x)=ε OR define ∫
@assert ∫(1) == ω # definition
@assert ∫(ε) == 𝟙
@assert ∫(ε) ≈ 1 
# @assert ∫(ε) == 1 # can't use == because of julia limitations
@assert ∫(ω) == ω^2 # definition



# @assert ∫(step) ≈ x -> x<0 ? 0 : x # integral of step function
# @assert ∫(step)(1) ≈ 1 
# @assert ∫(step)(-1) ≈ 0 
# @assert ∫(step)(0) ≈ 0 
# @assert ∫(step)(2) ≈ 2 

println(∫(42ε)) # 42 OK by definition


# Exports
export Hyper, ε, ω, standard
export abs, isfinite, isinfinite, isinfinitesimal, near, cofinite, monad, galaxy, halo, ∂, ∫

end