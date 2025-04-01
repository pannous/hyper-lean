# make sure julia extension is installed and enabled
module HyperReals
import Base: sqrt
import Base: log
import Base: abs
import Base: exp
import Base: round
import Base: ≈ # aka Base.isapprox 0.1 + 0.2 ≈ 0.3  # true 
import Base: <
import Base: isless
# ⚠️ we use ≈ and ~ for permissive approximation ε≈0 ( sorted, simplified, rounded ) 
# on demand use ≡ for strict equality ⩭ for strict near-ness! ⩶ for strict equivalence 

const TERM_PRECISION = 40 # MAX_ORDER for calculations
const CUTOFF=1e-10 #! for display
const CALC_CUTOFF=1e-20 #! for simplification
const MAX_ORDER=10 # for display only
const MIN_ORDER=-10 # for display AND calculations
# const ROUNDING_DIGITS=12 # only for display, not for calculations
const CALC_ROUNDING_DIGITS=20 #14 # for calculations

const ROUNDING_DIGITS=9 # only for display, not for calculations SYNC WITH:
const NEAR_TOLERANCE = 1e-6 # x ≈ 0 ~ 0 for Todo: near relation / ε halo use ≊ ⩰ ⸛ ⸞ ⸟ ?
# const COMP_ROUNDING_DIGITS=8 # for comparisons

# setprecision(BigFloat, 256)  # ~77 decimal digits  TODO reuse for us?
# log2_h = log(BigFloat(2))
log2_h = log(Float64(2))

# todo infinite and infinitesimal are too similar words, consider renaming 
#  infinite:        •transfinite •divergent •omega •unbounded
#  infinitesimal:      •epsilon •micro •tiny •minis •ε

const ∞ = Inf
# const ⧞ = NaN # unknown unicode character HUH?

# const Field = Float32
# const Field = Float64
# const Field = Complex
const Field = ComplexF64
# const Field = Real

const Term = Tuple{Field, Float32} # (coefficient, exponent/order) 
# e.g. any real number has order 0, ε has order -1, ω has order 1


# const Hyper = Vector{Term} # NO WORKAROUND can turn this into a Number!
struct Hyper <: Number
    terms::Vector{Term}
end
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
# 
real(x::Real) = x
round(x::Hyper; digits::Integer=CALC_ROUNDING_DIGITS) = Hyper([(round(r; digits=digits), e) for (r, e) in x.terms if abs(r) > CALC_CUTOFF])
round_compare(x::Hyper; digits::Integer) = Hyper([(round(r; digits=digits), e) for (r, e) in x.terms if abs(r) > CUTOFF])
round_display(x::Hyper; digits::Integer) = Hyper([(round(r; digits=digits), e) for (r, e) in x.terms if abs(r) > CUTOFF])
round_display(x::ComplexF64; digits::Int64) = isreal(x) ? round(x.re; digits=digits) : round(x.re; digits=digits) + im * round(x.im; digits=digits)
# round_display(x::ComplexF64; digits::Int64) = Hyper(round(x.re; digits=digits) + im * round(x.im; digits=digits))
round_display(x::Float32; digits::Int64) = round(x; digits=digits)
round(::Type{Int}, x::Hyper) = round(Int, standard(x))

Base.:+(x::Hyper, y::Hyper)::Hyper = simplify(vcat(x.terms, y.terms))
Base.:+(x::Hyper, y::Real) = x + Hyper(y)
Base.:+(x::Hyper, y::Field) = x + Hyper(y)
Base.:+(x::Field, y::Hyper) = Hyper(x) + y
Base.:+(x::Real, y::Hyper) = Hyper(x) + y
Base.:-(x::Hyper)::Hyper = Hyper([(-r, e) for (r, e) in x.terms])
# Base.:-(x::Hyper)::Hyper = [(-r, e) for (r, e) in x.terms]
Base.:-(x::Hyper, y::Hyper)::Hyper = x + (-y)
Base.:-(x::Hyper, y::Real) = x - Hyper(y)
Base.:-(x::Real, y::Hyper) = Hyper(x) - y
Base.:*(x::Hyper, y::Hyper)::Hyper = simplify([(r1*r2, e1+e2) for (r1, e1) in x.terms for (r2, e2) in y.terms])
# Base.:*(x::Hyper, y::Hyper)::Hyper = begin
#     if length(x.terms) == 0 || length(y.terms) == 0 return 𝟘 end
#     prod = [(r1*r2, e1+e2) for (r1, e1) in x.terms for (r2, e2) in y.terms]
#     @assert all(t -> t isa Tuple{Float64, Float64}, prod) "Product term type error"
#     simplify(prod)
# end
Base.:*(a::Real, x::Hyper)::Hyper = [(a * r, e) for (r, e) in x.terms]
Base.:*(x::Hyper, a::Real) = [(r * a, e) for (r, e) in x.terms]
Base.:/(x::Hyper, y::Hyper) = x * inv(y)
Base.:/(x::Hyper, y::Real) = x / Hyper(y)
Base.:/(x::Real, y::Hyper) = Hyper(x) / y
Base.inv(x::Hyper)::Hyper = Hyper([(1.0/r, -e) for (r, e) in x.terms if r ≠ 0.0])
Base.:*(x::Real, y::Hyper) = Hyper(x) * y
Base.:*(x::Hyper, a::Real) = x * convert(Hyper, a)
# Base.:*(x::Hyper, a::Real) = [(r * a, e) for (r, e) in x]
Base.:*(a::Int, x::Hyper) = Field(a) * x
Base.:*(x::Hyper, a::Int) = x * Field(a)

Base.:(==)(x::Hyper, y::Hyper) = simplify(x).terms == simplify(y).terms
# Base.:(==)(x::Hyper, y::Hyper) = isequal(simplify(x).terms, simplify(y).terms)

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

order(x::Int64)=x

Base.:^(x::Hyper, p::Integer) = p == 0 ? 𝟙 : p == 1 ? x : ipow(x, p) # recursive x * x * x
Base.:^(x::Hyper, p::Real) = round(order(simplify(exp(p * log(x)))))
# Base.:^(x::Hyper, p::Real) = simplify(exp(p * log(x)))



sign(x::ComplexF64) = isreal(x) ? (x.re > 0 ? 1.0 : x.re < 0 ? -1.0 : 0.0) : 1.0 # sign(im) shall be 1.0 

# PART functions
# real part of a hyperreal EVEN IF contains ω≈∞
real(x::Hyper)::Field = sum((r for (r, e) in simplify(x).terms if e == 0.0), init=Field(0.0))
standard(x::Hyper)::Field = isfinite(round(x)) ? real(x) : sign(leading(x)[1]) * ∞
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
# log(ε) = -ω = -1/ε can't be ?
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
    return Hyper([(r,e) for (r,e) in order(simplify(x)).terms if e > MIN_ORDER && e < MAX_ORDER && abs(r) > CUTOFF])
end



function Base.show(io::IO, x::Hyper)
    # terms = simplify(x).terms
    # terms = simplify(round(x)).terms # rounding but keep high 
    terms = common(x).terms
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
    c=round_display(c; digits=ROUNDING_DIGITS) # coefficient
    e=round_display(e; digits=ROUNDING_DIGITS) # exponent
    if !isreal(c) 
        throw("TODO")
    end
    c = real(c)
    c = (c == floor(c)) ? string(Int(c)) : string(c) # 1.0 => 1
    e1 = (e == floor(e)) ? string(Int(abs(e))) : string(abs(e)) # 1.0 => 1
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

z = -3.0e-8 + 0.0im*ω^16 + 1.9e-7 + 0.0im*ω^15 + -1.32e-6 + 0.0im*ω^14 + 8.55e-6 + 0.0im*ω^13 + -5.131e-5 + 0.0im*ω^12 + 0.00028219 + 0.0im*ω^11 + -0.00141093 + 0.0im*ω^10 + 0.00634921 + 0.0im*ω^9 + -0.02539683 + 0.0im*ω^8 + 0.08888889 + 0.0im*ω^7 + -0.26666667 + 0.0im*ω^6 + 0.66666667 + 0.0im*ω^5 + -1.33333333 + 0.0im*ω^4 + 2ω^3 + -2ω² + ω
println(z)

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
abs(x::Hyper)::Hyper = [(abs(r), e) for (r, e) in x.terms]

# Helper: construct scalar multiple of ε or ω ??
# εr(r::Real) = [(r, -1.0)]
# ωr(r::Real) = [(r, 1.0)]

# Proximity relations

near(x::Hyper, y::Hyper) = isinfinitesimal(x - y)
near(x::Vector{Tuple{Float64, Float64}}, y::Hyper) = near(Hyper(x), y)
near(x::Hyper, y::Vector{Tuple{Float64, Float64}}) = near(x, Hyper(y))

cofinite(x::Hyper, y::Hyper) = isfinite(x - y)

# ~(x::Hyper, y::Hyper) = near(x, y) use ⩯ for exact nearness
~(x::Hyper, y::Hyper) = near(round(x), round(y)) 
~(x::Hyper, y::Real) = x ~ Hyper(y)
~(x::Real, y::Hyper) = Hyper(x)~(y)
~(x::Int, y::Hyper) = Hyper(x)~(y)
~(x::Real, y::Real) = round(x) ≈ round(y)
~(x::Number, y::Number) = round(x)≈round(y)

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

function lead(x::Hyper)::Hyper
    if length(x.terms) <= 1 return x end
    sorted = order(x).terms
    return Hyper([sorted[1]])
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
        return quote
            res1 = $(esc(lhs))
            res2 = $(esc(rhs))
            if !(res1 ~ res2)
                msg = """
                FAILED @asserts $(string($(QuoteNode(lhs)))) == $(string($(QuoteNode(rhs))))
                Left: $(res1)Right: $(res2)
                # Left:  $(raw(res1))
                # Right: $(raw(res2))
                """
                # Left:  $(round(simplify(order(res1))))Right: $(round(simplify(order(res2))))
                println(msg) # assert again to get the line number
                # throw(AssertionError(msg))
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
@assert lead(√(ε + ω)) ~ 2e-20ω^17  # Hyper[(1/2ⁿn!,n)] in limit?    TODO: changes with precision
@assert least(√(ε + ω)) ~ 1

# @assert √ω^2 ~ ω # TODO 
# @asserts √(ω^2) ~ ω # same
# @assert (√ω)^2 ~ ω # TODO 
@assert √ω ~ ω^.5 # definition
@assert √ω ~ ω^(1/2) # same

isless(x::Int64, y::Hyper) = Hyper(x)<y
isless(x::Hyper, y::Int64) = x<Hyper(y)
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

# println("isless(ε, ω) is ", isless(ε, ω))
# println("isless(ω, ε) is ", isless(ω, ε))
println("isless(0,ε) is ", isless(0,ε))
@assert 0<ε
@assert 0>-ε

@assert ε<ω
@assert 1<ω
@assert ε<1

@assert ε>-ω
@assert 1>-ω
@assert ε>-1
@assert ε < 1

println("√")
println(√(2+ε)) 
println("√(2+ε)*√(2+ε) = ",√(2+ε)*√(2+ε))
@asserts √(2+ε)*√(2+ε) ~ 2+ε
@assert √(2+ε)*√(2+ε) ~ 2+ε
# @assert √(2+ε)*√(2+ε) ≈ 2+ε   # if ≈ like ~
# @assert √(2+ε)*√(2+ε) == 2+ε  # never!
@assert (√(2+ε))^2 ~ 2+ε




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

function denoise(x::Hyper; ω_cutoff=1e-12)
    Hyper([(r,e) for (r,e) in x.terms if !(e > 0.0 && abs(r) < ω_cutoff)])
end


#  Julia doesn’t allow users to subtype Function directly, so we need to wrap our Closure (for print etc)
struct Closure{F} 
    fun::F
    name::Symbol
end
guessname(f::Function) = Symbol(string(f))
guessname(f::Closure) = f.name
Closure(f::F) where {F} = Closure(f, guessname(f))
# Closure(f::F) where {F} = Closure(f, :unknown)


# ∂(f::Function) = f'
# ∂(f::Function) = x -> f(x) - f(x-ε) / (ε) # backward difference
# ∂(f::Function) = x -> f(x+ε) - f(x-ε) / (2*ε) # central difference
# ∂(f::Function) = x -> simplify( (f(x+ε) - f(x)) / ε )
# ∂(f::Function) = x -> simplify((f(x+ε) - f(x-ε)) / (2ε))
∂(f::Function) = Closure(x -> simplify((f(x+ε) - f(x-ε)) / (2ε)), guessname(f))
∂(c::Closure) = Closure(x -> simplify((c(x+ε) - c(x-ε)) / (2ε)))
# ∂(f::Function) = x -> denoise(simplify((f(x+ε) - f(x-ε)) / (2ε)))

# (w::∂Wrapper)(x) = simplify((w(x + ε) - w(x - ε)) / (2ε))
# Base.show(io::IO, w::∂Wrapper) = print(io, "∂(", w.f, ")")
(c::Closure)(x) = c.fun(x)
Base.show(io::IO, w::Closure) = print(io, "ƒ(", w.name, ")")
Base.convert(::Type{Closure}, f::Function) = Closure(f)
Base.promote_rule(::Type{Function}, ::Type{Closure}) = Function
Base.promote_rule(::Type{Closure}, ::Type{Function}) = Function
Base.:+(f::Function, g::Closure) = x -> f(x) + g(x)
Base.:+(f::Closure, g::Function) = x -> f(x) + g(x)


# should follow from definitions of ∫ and ∂ if we treat number h as constant function h(x)=h
∂(x::Hyper) = Hyper([(r, e-1) for (r, e) in x.terms])
∂(x::Real) = 𝟘 # ∂1=0  

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
end
# @asserts dsquare(0.0) ~ 0  # -3.685e-10ω^18  + 2ω^3 + -2ω² + ω   TODO: bug / numeric instability
# @assert dsquare(0.0) ~ 0  # Infinity!
@assert dsquare(0.0) ~ 0 # OK IFF using central derivative
# @assert dsquare(ϵ) ~ 0  # OK IFF NOT using central derivative
@assert dsquare(1.0) ~ 2  
@assert dsquare(2.0) ~ 4 
@assert dsquare(2.5) ~ 5
@asserts dsquare(3.0) ~ 6
@assert dsquare(3.0) ~ 6


# using Plots
# plot(square, -5, 5, label="x²")
# plot!(dsquare, 1, 5, label="∂x²/∂x", linestyle=:dash)
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
# @assert ∂(square) ≈ x -> 2.0
# @assert ∂(square) ≈ 2x
# @assert ∂(square)(x::Hyper) == 2x



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

plot_ascii(square; xlim=(-π, π))
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

plot_ascii(∂(sin); xlim=(-π, π))

Base.show(io::IO, f::Function) = begin
    T = typeof(f)
    if T.name.wrapper && occursin("#", string(T.name.wrapper)) && fieldcount(T) == 1
        inner = getfield(f, 1)
        println(io, "∂(", nameof(inner), ")")
    else
        println(io, "∂(f)")
    end
end

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
step(x) = x > 0 # aka positive, heaviside, unitstep …
step0(x) = x >= 0 # aka positive, heaviside, unitstep …
plot_ascii(step; xlim=(-5, 5))
@assert step(1) == 1
@assert step(-1) == 0
@assert step(0) == 0
@assert step0(0) == 1
@assert step(ε) == 1
@assert step(-ε) == 0
@assert ∂(step)(1) ≈ 0
@assert ∂(step)(-1) ≈ 0
@assert ∂(step)(2ε) ≈ 0
@assert ∂(step)(-2ε) ≈ 0
@assert ∂(step)(ε) ~ ω/2 # FOR central derivative
# @assert ∂(step)(-ε) ~ ω/2 # Todo [(0.5 + 0.0im, 1.0)] OK!? why does it fail??
@assert ∂(step)(0) ~ ω/2
@assert ∂(step0)(0) ~ ω/2
@assert ∂(step) ≈ x -> x==0 ? ω/2 : 0
# @assert ∂(step) ≈ 0 # except for x==0 ! Todo ≈ exact vs approximate without null set

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
∫(f::Function) = Closure(x -> f(x+ε) * ε - f(x))
∫(c::Closure) = Closure(x -> c(x+ε) * ε - c(x))
# ∫(f::Function) = x -> ∑(i in xω) f(x+i) * ε
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