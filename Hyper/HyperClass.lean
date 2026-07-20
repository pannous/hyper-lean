/-!
`IsHyperReal` — the implementation-independent interface every concrete
hyperreal model (`HyperList`, `HyperGeneral`, `HyperFun`, ...) is expected to
satisfy: two distinguished elements `eps`/`omega` and the handful of defining
facts about them (positivity, gauging, infinitesimality vs. `1`).

Anything provable from these fields alone (see `Hyper/HyperBasics.lean`) is
proved exactly once and holds for every backend that supplies an instance —
the proof never inspects how `eps`/`omega`/`+`/`*` are represented.

Ring-level facts (`add_comm`, `mul_assoc`, ...) are deliberately NOT required
here: several backends still carry `sorry`s in their `Field`/`CommRing`
instances (see task "close Field-instance sorries"), so bundling that
machinery into this interface would make it unusable today. `IsHyperReal`
only assumes the raw operations (`Add`, `Mul`, ...) resolve, plus the small,
concrete (hence backend-checkable, e.g. via `native_decide`) facts below.
-/

class IsHyperReal (α : Type) [Zero α] [One α] [Add α] [Mul α] [Neg α] [Sub α]
    [LT α] [LE α] where
  /-- the canonical infinitesimal -/
  eps : α
  /-- the canonical infinite, gauged so that `eps * omega = 1` -/
  omega : α
  eps_pos : (0 : α) < eps
  eps_lt_one : eps < (1 : α)
  eps_lt_omega : eps < omega
  eps_sq_lt_eps : eps * eps < eps
  eps_mul_omega : eps * omega = 1
  omega_mul_eps : omega * eps = 1
  eps_add_eps : eps + eps = (1 + 1) * eps
  eps_add_eps_add_eps : eps + eps + eps = (1 + 1 + 1) * eps
  omega_add_omega : omega + omega = (1 + 1) * omega
  eps_sub_eps : eps - eps = 0
  neg_eps_add_eps : -eps + eps = 0
  eps_add_zero : eps + (0 : α) = eps
  zero_add_omega : (0 : α) + omega = omega
  eps_sq_ne_eps : eps * eps ≠ eps
  eps_ne_zero : eps ≠ (0 : α)
  eps_ne_omega : eps ≠ omega
  eps_ne_one : eps ≠ (1 : α)

/-!
Note: `eps_ne_zero`/`eps_ne_omega`/`eps_ne_one` are listed as fields (not
derived from `eps_pos`/`eps_lt_omega`/`eps_lt_one` via e.g. `ne_of_lt`)
because that derivation needs `<` to be irreflexive, which in turn needs a
`Preorder`/`LinearOrder` instance — several backends only have raw `LT`/`LE`
so far (their full order instance is separate, tracked work). Once a backend
proves `Preorder`/`LinearOrder`, these three fields could be dropped in
favour of the derivation without changing any downstream proof.
-/

namespace IsHyperReal

variable {α : Type} [Zero α] [One α] [Add α] [Mul α] [Neg α] [Sub α] [LT α] [LE α]
  [IsHyperReal α]

/-- `ε` and `ω` commute with each other — genuinely derived from the two
gauging axioms alone, no `mul_comm`/`CommRing` needed. This is the shape of
fact this file is *for*: every backend gets it for free the moment it
supplies `eps_mul_omega`/`omega_mul_eps`, without proving it itself. -/
theorem eps_omega_comm : (eps : α) * omega = omega * eps := by
  rw [eps_mul_omega, omega_mul_eps]

end IsHyperReal

/-!
### Migration candidates

Facts currently listed as raw *fields* above but that are really consequences
of more basic structure, once a backend has it:

- `eps_ne_zero`/`eps_ne_omega`/`eps_ne_one` — derivable from `eps_pos`/
  `eps_lt_omega`/`eps_lt_one` given `<` irreflexive (needs `Preorder`).
- `eps_sub_eps`/`neg_eps_add_eps` — both instances of `sub_self`/
  `neg_add_cancel`, i.e. free from any `AddGroup` instance.
- `eps_add_zero`/`zero_add_omega` — instances of `add_zero`/`zero_add` from
  any `AddMonoid` instance.
- `eps_add_eps`/`eps_add_eps_add_eps`/`omega_add_omega` — instances of
  `two_mul`/distributivity from any `Semiring`/`Ring` instance.

None of that ring/order machinery is required *yet* because backends still
carry `sorry`s in their algebraic instances (see task "close Field-instance
sorries"). As those get filled in, prefer moving a fact from this class's
field list into a `theorem` derived from the weaker Mathlib class it actually
follows from (as `eps_omega_comm` above does today) — that shrinks the
per-backend proof burden without touching `Hyper/HyperBasics.lean`, since
`IsHyperReal.foo` resolves the same way whether `foo` is a field or a
`theorem`. Conversely, if a fact turns out to need real backend-specific
knowledge no weaker class can supply, it belongs back as a field.
-/
