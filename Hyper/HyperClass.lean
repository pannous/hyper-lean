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
