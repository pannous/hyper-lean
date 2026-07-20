import Hyper.HyperClass

/-!
Basic hyperreal identities, stated once against the `IsHyperReal` interface
(`Hyper/HyperClass.lean`) and therefore valid for *every* concrete model that
instantiates it — `HyperList`, or any future backend — without this file
knowing whether `eps`/`omega` are lists, functions, or opaque axioms.

Concrete backends only need to provide `instance : IsHyperReal α` once (see
`Hyper/HyperReal.lean` for the current reference model); everything below
then applies to them for free.
-/

namespace Hyper.Basics

open IsHyperReal

variable {α : Type} [Zero α] [One α] [Add α] [Mul α] [Neg α] [Sub α] [LT α] [LE α]
  [IsHyperReal α]

example : (eps : α) + eps = (1 + 1) * eps := eps_add_eps
example : (eps : α) + eps + eps = (1 + 1 + 1) * eps := eps_add_eps_add_eps
example : (omega : α) + omega = (1 + 1) * omega := omega_add_omega

example : (eps : α) - eps = 0 := eps_sub_eps
example : -(eps : α) + eps = 0 := neg_eps_add_eps
example : (eps : α) + 0 = eps := eps_add_zero
example : (0 : α) + omega = omega := zero_add_omega

example : (eps : α) * omega = 1 := eps_mul_omega
example : (omega : α) * eps = 1 := omega_mul_eps
example : (eps : α) * omega = omega * eps := eps_omega_comm

example : (0 : α) < eps := eps_pos
example : (eps : α) < 1 := eps_lt_one
example : (eps : α) < omega := eps_lt_omega
example : (eps : α) * eps < eps := eps_sq_lt_eps

example : (eps : α) ≠ omega := eps_ne_omega
example : (eps : α) ≠ 0 := eps_ne_zero
example : (eps : α) ≠ 1 := eps_ne_one
example : (eps : α) * eps ≠ eps := eps_sq_ne_eps

end Hyper.Basics
