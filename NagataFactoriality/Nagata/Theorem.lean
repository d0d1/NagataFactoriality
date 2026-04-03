import NagataFactoriality.Nagata.Lemmas

namespace NagataFactoriality

/-
This file currently packages the UFD criterion that the full Nagata localization
argument is meant to establish. A faithful proof of Nagata's theorem still
requires a substantially larger localization and ideal-theory development.
-/
theorem ufd_of_factorization_and_prime_irreducibles {α : Type _} [IntegralDomain α]
    (hfac : HasFactorization (α := α))
    (hprime : ∀ p : α, Irreducible p → Prime p) : UFD (α := α) :=
  ⟨hfac, hprime⟩

end NagataFactoriality
