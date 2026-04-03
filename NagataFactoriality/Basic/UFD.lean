import NagataFactoriality.Basic.Noetherian

namespace NagataFactoriality

theorem ufd_iff_factorization_and_irreducibles_prime {α : Type _} [IntegralDomain α] :
    UFD (α := α) ↔ HasFactorization (α := α) ∧ ∀ p : α, Irreducible p → Prime p := Iff.rfl

theorem UFD.hasFactorization {α : Type _} [IntegralDomain α] (h : UFD (α := α)) :
    HasFactorization (α := α) :=
  h.1

theorem UFD.prime_of_irreducible {α : Type _} [IntegralDomain α]
    (h : UFD (α := α)) {p : α} (hp : Irreducible p) : Prime p :=
  h.2 p hp

theorem prime_iff_irreducible_of_ufd {α : Type _} [IntegralDomain α]
    (h : UFD (α := α)) {p : α} : Prime p ↔ Irreducible p := by
  constructor
  · exact prime_irreducible
  · intro hp
    exact h.2 p hp

theorem ufd_of_factorization_and_primes {α : Type _} [IntegralDomain α]
    (hfac : HasFactorization (α := α))
    (hprime : ∀ p : α, Irreducible p → Prime p) : UFD (α := α) :=
  ⟨hfac, hprime⟩

end NagataFactoriality
