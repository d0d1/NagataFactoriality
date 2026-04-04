import NagataFactoriality.Nagata.Lemmas

namespace NagataFactoriality

theorem nagata_theorem {α : Type _} [CommRing α] [IsDomain α] [IsNoetherianRing α]
    (S : MultSet α)
    (hS : MultSet.GeneratedByPrimes S)
    (hUFD : UFD (α := Localization S)) :
    UFD (α := α) := by
  exact ufd_of_factorization_and_primes
    (hasFactorization_of_noetherian (α := α))
    (fun p hp => nagata_key_lemma (S := S) hS hUFD hp)

theorem ufd_of_factorization_and_prime_irreducibles {α : Type _} [CommRing α] [IsDomain α]
    (hfac : HasFactorization (α := α))
    (hprime : ∀ p : α, Irreducible p → Prime p) : UFD (α := α) :=
  ufd_of_factorization_and_primes hfac hprime

end NagataFactoriality
