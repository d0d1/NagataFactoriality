import NagataFactoriality.Nagata.Lemmas

namespace NagataFactoriality

theorem nagata_theorem {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (S : Submonoid R) (hS : PrimeGenerated S)
    (hUFD :
      @UniqueFactorizationMonoid (Localization S)
        (by
          letI : Fact ((0 : R) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
          infer_instance)) :
    UniqueFactorizationMonoid R := by
  letI : Fact ((0 : R) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
  exact ufd_of_factorization_and_primes
    (hasFactorization_of_noetherian (α := R))
    (fun p hp => nagata_key_lemma_primeGenerated (S := S) hS hUFD hp)

theorem nagata_theorem_of_prime_or_unit {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (S : Submonoid R) (hS : ∀ s ∈ S, Prime s ∨ IsUnit s)
    (hUFD :
      @UniqueFactorizationMonoid (Localization S)
        (by
          letI : Fact ((0 : R) ∉ S) := ⟨Submonoid.zero_notMem_of_prime_or_unit hS⟩
          infer_instance)) :
    UniqueFactorizationMonoid R := by
  letI : Fact ((0 : R) ∉ S) := ⟨Submonoid.zero_notMem_of_prime_or_unit hS⟩
  exact ufd_of_factorization_and_primes
    (hasFactorization_of_noetherian (α := R))
    (fun p hp => nagata_key_lemma (S := S) hS hUFD hp)

theorem ufd_of_factorization_and_prime_irreducibles {α : Type*} [CommRing α] [IsDomain α]
    (hfac : WfDvdMonoid α)
    (hprime : ∀ p : α, Irreducible p → Prime p) :
    UniqueFactorizationMonoid α :=
  ufd_of_factorization_and_primes hfac hprime

end NagataFactoriality
