import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import NagataFactoriality.Basic.Noetherian

namespace NagataFactoriality

theorem ufd_iff_factorization_and_irreducibles_prime {α : Type*} [CommRing α] [IsDomain α] :
    UFD (α := α) ↔ HasFactorization (α := α) ∧ ∀ p : α, Irreducible p → Prime p := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · letI : UniqueFactorizationMonoid α := h
      exact (inferInstance : WfDvdMonoid α)
    · intro p hp
      letI : UniqueFactorizationMonoid α := h
      exact (UniqueFactorizationMonoid.irreducible_iff_prime).mp hp
  · rintro ⟨hfac, hprime⟩
    exact UniqueFactorizationMonoid.of_exists_prime_factors (fun a ha => by
      letI : WfDvdMonoid α := hfac
      obtain ⟨f, hf, hassoc⟩ := WfDvdMonoid.exists_factors a ha
      refine ⟨f, ?_, hassoc⟩
      intro b hb
      exact hprime b (hf b hb))

theorem UFD.hasFactorization {α : Type*} [CommRing α] [IsDomain α] (h : UFD (α := α)) :
    HasFactorization (α := α) := by
  letI : UniqueFactorizationMonoid α := h
  exact (inferInstance : WfDvdMonoid α)

theorem UFD.prime_of_irreducible {α : Type*} [CommRing α] [IsDomain α]
    (h : UFD (α := α)) {p : α} (hp : Irreducible p) : Prime p := by
  letI : UniqueFactorizationMonoid α := h
  exact (UniqueFactorizationMonoid.irreducible_iff_prime).mp hp

theorem prime_iff_irreducible_of_ufd {α : Type*} [CommRing α] [IsDomain α]
    (h : UFD (α := α)) {p : α} : Prime p ↔ Irreducible p := by
  letI : UniqueFactorizationMonoid α := h
  exact UniqueFactorizationMonoid.irreducible_iff_prime.symm

theorem ufd_of_factorization_and_primes {α : Type*} [CommRing α] [IsDomain α]
    (hfac : HasFactorization (α := α))
    (hprime : ∀ p : α, Irreducible p → Prime p) : UFD (α := α) := by
  exact (ufd_iff_factorization_and_irreducibles_prime (α := α)).2 ⟨hfac, hprime⟩

end NagataFactoriality
