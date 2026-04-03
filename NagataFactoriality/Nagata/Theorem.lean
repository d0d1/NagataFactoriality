import NagataFactoriality.Nagata.Lemmas

namespace NagataFactoriality

theorem nagata_theorem {α : Type _} [IntegralDomain α]
    (S : MultSet α)
    (hNoeth : NoetherianRing α)
    (hS : MultSet.GeneratedByPrimes S)
    (hUFD : UFD (α := Localization S)) :
    UFD (α := α) := by
  refine ⟨hNoeth.hasFactorization, ?_⟩
  intro p hp
  exact nagata_key_lemma (S := S) hS hUFD hp

theorem ufd_of_factorization_and_prime_irreducibles {α : Type _} [IntegralDomain α]
    (hfac : HasFactorization (α := α))
    (hprime : ∀ p : α, Irreducible p → Prime p) : UFD (α := α) :=
  ⟨hfac, hprime⟩

end NagataFactoriality
