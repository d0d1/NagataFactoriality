import NagataFactoriality.Localization.Properties
import NagataFactoriality.Basic.UFD

namespace NagataFactoriality

theorem ufd_irreducible_iff_prime {α : Type _} [IntegralDomain α]
    (h : UFD (α := α)) {p : α} : Irreducible p ↔ Prime p := by
  exact (prime_iff_irreducible_of_ufd h (p := p)).symm

end NagataFactoriality
