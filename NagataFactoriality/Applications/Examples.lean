import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization

namespace NagataFactoriality

open Polynomial

theorem int_uniqueFactorizationMonoid : UniqueFactorizationMonoid ℤ := by
  infer_instance

theorem int_polynomial_uniqueFactorizationMonoid : UniqueFactorizationMonoid ℤ[X] := by
  infer_instance

theorem mvPolynomial_uniqueFactorizationMonoid (n : ℕ) (k : Type*) [Field k] :
    UniqueFactorizationMonoid (MvPolynomial (Fin n) k) := by
  infer_instance

theorem iterated_polynomial_uniqueFactorizationMonoid (k : Type*) [Field k] :
    UniqueFactorizationMonoid (Polynomial (Polynomial k)) := by
  infer_instance

end NagataFactoriality
