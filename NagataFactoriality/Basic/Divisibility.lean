import NagataFactoriality.Basic.Ring

open Lean.Grind

namespace NagataFactoriality

def dvd {α : Type _} [CommRing α] (a b : α) : Prop := ∃ c, b = a * c

def listProd {α : Type _} [CommRing α] : List α → α
  | [] => 1
  | a :: as => a * listProd as

@[simp] theorem listProd_nil {α : Type _} [CommRing α] : listProd ([] : List α) = 1 := rfl

@[simp] theorem listProd_cons {α : Type _} [CommRing α] (a : α) (as : List α) :
    listProd (a :: as) = a * listProd as := rfl

theorem listProd_append {α : Type _} [CommRing α] (xs ys : List α) :
    listProd (xs ++ ys) = listProd xs * listProd ys := by
  induction xs with
  | nil =>
      simp [listProd, Semiring.one_mul]
  | cons x xs ih =>
      simp [listProd, ih, Semiring.mul_assoc]

theorem dvd_refl {α : Type _} [CommRing α] (a : α) : dvd a a := by
  refine ⟨1, ?_⟩
  grind

theorem dvd_trans {α : Type _} [CommRing α] {a b c : α} :
    dvd a b → dvd b c → dvd a c := by
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  refine ⟨u * v, ?_⟩
  grind

theorem dvd_mul_of_dvd_left {α : Type _} [CommRing α] {a b c : α} :
    dvd a b → dvd a (b * c) := by
  rintro ⟨u, hu⟩
  refine ⟨u * c, ?_⟩
  grind

theorem dvd_mul_of_dvd_right {α : Type _} [CommRing α] {a b c : α} :
    dvd a c → dvd a (b * c) := by
  rintro ⟨u, hu⟩
  refine ⟨b * u, ?_⟩
  grind

def IsUnit {α : Type _} [CommRing α] (a : α) : Prop := ∃ b, a * b = 1

theorem isUnit_one {α : Type _} [CommRing α] : IsUnit (1 : α) := by
  refine ⟨1, ?_⟩
  grind

theorem isUnit_mul {α : Type _} [CommRing α] {a b : α} :
    IsUnit a → IsUnit b → IsUnit (a * b) := by
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  refine ⟨u * v, ?_⟩
  grind

theorem isUnit_of_dvd_one {α : Type _} [CommRing α] {a : α} (h : dvd a 1) : IsUnit a := by
  rcases h with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  simpa [CommSemiring.mul_comm] using hu.symm

theorem isUnit_ne_zero {α : Type _} [IntegralDomain α] {a : α} (ha : IsUnit a) : a ≠ 0 := by
  intro h0
  rcases ha with ⟨b, hb⟩
  have h1 : (0 : α) = 1 := by
    grind
  exact IntegralDomain.zero_ne_one h1

def Associated {α : Type _} [CommRing α] (a b : α) : Prop := ∃ u, IsUnit u ∧ b = a * u

theorem associated_refl {α : Type _} [CommRing α] (a : α) : Associated a a := by
  refine ⟨1, isUnit_one, ?_⟩
  grind

theorem associated_symm {α : Type _} [CommRing α] {a b : α} :
    Associated a b → Associated b a := by
  rintro ⟨u, ⟨v, huv⟩, hab⟩
  refine ⟨v, ?_, ?_⟩
  · refine ⟨u, ?_⟩
    grind
  · grind

theorem associated_trans {α : Type _} [CommRing α] {a b c : α} :
    Associated a b → Associated b c → Associated a c := by
  rintro ⟨u, hu, hab⟩ ⟨v, hv, hbc⟩
  refine ⟨u * v, isUnit_mul hu hv, ?_⟩
  grind

def Irreducible {α : Type _} [IntegralDomain α] (p : α) : Prop :=
  p ≠ 0 ∧ ¬ IsUnit p ∧ ∀ a b : α, p = a * b → IsUnit a ∨ IsUnit b

def Prime {α : Type _} [IntegralDomain α] (p : α) : Prop :=
  p ≠ 0 ∧ ¬ IsUnit p ∧ ∀ a b : α, dvd p (a * b) → dvd p a ∨ dvd p b

def HasFactorization {α : Type _} [IntegralDomain α] : Prop :=
  ∀ a : α, a ≠ 0 → ¬ IsUnit a →
    ∃ factors : List α, listProd factors = a ∧ ∀ p : α, p ∈ factors → Irreducible p

def UFD {α : Type _} [IntegralDomain α] : Prop :=
  HasFactorization (α := α) ∧ ∀ p : α, Irreducible p → Prime p

theorem prime_irreducible {α : Type _} [IntegralDomain α] {p : α} (hp : Prime p) :
    Irreducible p := by
  rcases hp with ⟨hp0, hpnu, hpdiv⟩
  refine ⟨hp0, hpnu, ?_⟩
  intro a b hab
  have hprod : dvd p (a * b) := by
    refine ⟨1, ?_⟩
    grind
  rcases hpdiv a b hprod with hpa | hpb
  · rcases hpa with ⟨c, hc⟩
    right
    refine ⟨c, ?_⟩
    have hcancel : p * 1 = p * (c * b) := by
      grind
    have hone : 1 = c * b := IntegralDomain.mul_left_cancel₀ hp0 hcancel
    grind
  · rcases hpb with ⟨c, hc⟩
    left
    refine ⟨c, ?_⟩
    have hcancel : p * 1 = p * (a * c) := by
      grind
    have hone : 1 = a * c := IntegralDomain.mul_left_cancel₀ hp0 hcancel
    grind

theorem associated_of_irreducible_of_dvd {α : Type _} [IntegralDomain α] {p q : α}
    (hp : Irreducible p) (hq : Irreducible q) (hdiv : dvd p q) : Associated p q := by
  rcases hdiv with ⟨c, hc⟩
  refine ⟨c, ?_, hc⟩
  rcases hp with ⟨_, hpnu, _⟩
  rcases hq with ⟨_, _, hqirr⟩
  have hfact : q = p * c := by simpa [CommSemiring.mul_comm] using hc
  rcases hqirr p c hfact with hpunit | hcunit
  · exact False.elim (hpnu hpunit)
  · exact hcunit

theorem prime_of_associated {α : Type _} [IntegralDomain α] {p q : α}
    (hp : Prime p) (hassoc : Associated p q) : Prime q := by
  rcases hp with ⟨hp0, hpnu, hpdiv⟩
  rcases hassoc with ⟨u, hu, hq⟩
  rcases hu with ⟨v, huv⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hq0
    have hu0 : u ≠ 0 := isUnit_ne_zero ⟨v, huv⟩
    have hpzero : p = 0 := by
      apply IntegralDomain.mul_right_cancel₀ hu0
      grind
    exact hp0 hpzero
  · intro hqu
    apply hpnu
    rcases hqu with ⟨w, hqw⟩
    refine ⟨u * w, ?_⟩
    have : p * (u * w) = 1 := by
      calc
        p * (u * w) = (p * u) * w := by grind
        _ = q * w := by rw [hq]
        _ = 1 := hqw
    simpa [Semiring.mul_assoc] using this
  · intro a b hqdiv
    rcases hqdiv with ⟨c, hqc⟩
    have hpab : dvd p (a * b) := by
      refine ⟨u * c, ?_⟩
      grind
    rcases hpdiv a b hpab with hpa | hpb
    · rcases hpa with ⟨d, hd⟩
      left
      refine ⟨v * d, ?_⟩
      have hmul : q * (v * d) = a := by
        calc
          q * (v * d) = (p * u) * (v * d) := by rw [hq]
          _ = p * (u * (v * d)) := by grind
          _ = p * ((u * v) * d) := by grind
          _ = p * (1 * d) := by rw [huv]
          _ = a := by grind
      simpa [Semiring.mul_assoc] using hmul.symm
    · rcases hpb with ⟨d, hd⟩
      right
      refine ⟨v * d, ?_⟩
      have hmul : q * (v * d) = b := by
        calc
          q * (v * d) = (p * u) * (v * d) := by rw [hq]
          _ = p * (u * (v * d)) := by grind
          _ = p * ((u * v) * d) := by grind
          _ = p * (1 * d) := by rw [huv]
          _ = b := by grind
      simpa [Semiring.mul_assoc] using hmul.symm

end NagataFactoriality
