import NagataFactoriality.Localization.Properties
import NagataFactoriality.Basic.UFD

namespace NagataFactoriality

theorem ufd_irreducible_iff_prime {α : Type _} [IntegralDomain α]
    (h : UFD (α := α)) {p : α} : Irreducible p ↔ Prime p := by
  exact (prime_iff_irreducible_of_ufd h (p := p)).symm

def Avoids {α : Type _} [IntegralDomain α] (S : MultSet α) (p : α) : Prop :=
  ∀ s : α, S s → ¬ dvd p s

theorem localization_of_eq_zero_iff {α : Type _} [IntegralDomain α] {S : MultSet α} (a : α) :
    Localization.of (S := S) a = (Zero.zero : Localization S) ↔ a = 0 := by
  constructor
  · intro h
    exact (Localization.of_eq_iff (S := S) a 0).mp (by simpa [Localization.of_zero (S := S)] using h)
  · intro h
    subst h
    exact Localization.of_zero (S := S)

theorem localization_mk_mul_of {α : Type _} [IntegralDomain α] {S : MultSet α}
    (a b s : α) (hs : S s) :
    Localization.mk (S := S) (a * b) s hs =
      Localization.mk (S := S) a s hs * Localization.of (S := S) b := by
  exact Localization.mk_mul_of (S := S) a b s hs

theorem localization_isUnit_of_mem {α : Type _} [IntegralDomain α] {S : MultSet α}
    {s : α} (hs : S s) : IsUnit (Localization.of (S := S) s) := by
  exact Localization.isUnit_of_mem (S := S) hs

theorem localization_isUnit_mk_of_mem {α : Type _} [IntegralDomain α] {S : MultSet α}
    {a s : α} (ha : S a) (hs : S s) : IsUnit (Localization.mk (S := S) a s hs) := by
  exact Localization.isUnit_mk_of_mem (S := S) ha hs

theorem localization_isUnit_of_isUnit {α : Type _} [IntegralDomain α] {S : MultSet α}
    {a : α} (ha : IsUnit a) : IsUnit (Localization.of (S := S) a) := by
  exact Localization.isUnit_of_isUnit (S := S) ha

theorem generatedByPrimes_to_list {α : Type _} [IntegralDomain α] {S : MultSet α}
    (hS : MultSet.GeneratedByPrimes S) {s : α} (hs : S s) :
    ∃ qs : List α, listProd qs = s ∧ ∀ q : α, q ∈ qs → S q ∧ Prime q := by
  exact MultSet.generatedBy_to_list (hS s hs)

theorem prime_of_irreducible_of_dvd_listProd_primes {α : Type _} [IntegralDomain α]
    {qs : List α} {p : α} (hp : Irreducible p)
    (hqs : ∀ q : α, q ∈ qs → Prime q) (hdiv : dvd p (listProd qs)) : Prime p := by
  induction qs generalizing p with
  | nil =>
      exfalso
      exact hp.2.1 (isUnit_of_dvd_one (by simpa using hdiv))
  | cons q qs ih =>
      have hq : Prime q := hqs q (by simp)
      rcases hdiv with ⟨c, hc⟩
      have hqdiv : dvd q (p * c) := by
        refine ⟨listProd qs, ?_⟩
        simpa [listProd] using hc.symm
      rcases hq.2.2 p c hqdiv with hqp | hqc
      · have hqirr : Irreducible q := prime_irreducible hq
        have hassoc : Associated q p := associated_of_irreducible_of_dvd hqirr hp hqp
        exact prime_of_associated hq hassoc
      · rcases hqc with ⟨d, hd⟩
        have q0 : q ≠ 0 := hq.1
        have hrest : dvd p (listProd qs) := by
          refine ⟨d, ?_⟩
          have hcancel : q * listProd qs = q * (p * d) := by
            calc
              q * listProd qs = p * c := by simpa [listProd] using hc
              _ = p * (q * d) := by rw [hd]
              _ = q * (p * d) := by grind
          exact IntegralDomain.mul_left_cancel₀ q0 hcancel
        apply ih hp
        · intro r hr
          exact hqs r (by simp [hr])
        · exact hrest

theorem prime_of_irreducible_of_dvd_generated_primes {α : Type _} [IntegralDomain α]
    {S : MultSet α} (hS : MultSet.GeneratedByPrimes S) {p s : α}
    (hp : Irreducible p) (hs : S s) (hdiv : dvd p s) : Prime p := by
  rcases generatedByPrimes_to_list hS hs with ⟨qs, hqs, hprime⟩
  apply prime_of_irreducible_of_dvd_listProd_primes hp
  · intro q hq
    exact (hprime q hq).2
  · simpa [hqs] using hdiv

theorem dvd_of_mul_listProd_eq {α : Type _} [IntegralDomain α] {qs : List α} {a c p : α}
    (hp : Irreducible p) (havoid : ∀ q : α, q ∈ qs → ¬ dvd p q)
    (hqs : ∀ q : α, q ∈ qs → Prime q) (h : a * listProd qs = p * c) : dvd p a := by
  induction qs generalizing a c with
  | nil =>
      refine ⟨c, ?_⟩
      have h' : a = p * c := by
        grind [listProd]
      exact h'
  | cons q qs ih =>
      have hq : Prime q := hqs q (by simp)
      have hqdiv : dvd q (p * c) := by
        refine ⟨a * listProd qs, ?_⟩
        calc
          p * c = a * listProd (q :: qs) := h.symm
          _ = q * (a * listProd qs) := by simp [listProd]; grind
      rcases hq.2.2 p c hqdiv with hqp | hqc
      · exfalso
        have hqirr : Irreducible q := prime_irreducible hq
        have hassoc : Associated q p := associated_of_irreducible_of_dvd hqirr hp hqp
        exact havoid q (by simp) (dvd_of_associated (associated_symm hassoc))
      · rcases hqc with ⟨d, hd⟩
        have q0 : q ≠ 0 := hq.1
        have hrest : a * listProd qs = p * d := by
          have hcancel : q * (a * listProd qs) = q * (p * d) := by
            calc
              q * (a * listProd qs) = a * (q * listProd qs) := by grind
              _ = a * listProd (q :: qs) := by simp [listProd]
              _ = p * c := h
              _ = p * (q * d) := by rw [hd]
              _ = q * (p * d) := by grind
          exact IntegralDomain.mul_left_cancel₀ q0 hcancel
        apply ih
        · intro r hr
          exact havoid r (by simp [hr])
        · intro r hr
          exact hqs r (by simp [hr])
        · exact hrest

theorem split_listProd_primes_across_product {α : Type _} [IntegralDomain α] {S : MultSet α}
    {qs : List α} {a b p : α}
    (hqs : ∀ q : α, q ∈ qs → S q ∧ Prime q) (h : a * b = p * listProd qs) :
    ∃ xs ys : List α, ∃ a' b' : α,
      (∀ q : α, q ∈ xs → S q ∧ Prime q) ∧
      (∀ q : α, q ∈ ys → S q ∧ Prime q) ∧
      listProd qs = listProd xs * listProd ys ∧
      a = listProd xs * a' ∧
      b = listProd ys * b' ∧
      a' * b' = p := by
  induction qs generalizing a b p with
  | nil =>
      have hab : a * b = p := by
        grind [listProd]
      refine ⟨[], [], a, b, ?_, ?_, ?_, ?_, ?_, hab⟩
      · intro q hq
        simp at hq
      · intro q hq
        simp at hq
      · grind [listProd]
      · grind [listProd]
      · grind [listProd]
  | cons q qs ih =>
      have hqSq : S q := (hqs q (by simp)).1
      have hqPrime : Prime q := (hqs q (by simp)).2
      have hqdiv : dvd q (a * b) := by
        refine ⟨p * listProd qs, ?_⟩
        calc
          a * b = p * listProd (q :: qs) := h
          _ = p * (q * listProd qs) := by simp [listProd]
          _ = q * (p * listProd qs) := by grind
      rcases hqPrime.2.2 a b hqdiv with hqa | hqb
      · rcases hqa with ⟨d, hd⟩
        have q0 : q ≠ 0 := hqPrime.1
        have hrest : d * b = p * listProd qs := by
          have hcancel : q * (d * b) = q * (p * listProd qs) := by
            calc
              q * (d * b) = a * b := by rw [hd]; grind
              _ = p * listProd (q :: qs) := h
              _ = p * (q * listProd qs) := by simp [listProd]
              _ = q * (p * listProd qs) := by grind
          exact IntegralDomain.mul_left_cancel₀ q0 hcancel
        rcases ih (a := d) (b := b) (p := p)
            (fun r hr => hqs r (by simp [hr])) hrest with
          ⟨xs, ys, a', b', hxs, hys, hprod, ha, hb, hab⟩
        refine ⟨q :: xs, ys, a', b', ?_, hys, ?_, ?_, hb, hab⟩
        · intro r hr
          simp at hr
          rcases hr with rfl | hr
          · exact ⟨hqSq, hqPrime⟩
          · exact hxs r hr
        · calc
            listProd (q :: qs) = q * listProd qs := by simp [listProd]
            _ = q * (listProd xs * listProd ys) := by rw [hprod]
            _ = listProd (q :: xs) * listProd ys := by simp [listProd]; grind
        · calc
            a = q * d := hd
            _ = q * (listProd xs * a') := by rw [ha]
            _ = listProd (q :: xs) * a' := by simp [listProd]; grind
      · rcases hqb with ⟨d, hd⟩
        have q0 : q ≠ 0 := hqPrime.1
        have hrest : a * d = p * listProd qs := by
          have hcancel : q * (a * d) = q * (p * listProd qs) := by
            calc
              q * (a * d) = a * b := by rw [hd]; grind
              _ = p * listProd (q :: qs) := h
              _ = p * (q * listProd qs) := by simp [listProd]
              _ = q * (p * listProd qs) := by grind
          exact IntegralDomain.mul_left_cancel₀ q0 hcancel
        rcases ih (a := a) (b := d) (p := p)
            (fun r hr => hqs r (by simp [hr])) hrest with
          ⟨xs, ys, a', b', hxs, hys, hprod, ha, hb, hab⟩
        refine ⟨xs, q :: ys, a', b', hxs, ?_, ?_, ha, ?_, hab⟩
        · intro r hr
          simp at hr
          rcases hr with rfl | hr
          · exact ⟨hqSq, hqPrime⟩
          · exact hys r hr
        · calc
            listProd (q :: qs) = q * listProd qs := by simp [listProd]
            _ = q * (listProd xs * listProd ys) := by rw [hprod]
            _ = listProd xs * listProd (q :: ys) := by simp [listProd]; grind
        · calc
            b = q * d := hd
            _ = q * (listProd ys * b') := by rw [hb]
            _ = listProd (q :: ys) * b' := by simp [listProd]; grind

theorem localization_irreducible_of_irreducible {α : Type _} [IntegralDomain α] {S : MultSet α}
    (hS : MultSet.GeneratedByPrimes S) {p : α} (hp : Irreducible p)
    (havoid : Avoids S p) : Irreducible (Localization.of (S := S) p) := by
  refine ⟨?_, ?_, ?_⟩
  · change Localization.of (S := S) p ≠ (Zero.zero : Localization S)
    intro hp0
    exact hp.1 ((localization_of_eq_zero_iff (S := S) p).mp hp0)
  · intro hunit
    rcases hunit with ⟨x, hx⟩
    refine Quotient.inductionOn x ?_ hx
    intro a hxa
    change Quotient.mk (Fraction.relSetoid S) (Fraction.mul ⟨p, 1, S.one_mem⟩ a) =
        Quotient.mk (Fraction.relSetoid S) Fraction.one at hxa
    have hrel : Fraction.Rel (Fraction.mul ⟨p, 1, S.one_mem⟩ a) Fraction.one := Quotient.exact hxa
    have hdiv : dvd p a.den := by
      refine ⟨a.num, ?_⟩
      calc
        a.den = 1 * (1 * a.den) := by grind
        _ = (p * a.num) * 1 := by
          simpa [Fraction.Rel, Fraction.mul, Fraction.one] using hrel.symm
        _ = p * a.num := by grind
    exact havoid a.den a.den_mem hdiv
  · intro x y hxy
    refine Quotient.inductionOn₂ x y ?_ hxy
    intro a b hab
    change Quotient.mk (Fraction.relSetoid S) ⟨p, 1, S.one_mem⟩ =
        Quotient.mk (Fraction.relSetoid S) (Fraction.mul a b) at hab
    have hrel : Fraction.Rel ⟨p, 1, S.one_mem⟩ (Fraction.mul a b) := Quotient.exact hab
    have hsden : S (a.den * b.den) := S.mul_mem a.den_mem b.den_mem
    rcases generatedByPrimes_to_list hS hsden with ⟨qs, hqs, hprime⟩
    have hprod : a.num * b.num = p * listProd qs := by
      have h0 : p * (a.den * b.den) = a.num * b.num := by
        have h1 : p * (a.den * b.den) = a.num * b.num * 1 := by
          simpa [Fraction.Rel, Fraction.mul] using hrel
        grind
      calc
        a.num * b.num = p * (a.den * b.den) := h0.symm
        _ = p * listProd qs := by rw [hqs]
    rcases split_listProd_primes_across_product
        (S := S) (a := a.num) (b := b.num) (p := p)
        (qs := qs) (fun q hq => hprime q hq) hprod with
      ⟨xs, ys, a', b', hxs, hys, hsplit, ha, hb, habp⟩
    have hsx : S (listProd xs) := by
      apply MultSet.listProd_mem
      intro q hq
      exact (hxs q hq).1
    have hsy : S (listProd ys) := by
      apply MultSet.listProd_mem
      intro q hq
      exact (hys q hq).1
    rcases hp.2.2 a' b' habp.symm with haunit | hbunit
    · left
      change IsUnit (Localization.mk (S := S) a.num a.den a.den_mem)
      rw [ha]
      rw [localization_mk_mul_of (S := S) (listProd xs) a' a.den a.den_mem]
      exact isUnit_mul (localization_isUnit_mk_of_mem (S := S) hsx a.den_mem)
        (localization_isUnit_of_isUnit (S := S) haunit)
    · right
      change IsUnit (Localization.mk (S := S) b.num b.den b.den_mem)
      rw [hb]
      rw [localization_mk_mul_of (S := S) (listProd ys) b' b.den b.den_mem]
      exact isUnit_mul (localization_isUnit_mk_of_mem (S := S) hsy b.den_mem)
        (localization_isUnit_of_isUnit (S := S) hbunit)

theorem localization_prime_of_prime {α : Type _} [IntegralDomain α] {S : MultSet α}
    {p : α} (hp : Prime p) (havoid : Avoids S p) : Prime (Localization.of (S := S) p) := by
  refine ⟨?_, ?_, ?_⟩
  · change Localization.of (S := S) p ≠ (Zero.zero : Localization S)
    intro hp0
    exact hp.1 ((localization_of_eq_zero_iff (S := S) p).mp hp0)
  · intro hunit
    rcases hunit with ⟨x, hx⟩
    refine Quotient.inductionOn x ?_ hx
    intro a hxa
    change Quotient.mk (Fraction.relSetoid S) (Fraction.mul ⟨p, 1, S.one_mem⟩ a) =
        Quotient.mk (Fraction.relSetoid S) Fraction.one at hxa
    have hrel : Fraction.Rel (Fraction.mul ⟨p, 1, S.one_mem⟩ a) Fraction.one := Quotient.exact hxa
    have hdiv : dvd p a.den := by
      refine ⟨a.num, ?_⟩
      have h0 : p * a.num = a.den := by
        have h1 : p * a.num * 1 = 1 * (1 * a.den) := by
          simpa [Fraction.Rel, Fraction.mul, Fraction.one] using hrel
        grind
      exact h0.symm
    exact havoid a.den a.den_mem hdiv
  · intro x y hxy
    rcases hxy with ⟨z, hz⟩
    refine Quotient.inductionOn₃ x y z ?_ hz
    intro a b c hEq
    change Quotient.mk (Fraction.relSetoid S) (Fraction.mul a b) =
        Quotient.mk (Fraction.relSetoid S) (Fraction.mul ⟨p, 1, S.one_mem⟩ c) at hEq
    have hrel : Fraction.Rel (Fraction.mul a b) (Fraction.mul ⟨p, 1, S.one_mem⟩ c) :=
      Quotient.exact hEq
    have hdivabc : dvd p ((a.num * b.num) * c.den) := by
      refine ⟨c.num * (a.den * b.den), ?_⟩
      unfold Fraction.Rel Fraction.mul at hrel
      grind
    have hdivab : dvd p (a.num * b.num) := by
      rcases hp.2.2 (a.num * b.num) c.den hdivabc with hab | hc
      · exact hab
      · exact False.elim (havoid c.den c.den_mem hc)
    rcases hp.2.2 a.num b.num hdivab with ha | hb
    · left
      rcases ha with ⟨d, hd⟩
      refine ⟨Localization.mk (S := S) d a.den a.den_mem, ?_⟩
      apply Quotient.sound
      change Fraction.Rel a (Fraction.mul ⟨p, 1, S.one_mem⟩ ⟨d, a.den, a.den_mem⟩)
      unfold Fraction.Rel Fraction.mul
      grind
    · right
      rcases hb with ⟨d, hd⟩
      refine ⟨Localization.mk (S := S) d b.den b.den_mem, ?_⟩
      apply Quotient.sound
      change Fraction.Rel b (Fraction.mul ⟨p, 1, S.one_mem⟩ ⟨d, b.den, b.den_mem⟩)
      unfold Fraction.Rel Fraction.mul
      grind

theorem dvd_of_localization_dvd {α : Type _} [IntegralDomain α] {S : MultSet α}
    (hS : MultSet.GeneratedByPrimes S) {p a : α} (hp : Irreducible p) (havoid : Avoids S p)
    (hdiv : dvd (Localization.of (S := S) p) (Localization.of (S := S) a)) : dvd p a := by
  rcases (Localization.dvd_of_iff (S := S) (a := p) (b := a)).1 hdiv with ⟨s, hs, hsa⟩
  rcases hsa with ⟨c, hc⟩
  rcases generatedByPrimes_to_list hS hs with ⟨qs, hqs, hprime⟩
  have heq : a * listProd qs = p * c := by
    calc
      a * listProd qs = a * s := by rw [hqs]
      _ = s * a := by grind
      _ = p * c := hc
  exact dvd_of_mul_listProd_eq hp
    (fun q hq => havoid q ((hprime q hq).1))
    (fun q hq => (hprime q hq).2) heq

theorem prime_of_localization_prime {α : Type _} [IntegralDomain α] {S : MultSet α}
    (hS : MultSet.GeneratedByPrimes S) {p : α} (hp : Irreducible p) (havoid : Avoids S p)
    (hploc : Prime (Localization.of (S := S) p)) : Prime p := by
  refine ⟨hp.1, hp.2.1, ?_⟩
  intro a b hdiv
  have hlocdiv : dvd (Localization.of (S := S) p)
      (Localization.of (S := S) a * Localization.of (S := S) b) := by
    rcases hdiv with ⟨c, hc⟩
    refine ⟨Localization.of (S := S) c, ?_⟩
    rw [← Localization.of_mul (S := S), hc, Localization.of_mul (S := S)]
  rcases hploc.2.2 (Localization.of (S := S) a) (Localization.of (S := S) b) hlocdiv with hpa | hpb
  · left
    exact dvd_of_localization_dvd hS hp havoid hpa
  · right
    exact dvd_of_localization_dvd hS hp havoid hpb

theorem nagata_key_lemma {α : Type _} [IntegralDomain α] {S : MultSet α}
    (hS : MultSet.GeneratedByPrimes S) (hUFD : UFD (α := Localization S))
    {p : α} (hp : Irreducible p) : Prime p := by
  by_cases hmem : ∃ s : α, S s ∧ dvd p s
  · rcases hmem with ⟨s, hs, hdiv⟩
    exact prime_of_irreducible_of_dvd_generated_primes hS hp hs hdiv
  · have havoid : Avoids S p := by
      intro s hs hdiv
      exact hmem ⟨s, hs, hdiv⟩
    have hlocIrred : Irreducible (Localization.of (S := S) p) :=
      localization_irreducible_of_irreducible hS hp havoid
    have hlocPrime : Prime (Localization.of (S := S) p) := hUFD.2 _ hlocIrred
    exact prime_of_localization_prime hS hp havoid hlocPrime

end NagataFactoriality
