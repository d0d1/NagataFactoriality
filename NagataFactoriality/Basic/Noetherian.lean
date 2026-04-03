import NagataFactoriality.Basic.Divisibility

open Lean.Grind

namespace NagataFactoriality

structure Ideal (α : Type _) [CommRing α] where
  carrier : α → Prop
  zero_mem : carrier 0
  add_mem : ∀ {a b : α}, carrier a → carrier b → carrier (a + b)
  mul_mem : ∀ r : α, ∀ {a : α}, carrier a → carrier (r * a)

namespace Ideal

def Subset {α : Type _} [CommRing α] (I J : Ideal α) : Prop := ∀ ⦃a : α⦄, I.carrier a → J.carrier a

instance {α : Type _} [CommRing α] : LE (Ideal α) := ⟨Subset⟩

theorem le_refl {α : Type _} [CommRing α] (I : Ideal α) : I ≤ I := by
  intro a ha
  exact ha

theorem le_trans {α : Type _} [CommRing α] {I J K : Ideal α} : I ≤ J → J ≤ K → I ≤ K := by
  intro hIJ hJK a ha
  exact hJK (hIJ ha)

def principal {α : Type _} [IntegralDomain α] (a : α) : Ideal α where
  carrier x := dvd a x
  zero_mem := by
    refine ⟨0, ?_⟩
    grind
  add_mem := by
    intro x y hx hy
    rcases hx with ⟨u, hu⟩
    rcases hy with ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    grind
  mul_mem := by
    intro r x hx
    rcases hx with ⟨u, hu⟩
    refine ⟨r * u, ?_⟩
    grind

@[simp] theorem mem_principal {α : Type _} [IntegralDomain α] {a x : α} :
    (principal a).carrier x ↔ dvd a x := Iff.rfl

theorem principal_le_of_dvd {α : Type _} [IntegralDomain α] {a b : α} (h : dvd a b) :
    principal b ≤ principal a := by
  intro x hx
  exact dvd_trans h hx

end Ideal

def AscendingChain {α : Type _} [CommRing α] (c : Nat → Ideal α) : Prop :=
  ∀ n : Nat, c n ≤ c (n + 1)

def Stabilizes {α : Type _} [CommRing α] (c : Nat → Ideal α) : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n → c n = c N

def NoetherianRing (α : Type _) [CommRing α] : Prop :=
  ∀ c : Nat → Ideal α, AscendingChain c → Stabilizes c

def FactorsTo {α : Type _} [IntegralDomain α] (a : α) : Prop :=
  ∃ factors : List α, listProd factors = a ∧ ∀ p : α, p ∈ factors → Irreducible p

theorem factorsTo_irreducible {α : Type _} [IntegralDomain α] {a : α}
    (ha : Irreducible a) : FactorsTo a := by
  refine ⟨[a], ?_, ?_⟩
  · grind [listProd]
  · intro p hp
    simp at hp
    simpa [hp] using ha

theorem factorsTo_mul {α : Type _} [IntegralDomain α] {a b : α}
    (ha : FactorsTo a) (hb : FactorsTo b) : FactorsTo (a * b) := by
  rcases ha with ⟨xs, hxs, hixs⟩
  rcases hb with ⟨ys, hys, hiys⟩
  refine ⟨xs ++ ys, ?_, ?_⟩
  · calc
      listProd (xs ++ ys) = listProd xs * listProd ys := listProd_append xs ys
      _ = a * b := by rw [hxs, hys]
  · intro p hp
    rw [List.mem_append] at hp
    exact hp.elim (hixs p) (hiys p)

def Bad {α : Type _} [IntegralDomain α] (a : α) : Prop :=
  a ≠ 0 ∧ ¬ IsUnit a ∧ ¬ FactorsTo a

theorem bad_not_irreducible {α : Type _} [IntegralDomain α] {a : α} (ha : Bad a) :
    ¬ Irreducible a := by
  intro hairr
  exact ha.2.2 (factorsTo_irreducible hairr)

theorem principal_le_of_eq_mul_left {α : Type _} [IntegralDomain α] {a b c : α}
    (h : a = b * c) : Ideal.principal a ≤ Ideal.principal b := by
  intro x hx
  rcases hx with ⟨u, hu⟩
  refine ⟨c * u, ?_⟩
  calc
    x = a * u := hu
    _ = (b * c) * u := by rw [h]
    _ = b * (c * u) := by grind

theorem principal_le_of_eq_mul_right {α : Type _} [IntegralDomain α] {a b c : α}
    (h : a = b * c) : Ideal.principal a ≤ Ideal.principal c := by
  intro x hx
  rcases hx with ⟨u, hu⟩
  refine ⟨b * u, ?_⟩
  calc
    x = a * u := hu
    _ = (b * c) * u := by rw [h]
    _ = c * (b * u) := by grind

theorem not_principal_le_of_eq_mul_left {α : Type _} [IntegralDomain α] {a b c : α}
    (hb0 : b ≠ 0) (hcnu : ¬ IsUnit c) (h : a = b * c) :
    ¬ Ideal.principal b ≤ Ideal.principal a := by
  intro hle
  have hbmem : (Ideal.principal b).carrier b := dvd_refl b
  have hamem : (Ideal.principal a).carrier b := hle hbmem
  rcases hamem with ⟨d, hd⟩
  have hcancel : b * 1 = b * (c * d) := by
    calc
      b * 1 = b := by grind
      _ = a * d := hd
      _ = (b * c) * d := by rw [h]
      _ = b * (c * d) := by grind
  have hone : 1 = c * d := IntegralDomain.mul_left_cancel₀ hb0 hcancel
  exact hcnu ⟨d, by simpa [Eq.comm] using hone⟩

theorem not_principal_le_of_eq_mul_right {α : Type _} [IntegralDomain α] {a b c : α}
    (hc0 : c ≠ 0) (hbnu : ¬ IsUnit b) (h : a = b * c) :
    ¬ Ideal.principal c ≤ Ideal.principal a := by
  intro hle
  have hcmem : (Ideal.principal c).carrier c := dvd_refl c
  have hamem : (Ideal.principal a).carrier c := hle hcmem
  rcases hamem with ⟨d, hd⟩
  have hcancel : c * 1 = c * (b * d) := by
    calc
      c * 1 = c := by grind
      _ = a * d := hd
      _ = (b * c) * d := by rw [h]
      _ = c * (b * d) := by grind
  have hone : 1 = b * d := IntegralDomain.mul_left_cancel₀ hc0 hcancel
  exact hbnu ⟨d, by simpa [Eq.comm] using hone⟩

theorem bad_has_strict_factor {α : Type _} [IntegralDomain α] {a : α} (ha : Bad a) :
    ∃ b : α, Bad b ∧ Ideal.principal a ≤ Ideal.principal b ∧
      ¬ Ideal.principal b ≤ Ideal.principal a := by
  have hnotirr : ¬ Irreducible a := bad_not_irreducible ha
  have hsplit : ∃ b c : α, a = b * c ∧ ¬ IsUnit b ∧ ¬ IsUnit c := by
    by_cases hex : ∃ b c : α, a = b * c ∧ ¬ IsUnit b ∧ ¬ IsUnit c
    · exact hex
    · exact False.elim <|
        hnotirr <|
          ⟨ha.1, ha.2.1, by
            intro b c hab
            by_cases hb : IsUnit b
            · exact Or.inl hb
            · by_cases hc : IsUnit c
              · exact Or.inr hc
              · exact False.elim (hex ⟨b, c, hab, hb, hc⟩)⟩
  rcases hsplit with ⟨b, c, hab, hbnu, hcnu⟩
  have hb0 : b ≠ 0 := by
    intro hb0
    apply ha.1
    rw [hab, hb0]
    grind
  have hc0 : c ≠ 0 := by
    intro hc0
    apply ha.1
    rw [hab, hc0]
    grind
  by_cases hbfac : FactorsTo b
  · by_cases hcfac : FactorsTo c
    · exact False.elim <|
        ha.2.2 <|
          by
            have habfac : FactorsTo (b * c) := factorsTo_mul hbfac hcfac
            simpa [hab] using habfac
    · refine ⟨c, ⟨hc0, hcnu, hcfac⟩, principal_le_of_eq_mul_right hab, ?_⟩
      exact not_principal_le_of_eq_mul_right hc0 hbnu hab
  · refine ⟨b, ⟨hb0, hbnu, hbfac⟩, principal_le_of_eq_mul_left hab, ?_⟩
    exact not_principal_le_of_eq_mul_left hb0 hcnu hab

abbrev BadPoint (α : Type _) [IntegralDomain α] := {a : α // Bad a}

noncomputable def badStep {α : Type _} [IntegralDomain α] (x : BadPoint α) : BadPoint α :=
  let h := bad_has_strict_factor x.2
  ⟨Classical.choose h, (Classical.choose_spec h).1⟩

theorem badStep_le {α : Type _} [IntegralDomain α] (x : BadPoint α) :
    Ideal.principal x.1 ≤ Ideal.principal (badStep x).1 := by
  dsimp [badStep]
  exact (Classical.choose_spec (bad_has_strict_factor x.2)).2.1

theorem badStep_not_le {α : Type _} [IntegralDomain α] (x : BadPoint α) :
    ¬ Ideal.principal (badStep x).1 ≤ Ideal.principal x.1 := by
  dsimp [badStep]
  exact (Classical.choose_spec (bad_has_strict_factor x.2)).2.2

noncomputable def badSequence {α : Type _} [IntegralDomain α]
    (a0 : BadPoint α) : Nat → BadPoint α
  | 0 => a0
  | n + 1 => badStep (badSequence a0 n)

noncomputable def badIdealChain {α : Type _} [IntegralDomain α] (a0 : BadPoint α) (n : Nat) : Ideal α :=
  Ideal.principal (badSequence a0 n).1

theorem badIdealChain_ascending {α : Type _} [IntegralDomain α] (a0 : BadPoint α) :
    AscendingChain (badIdealChain a0) := by
  intro n
  simpa [badIdealChain, badSequence] using badStep_le (x := badSequence a0 n)

theorem badIdealChain_not_le {α : Type _} [IntegralDomain α] (a0 : BadPoint α) (n : Nat) :
    ¬ badIdealChain a0 (n + 1) ≤ badIdealChain a0 n := by
  simpa [badIdealChain, badSequence] using badStep_not_le (x := badSequence a0 n)

theorem not_bad_of_noetherian {α : Type _} [IntegralDomain α]
    (hNoeth : NoetherianRing α) {a : α} (ha : Bad a) : False := by
  let a0 : BadPoint α := ⟨a, ha⟩
  obtain ⟨N, hstab⟩ := hNoeth (badIdealChain a0) (badIdealChain_ascending a0)
  have hEq : badIdealChain a0 (N + 1) = badIdealChain a0 N := by
    exact hstab (N + 1) (Nat.le_succ N)
  have hle : badIdealChain a0 (N + 1) ≤ badIdealChain a0 N := by
    rw [hEq]
    exact Ideal.le_refl _
  exact badIdealChain_not_le a0 N hle

theorem hasFactorization_of_noetherian {α : Type _} [IntegralDomain α]
    (hNoeth : NoetherianRing α) : HasFactorization (α := α) := by
  intro a ha0 hanu
  by_cases hfac : FactorsTo a
  · exact hfac
  · exact False.elim (not_bad_of_noetherian hNoeth ⟨ha0, hanu, hfac⟩)

theorem NoetherianRing.hasFactorization {α : Type _} [IntegralDomain α]
    (hNoeth : NoetherianRing α) : HasFactorization (α := α) :=
  hasFactorization_of_noetherian hNoeth

end NagataFactoriality
