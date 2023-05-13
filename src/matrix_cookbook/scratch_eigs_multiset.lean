import algebra.char_zero.infinite
import data.polynomial.algebra_map
import data.polynomial.degree.lemmas
import data.polynomial.div
import ring_theory.localization.fraction_ring
import algebra.polynomial.big_operators

noncomputable theory
open_locale classical polynomial
open finset
open multiset

universes u v w z
variables {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variables [comm_ring R] [is_domain R] {p q : R[X]}


lemma exists_multiset_roots : ∀ {p : R[X]} (hp : p ≠ 0),
  ∃ s : multiset R, (s.card : with_bot ℕ) ≤ polynomial.degree p ∧ 
    ∀ a, s.count a = polynomial.root_multiplicity a p
| p := begin

end

open classical 

lemma exists_multiset_roots_withCount : ∀ {p : R[X]} (hp : p ≠ 0),
  ∃ s : multiset R, (s.card : with_bot ℕ) = polynomial.degree p ∧ 
    ∀ a, s.count a = polynomial.root_multiplicity a p
| p := begin
  intro hp,


end

/-λ hp, by haveI := classical.prop_decidable (∃ x, is_root p x); exact
if h : ∃ x, is_root p x
then
  let ⟨x, hx⟩ := h in
  have hpd : 0 < degree p := degree_pos_of_root hp hx,
  have hd0 : p /ₘ (X - C x) ≠ 0 :=
    λ h, by rw [← mul_div_by_monic_eq_iff_is_root.2 hx, h, mul_zero] at hp; exact hp rfl,
  have wf : degree (p /ₘ _) < degree p :=
    degree_div_by_monic_lt _ (monic_X_sub_C x) hp
    ((degree_X_sub_C x).symm ▸ dec_trivial),
  let ⟨t, htd, htr⟩ := @exists_multiset_roots (p /ₘ (X - C x)) hd0 in
  have hdeg : degree (X - C x) ≤ degree p := begin
    rw [degree_X_sub_C, degree_eq_nat_degree hp],
    rw degree_eq_nat_degree hp at hpd,
    exact with_bot.coe_le_coe.2 (with_bot.coe_lt_coe.1 hpd)
  end,
  have hdiv0 : p /ₘ (X - C x) ≠ 0 := mt (div_by_monic_eq_zero_iff (monic_X_sub_C x)).1 $
    not_lt.2 hdeg,
  ⟨x ::ₘ t, calc (card (x ::ₘ t) : with_bot ℕ) = t.card + 1 :
      by exact_mod_cast card_cons _ _
    ... ≤ degree p :
      by rw [← degree_add_div_by_monic (monic_X_sub_C x) hdeg,
          degree_X_sub_C, add_comm];
        exact add_le_add (le_refl (1 : with_bot ℕ)) htd,
  begin
    assume a,
    conv_rhs { rw ← mul_div_by_monic_eq_iff_is_root.mpr hx },
    rw [root_multiplicity_mul (mul_ne_zero (X_sub_C_ne_zero x) hdiv0),
        root_multiplicity_X_sub_C, ← htr a],
    split_ifs with ha,
    { rw [ha, count_cons_self, nat.succ_eq_add_one, add_comm] },
    { rw [count_cons_of_ne ha, zero_add] },
  end⟩
else
  ⟨0, (degree_eq_nat_degree hp).symm ▸ with_bot.coe_le_coe.2 (nat.zero_le _),
    by { intro a, rw [count_zero, root_multiplicity_eq_zero (not_exists.mp h a)] }⟩
using_well_founded {dec_tac := tactic.assumption} -/