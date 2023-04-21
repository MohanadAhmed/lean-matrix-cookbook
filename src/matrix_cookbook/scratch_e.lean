import data.complex.basic
import data.complex.exponential
import data.real.basic
import analysis.special_functions.pow
import analysis.special_functions.trigonometric.basic
import analysis.special_functions.trigonometric.bounds
import data.complex.exponential_bounds
import data.real.pi.bounds

open_locale real

noncomputable def E : ℝ := real.exp(1)

lemma E_lt_3: 
  E < (3 :ℝ) := 
begin
  have h1 : E < (13591409143 / 5000000000), 
    by {rw E, exact real.exp_one_lt_d9,},
  have h2 : (13591409143 / 5000000000) < (3:ℝ), by norm_num,
  set α : ℝ  := (13591409143 / 5000000000),
  exact lt_trans' h2 h1,
end

lemma E_lt_pi :
  E < (π) := begin
  exact lt_trans E_lt_3 real.pi_gt_three,
end

lemma zero_lt_E :
  0 < E := begin
    rw E, exact real.exp_pos 1,
end

lemma zero_ne_E :
  0 ≠ E := begin
  rw E, exact (real.exp_ne_zero 1).symm,
end

lemma E_ne_zero :
  E ≠ 0 := begin
  rw E, exact (real.exp_ne_zero 1),
end

lemma E_ne_zero' : (↑E:ℂ) ≠ 0 :=
begin
  rw E, rw complex.of_real_exp,
  exact complex.exp_ne_zero 1,
end

lemma neg_pi_lt_E :
  -π < E := begin
  have neg_pi_lt_zero : -π < 0, 
    by {rw [neg_lt, neg_zero], exact real.pi_pos,},
  exact lt_trans neg_pi_lt_zero zero_lt_E,
end

lemma E_le_pi : E ≤ π := by exact le_of_lt (E_lt_pi)

lemma E_pow_eq_exp {x:ℝ}:
  E^x = real.exp(x) := 
begin
  rw E, rw real.exp_one_rpow,
end

lemma one_in_piInt_neg : -π < (1:ℂ).im :=
begin
  rw [complex.one_im, right.neg_neg_iff],
  exact real.pi_pos,
end

lemma one_in_piInt_pos : (1:ℂ).im ≤ π :=
begin
  rw [complex.one_im],
  exact le_of_lt real.pi_pos,
end


lemma E_pow_eq_cexp {x:ℂ}:
  (E:ℂ)^x = complex.exp(x) := 
begin
  rw [E, complex.cpow_def_of_ne_zero,
    complex.of_real_exp, complex.log_exp],
  simp only [complex.of_real_one, one_mul],
  exact one_in_piInt_neg,
  exact one_in_piInt_pos,
  exact E_ne_zero',
end

lemma E_pow_mul_comm {x y : ℂ} 
  {h1: -π < x.im} {h2: x.im ≤ π}:
    (E:ℂ)^(x*y) = ((E:ℂ)^x)^y :=
begin
  rw complex.cpow_def_of_ne_zero,
  rw complex.cpow_def_of_ne_zero,
  rw E_pow_eq_cexp,
  rw E, rw complex.of_real_exp,
  rw complex.log_exp h1 h2,
  rw complex.log_exp,
  simp only [complex.of_real_one, one_mul],
  exact one_in_piInt_neg,
  exact one_in_piInt_pos,
  rw E_pow_eq_cexp, exact complex.exp_ne_zero x,
  exact E_ne_zero',
end
