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

lemma E_pow_eq_cexp {x:ℂ}:
  (E:ℂ)^x = complex.exp(x) := 
begin
  rw [E, complex.cpow_def_of_ne_zero,
    complex.of_real_exp, complex.log_exp],
  simp only [complex.of_real_one, one_mul],

  simp only [complex.of_real_one, complex.one_im, right.neg_neg_iff
  , real.pi_pos],
  simp only [complex.of_real_one, complex.one_im],
  apply le_of_lt, exact real.pi_pos,
  exact real.exp_ne_zero,
  
end
