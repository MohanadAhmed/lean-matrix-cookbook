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

lemma real_in_piInt_neg {a:ℝ}: -π < (a:ℂ).im :=
begin
  rw [complex.of_real_im, right.neg_neg_iff],
  exact real.pi_pos,
end

lemma real_in_piInt_pos {a:ℝ} : (a:ℂ).im ≤ π :=
begin
  rw [complex.of_real_im],
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

section try
open complex
lemma two_pi_I_by_N_piInt_neg {N : ℕ}
  (h2 : 2 < N) :
  -π < ((-2) * ↑π * I / ↑N).im :=
begin
  have : (-2) * ↑π * I / ↑N = (((-2) * ↑π / ↑N)) * I, by {ring,},
  rw this, rw mul_I_im, rw neg_mul, 
  have : (-(2 * ↑π) / ↑N:ℂ).re = (-(2 * π) / ↑N) , 
  by {norm_cast,},
  
  rw this, rw lt_div_iff', rw mul_neg, rw neg_lt_neg_iff,  
  rw mul_lt_mul_right real.pi_pos, 
  exact_mod_cast h2,  
  norm_cast, 
  exact lt_trans zero_lt_two h2,  
end

lemma two_pi_I_by_N_piInt_pos {N : ℕ}
  (h2 : 2 < N) :
  ((-2) * ↑π * I / ↑N).im ≤ π :=
begin
  have hNlt0 : 0 < (N:ℝ), by {
    apply lt_trans (zero_lt_two' ℝ) _,
    exact_mod_cast h2, 
  },
  have : (-2) * ↑π * I / ↑N = (((-2) * ↑π / ↑N)) * I, by {ring,},
  rw this, rw mul_I_im, rw neg_mul, 
  have : (-(2 * ↑π) / ↑N:ℂ).re = (-(2 * π) / ↑N) , 
  by {norm_cast,},
  
  rw this,  rw div_le_iff',
  rw ← neg_mul,  rw mul_le_mul_right real.pi_pos, 

  have hm2 := le_of_lt (neg_lt_zero.2 (zero_lt_two' ℝ)),
  have hm0 := le_of_lt hNlt0,
  apply le_trans hm2 (le_of_lt hNlt0),
  exact hNlt0,
end

lemma cexp_pow {a b: ℝ} {ha: a ≠ 0}
  {h1: -π < a} {h2: a ≤ π}:
  exp(a*I)^(b:ℂ) = exp(a*b*I) := 
begin
  rw [← E_pow_eq_cexp, ← E_pow_mul_comm, E_pow_eq_cexp],
  ring_nf,
  rw [complex.mul_I_im, of_real_re], exact h1,
  rw [complex.mul_I_im, of_real_re], exact h2,
end

lemma complex_exp_neg_one {N: ℕ} {hE: 2 ≤ N}: 
  exp (-2 * π * I / ↑N) ^ ((N:ℂ) / 2) = -1 := 
begin
  have hNne0 : N ≠ 0, by linarith,

  by_cases h: (N = 2), rw h,
  have ha : -(2 * ↑π * I) / 2 = -π*I, by ring,
  
  simp only [neg_mul, nat.cast_bit0, 
    algebra_map.coe_one, div_self_of_invertible, 
    cpow_one],
  rw [ha, neg_mul, exp_neg, exp_pi_mul_I], ring,
  
  -- ¬(N = 2)
  rw ← ne.def at h,
  have h2 : 2 < N, by exact lt_of_le_of_ne hE (h.symm),

  rw [← E_pow_eq_cexp],
  rw ← E_pow_mul_comm, 
  rw E_pow_eq_cexp, 
  have ha : ((-2) * ↑π * I) / ↑N * (↑N / 2) = -π*I, by {
    ring_nf, rw mul_inv_cancel, simp only [one_mul],
    norm_cast, exact hNne0,
  },
  rw [ha,neg_mul, exp_neg, exp_pi_mul_I], ring,  
  exact two_pi_I_by_N_piInt_neg h2,
  exact two_pi_I_by_N_piInt_pos h2,
end

end try