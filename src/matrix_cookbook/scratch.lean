import data.complex.basic
import linear_algebra.matrix.hermitian
import linear_algebra.matrix.symmetric
import linear_algebra.matrix.nonsingular_inverse
import data.complex.exponential
import analysis.special_functions.trigonometric.basic
import data.matrix.basic

open_locale real matrix big_operators
open matrix
open equiv equiv.perm finset
open complex
open polynomial

lemma one_lt_N_zero_ne {N: ℕ} (hN: 1 < N) : (↑N:ℂ) ≠ (0:ℂ) := begin
  simp only [ne.def, nat.cast_eq_zero], 
  -- linarith,
  sorry,
end

lemma complex_exp_neg_one {N: ℕ} {hE: 2 < N}: 
  exp (-2 * π * I / ↑N) ^ ((↑N: ℂ) / 2) = -1 := 
begin
  set α := exp(- 2 * π * I / N),
  have hN : 1 < N, by {linarith,},
  have m0N: ((↑0:ℤ) ≤ ↑N), by norm_num,
  have hα : α ≠ 0, by {apply exp_ne_zero,}, 
  have hxy := cpow_def_of_ne_zero (hα) (N/2: ℂ),
  have hi : (-2) * ↑π * I / ↑N = (-2*π/N)*I, by {ring,},
  rw hxy,
  change α with exp(- 2 * π * I / N),
  rw log_exp,
  have : ((-2) * ↑π * I / ↑N * (↑N / 2)) = -(2*π*I)/2, by {
    rw neg_mul, rw neg_mul,
    ring_nf, rw mul_inv_cancel (one_lt_N_zero_ne hN), rw one_mul,
    -- sorry,
  },
  rw this, 
  have : -(2 * ↑π * I) / 2 = -↑π * I, by { ring,}, rw this,
  rw [neg_mul, exp_neg, exp_pi_mul_I], sorry,
  
  rw hi, rw complex.mul_I_im, 
  norm_cast, rw lt_div_iff, 
  simp only [neg_mul, int.cast_neg, int.cast_bit0, algebra_map.coe_one, neg_lt_neg_iff], 
  
  
  rw mul_comm,  rw   mul_lt_mul_left real.pi_pos,
  norm_cast, exact hE, simp only [nat.cast_pos], linarith only [hE],
  
  rw hi, rw complex.mul_I_im, 
  norm_cast, rw div_le_iff',
  rw mul_le_mul_right real.pi_pos,
  have m20: (-2 ≤ (↑0:ℤ)), by norm_num,
  norm_cast,
  exact le_trans m20 m0N, norm_cast, linarith,
end


-- lemma complex_exp_ne_one_if_kn {N:ℕ} {hN: 1 < N} 
--     {k n: fin N} {h: ¬(k = n)} :
--   exp (I * 2 * ↑π * (↑k - ↑n) / ↑N) ≠ 1 :=
-- begin
--   by_contra' hE,
--   rw complex.exp_eq_one_iff at hE,
--   cases hE with m hE,

--   have hm1 : I * 2 * ↑π * (↑k - ↑n) / ↑N = (2 * ↑π * I) * ((↑k - ↑n) / ↑N), by ring,
--   have hm2 : ↑m * (2 * ↑π * I) = (2 * ↑π * I) * m, by ring,
  
--   rw [hm1, hm2, mul_right_inj' two_pi_I_ne_zero] at hE, 
--   rw div_eq_iff at hE,
  
--   sorry,
--   exact one_lt_N_zero_ne hN,
-- end
