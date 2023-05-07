import data.complex.basic
import data.complex.exponential
import analysis.special_functions.pow
import analysis.special_functions.complex.log
import analysis.special_functions.trigonometric.basic

open_locale real matrix big_operators
open matrix
open equiv equiv.perm finset
open complex

example {N : ℕ}
  {hE : 2 < N} :
  let α : ℂ := exp ((-2) * ↑π * I / ↑N)
  in α ≠ 0 →
      α ^ (↑N / 2) = exp (log α * (↑N / 2)) → π * 2 < π * ↑N :=
begin
  intros α hα hxy,
  rw   mul_lt_mul_left real.pi_pos,
  norm_cast, exact hE,
end

example {N : ℕ}
  {hE : 2 < N} :
  let α : ℂ := exp ((-2) * ↑π * I / ↑N)
  in α ≠ 0 →
     α ^ (↑N / 2) = exp (log α * (↑N / 2)) → ((-2:ℝ) * π) ≤ (↑N) * π :=
begin
  intros α hα hxy,
  rw mul_le_mul_right real.pi_pos,
  have m20: (-2 ≤ (↑0:ℤ)), by norm_num,
  have m0N: ((↑0:ℤ) ≤ N), by norm_num,
  norm_cast,
  exact le_trans m20 m0N,
end

lemma exp_neg_pi_mul_I:
  complex.exp(-π * I) = -1 := 
begin
  simp only [neg_mul, exp_neg, exp_pi_mul_I],
  norm_num,
end

lemma two_pi_I_by_N_piInt_neg {N : ℕ}
  (h2 : 2 < N) :
  -π < ((2) * ↑π * I / ↑N).im :=
begin
  have : (2) * ↑π * I / ↑N = (((2) * ↑π / ↑N)) * I, by {ring,},
  rw this, rw mul_I_im,

  have : ((2 * ↑π) / ↑N:ℂ).re = ((2 * π) / ↑N) , 
  by {norm_cast,}, rw this,
  have neg_pi_lt_zero: -π < 0, {
    exact neg_lt_zero.2 real.pi_pos,
  },
  set η : ℝ := ↑N,
  have zero_lt_η: 0 < η,{
    change η with ↑N,
    simp only [nat.cast_pos],
    linarith,
  },
  have pi_div_N_lt_zero: 0 < 2*π/η, {
    exact div_pos real.two_pi_pos zero_lt_η,
  },
  rw lt_div_iff zero_lt_η, 
  rw neg_mul, rw mul_comm, rw ← neg_mul, 
  rw mul_lt_mul_right real.pi_pos,
  rw neg_lt_iff_pos_add',
  change η with ↑N,
  exact add_pos zero_lt_η zero_lt_two,
end

lemma two_pi_I_by_N_piInt_pos {N : ℕ}
  (h2 : 2 < N) :
  (2 * ↑π * I / ↑N).im < π :=
begin
  have hNlt0 : 0 < (N:ℝ), by {
    simp only [nat.cast_pos],
    linarith,
  },
  have : (2) * ↑π * I / ↑N = (((2) * ↑π / ↑N)) * I, by {ring,},
  rw this, rw mul_I_im,

  have : ((2 * ↑π) / ↑N:ℂ).re = ((2 * π) / ↑N) , 
  by {norm_cast,}, rw this,

  rw div_lt_iff hNlt0, rw mul_comm, 
  rw mul_lt_mul_left real.pi_pos,
  norm_cast, exact h2,
end

lemma twiddle_half_cycle_eq_neg {N: ℕ} {hN: 2 < N}:
  exp(2 * π * I / N)^((N:ℂ)/(2:ℂ)) = 
  -1 :=
begin
  rw cpow_def_of_ne_zero,
  rw log_exp,
  rw div_mul,
  set η:ℂ := ↑N,
  have hη: η ≠ 0, 
    by {simp only [nat.cast_ne_zero], linarith,},

  rw div_div_cancel' hη, ring_nf,
  rw mul_comm, 
  rw exp_pi_mul_I,
  exact two_pi_I_by_N_piInt_neg hN,
  exact le_of_lt (two_pi_I_by_N_piInt_pos hN),
  exact exp_ne_zero (2 * π * I / N),
end

lemma twiddle_neg_half_cycle_eq_neg' {N: ℕ} {hN: 2 ≤ N}:
  exp(-2 * π * I / N)^((N:ℂ)/(2:ℂ)) = 
  -1 :=
begin
  by_cases h2: (N = 2),
  rw h2, ring_nf,
  have: (1/(2:ℂ)*↑2) = 1, by {
    simp only [one_div, nat.cast_bit0, 
    algebra_map.coe_one,
     inv_mul_cancel_of_invertible],
  },
  rw this, simp only [cpow_one], rw exp_neg,
  rw mul_comm, rw exp_pi_mul_I,
  norm_num,
  rw le_iff_lt_or_eq at hN,
  cases hN with hNlt2 hNeq2,
  rw cpow_def_of_ne_zero,
  rw log_exp,
  rw div_mul,
  set η:ℂ := ↑N,
  have hη: η ≠ 0, 
    by {simp only [nat.cast_ne_zero], linarith,},

  rw div_div_cancel' hη, ring_nf,
  rw mul_comm, rw exp_neg,
  rw exp_pi_mul_I, norm_num,
  rw neg_mul, rw neg_mul, rw neg_div, rw neg_im,
  rw neg_lt_neg_iff,
  exact two_pi_I_by_N_piInt_pos hNlt2,
  
  rw neg_mul, rw neg_mul, rw neg_div, rw neg_im,
  rw neg_le,
  exact (le_of_lt (two_pi_I_by_N_piInt_neg hNlt2)),
  exact exp_ne_zero ((-2) * π * I / N),
  exfalso, exact h2 hNeq2.symm,
end

lemma eq_411 {N: ℕ}{h2: 2 ≤ N} {m: ℤ} : 
  let Wₙ := complex.exp(-2 * π * I  / N) in
  Wₙ ^ (m + N/2: ℂ)  = -Wₙ ^ (m:ℂ)  := 
begin
  dsimp only,
  set α := exp(- 2 * π * I / N),
  rw complex.cpow_add,
  simp only [cpow_int_cast],
  rw ← neg_one_mul, rw mul_comm,
  rw mul_left_inj',
  apply twiddle_neg_half_cycle_eq_neg',
  exact h2,
  rw ← exp_int_mul, ring_nf,
  exact exp_ne_zero (-(2 * (↑N)⁻¹ * I * ↑π * ↑m)),
  exact exp_ne_zero (- 2 * π * I / N),
end

lemma eq_411_m_real {N: ℕ}{h2: 2 ≤ N} {m: ℂ} : 
  let Wₙ := complex.exp(-2 * π * I  / N) in
  Wₙ ^ (m + N/2: ℂ)  = -Wₙ ^ (m:ℂ)  := 
begin
  dsimp only,
  set α := exp(- 2 * π * I / N),
  have hα: α ≠ 0, by exact exp_ne_zero ((-2) * ↑π * I / ↑N),
  
  rw complex.cpow_add,
  rw ← neg_one_mul, rw mul_comm,
  rw mul_left_inj',
  apply twiddle_neg_half_cycle_eq_neg',
  exact h2,
  rw cpow_def_of_ne_zero,
  apply exp_ne_zero _,
  assumption',
end

lemma eq_411_ints {N: ℕ}{h2: 2 ≤ N} {m: ℤ} : 
  let Wₙ := complex.exp(-2 * π * I  / N) in
  Wₙ ^ (m + N/2: ℂ)  = -Wₙ ^ (m:ℂ)  := 
begin
  apply eq_411_m_real, exact h2,
end

-- lemma eq_411_one {N: ℕ}{h2: 1 = N} {m: ℤ} : 
--   let Wₙ := complex.exp(-2 * π * I  / N) in
--   Wₙ ^ (m + N/2: ℂ)  = -Wₙ ^ (m:ℂ)  := 
-- begin
--   dsimp,
--   set α := exp(- 2 * π * I / N),
--   have hα: α ≠ 0, by exact exp_ne_zero ((-2) * ↑π * I / ↑N),
--   rw complex.cpow_add,
--   rw ← neg_one_mul, rw mul_comm,
--   rw mul_left_inj',
--   rw ← h2 at *, 
--   -- change α with 
--   rw cpow_def_of_ne_zero,
--   change α with exp(- 2 * π * I / ↑N), rw ← h2 at *, 
--   simp only [neg_mul, algebra_map.coe_one, div_one, one_div],
--   rw ← cpow_def_of_ne_zero, rw exp_neg, rw exp_two_pi_mul_I,
--   -- ring_nf,
  
-- end

