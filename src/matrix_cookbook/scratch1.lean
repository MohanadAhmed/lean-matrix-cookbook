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
  (h2 : 2 ≤ N) :
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
  (h2 : 2 ≤ N) :
  (2 * ↑π * I / ↑N).im ≤ π :=
begin
  have hNlt0 : 0 < (N:ℝ), by {
    simp only [nat.cast_pos],
    linarith,
  },
  have : (2) * ↑π * I / ↑N = (((2) * ↑π / ↑N)) * I, by {ring,},
  rw this, rw mul_I_im,

  have : ((2 * ↑π) / ↑N:ℂ).re = ((2 * π) / ↑N) , 
  by {norm_cast,}, rw this,

  rw div_le_iff hNlt0, rw mul_comm, 
  rw mul_le_mul_left real.pi_pos,
  norm_cast, exact h2,
end

lemma twiddle_half_cycle_eq_neg {N: ℕ} {hN: 2 ≤ N}:
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
  exact two_pi_I_by_N_piInt_pos hN,
  exact exp_ne_zero (2 * π * I / N),
end
