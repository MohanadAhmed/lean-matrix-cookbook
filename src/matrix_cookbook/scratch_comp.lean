import data.complex.basic
import data.complex.exponential
import analysis.special_functions.trigonometric.basic
import linear_algebra.matrix.hermitian

open_locale real matrix big_operators complex_conjugate
open matrix
open equiv equiv.perm finset
open complex

example {N : ℕ}
  {hN : ne_zero N}
  (i j : fin N) :
  exp(conj ((-2) * ↑π * I * ↑j * ↑i / ↑N)) =
    exp(2 * ↑π * I * ↑i * ↑j / ↑N) :=
begin
  rw neg_mul, rw neg_mul, rw mul_comm (2*↑π:ℂ), rw ← neg_mul,
  rw mul_assoc, rw mul_assoc, rw mul_div_assoc,
  rw star_ring_end_apply, rw star_mul', rw ← star_ring_end_apply,
  rw conj_neg_I,
  rw exp_eq_exp_iff_exists_int, use 0, 
  simp only [coe_coe, is_R_or_C.star_def, map_div₀, 
  _root_.map_mul, is_R_or_C.conj_bit0, _root_.map_one, is_R_or_C.conj_of_real,
  map_nat_cast, algebra_map.coe_zero, zero_mul, add_zero],
  ring,
end

noncomputable def Wₙ {N: ℕ}: matrix (fin N) (fin N) ℂ :=
λ k n, exp(-2 * π * I * k * n / N)

-- lemma twiddle_sum {N: ℕ}{hN: ne_zero N}(k m n: fin N) :
--   Wₙ k m * Wₙ k n  = Wₙ k (m + n) := 
-- begin
--   rw Wₙ, dsimp, 
--   -- repeat {rw Wkn},
--   have hNz: (↑N:ℂ) ≠ 0, {
--     rw nat.cast_ne_zero, rwa ne_zero_iff at hN, 
--   },
--   rw neg_mul,
--   rw neg_mul,
--   rw neg_mul,
--   rw neg_mul,
--   rw neg_mul,
--   rw neg_mul,
--   rw neg_div,
--   rw neg_div,
--   rw neg_div,
--   rw exp_neg,
--   rw exp_neg,
--   rw exp_neg,
--   rw ← mul_inv, rw inv_eq_iff_eq_inv, rw inv_inv,

--   rw ← exp_add, 
--   rw exp_eq_exp_iff_exists_int,
--   let a:ℤ := ((↑m + ↑n)/N),
--   let w:ℤ := k*a,
--   use w, 
  
--   rw ← add_div, rw ← mul_add (2 * ↑π * I * ↑↑k),
--   set α := (2 * ↑π * I),
--   rw mul_comm _ α, 
--   rw mul_assoc, rw mul_div_assoc,
--   rw mul_assoc α _ _, rw mul_div_assoc α,
--   rw ←  mul_add α,
--   rw mul_right_inj' two_pi_I_ne_zero,
--   rw div_eq_iff hNz, rw add_mul, 
--   rw div_mul_cancel _ hNz ,
--   change w with k*a,
--   rw int.cast_mul, simp only [coe_coe, int.cast_coe_nat],
--   rw ← coe_coe,
--   rw mul_assoc,
--   rw ← mul_add (↑k:ℂ),
--   by_cases hk: (↑k:ℂ) ≠ 0, {
--     -- rw mul_eq_mul_left_iff, left,
--     rw mul_right_inj' hk,
--     norm_cast, rw fin.coe_add,
--     change a with ((↑m + ↑n)/N),
--     simp only [coe_coe, int.cast_coe_nat], norm_cast,
--     rw nat.mod_add_div' (↑m + ↑n) N,
--   }, {
--     simp only [not_not] at hk,
--     rw hk, rw zero_mul, rw zero_mul,
--   },
-- end


lemma dft_idft {N: ℕ} (x: (fin N) → ℂ):
  idft(dft(x)) = x := 
begin
  
end