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

