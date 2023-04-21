import data.complex.basic
import data.complex.exponential
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

