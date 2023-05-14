import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.pos_def
import linear_algebra.matrix.spectrum
import linear_algebra.eigenspace
import ring_theory.trace
import data.complex.basic
import linear_algebra.matrix.charpoly.coeff
import analysis.inner_product_space.pi_L2
.
/-
Some Stuff

-/
variables {m n: Type*}[fintype n][decidable_eq n][fintype m][decidable_eq m]

open matrix
open_locale matrix big_operators

lemma left_mul_inj_of_invertible (P : matrix m m ℂ) [invertible P] :
  function.injective (λ (x : matrix m n ℂ), P ⬝ x) := 
begin
  have hP_uint := is_unit_det_of_invertible P,
  rintros x a hax, 
  replace hax := congr_arg (λ (x : matrix m n ℂ), P⁻¹ ⬝ x) hax,
  dsimp at hax, 
  rw nonsing_inv_mul_cancel_left at hax,
  rw nonsing_inv_mul_cancel_left at hax,
  assumption',
end

lemma eigbasis_inv {A: matrix n n ℂ} {hA: is_hermitian A}:
  hA.eigenvector_matrix_inv.mul hA.eigenvector_matrix = 1 := 
begin
  set α := hA.eigenvector_matrix,
  apply_fun α.mul,
  rw ← matrix.mul_assoc,
  rw matrix.is_hermitian.eigenvector_matrix_mul_inv, 
  rw matrix.one_mul, rw matrix.mul_one,
  apply left_mul_inj_of_invertible,
end

lemma eigsMat {A: matrix n n ℂ} (hA: is_hermitian A):
  A = (hA.eigenvector_matrix) ⬝ (matrix.diagonal (coe ∘ hA.eigenvalues)) ⬝ (hA.eigenvector_matrix_inv) := 
begin
  have hspec := is_hermitian.spectral_theorem hA,
  set α := hA.eigenvector_matrix,

  apply_fun α.mul at hspec,
  rw ← matrix.mul_assoc at hspec,
  rw ← matrix.mul_assoc at hspec,
  rw matrix.is_hermitian.eigenvector_matrix_mul_inv at hspec,
  rw matrix.one_mul at hspec, 
  exact hspec,
end

lemma trace_hermitian_eq_sum_eigenvalues 
  {A: matrix n n ℂ} {hA: is_hermitian A}{hn: nonempty n}:
  trace A = ∑(i: n), hA.eigenvalues i :=
begin
  have h0 := eigsMat hA,
  replace h0 := congr_arg matrix.trace h0,
  rw trace_mul_cycle at h0,
  rw eigbasis_inv at h0,
  rw matrix.one_mul at h0,
  rw h0,
  rw matrix.trace,
  rw matrix.diag_diagonal,
end


