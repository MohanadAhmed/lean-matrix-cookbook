import linear_algebra.matrix.bilinear_form
import linear_algebra.matrix.charpoly.minpoly
import linear_algebra.determinant
import linear_algebra.finite_dimensional
import linear_algebra.vandermonde
import linear_algebra.trace
import field_theory.is_alg_closed.algebraic_closure
import field_theory.primitive_element
import field_theory.galois
import ring_theory.power_basis
import ring_theory.trace

universes u v w z

variables {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
variables [algebra R S] [algebra R T]
variables {K L : Type*} [field K] [field L] [algebra K L]
variables {ι κ : Type w} [fintype ι]

open finite_dimensional
open linear_map
open matrix

open_locale big_operators
open_locale matrix


variables (b : basis ι R S)

variables (R S)


open algebra polynomial
variables {K}
variables {F : Type*} [field F]
variables [algebra K S] [algebra K F]

lemma trace_eq_sum_roots''' [finite_dimensional K L]
  {x : L} (hF : (minpoly K x).splits (algebra_map K F)) :
  algebra_map K F (algebra.trace K L x) =
    finrank K⟮x⟯ L • ((minpoly K x).map (algebra_map K _)).roots.sum :=
begin
  rw trace_eq_trace_adjoin K x,
  rw algebra.smul_def,
  rw ring_hom.map_mul, 
  rw ← algebra.smul_def,
  rw intermediate_field.adjoin_simple.trace_gen_eq_sum_roots _ hF, 
  rw is_scalar_tower.algebra_map_smul,
end

