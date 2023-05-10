import data.real.basic
import data.fin.basic

example {N : ℕ}
  {hN : ne_zero N}
  (k : fin N)
  (hk : ¬k = 0)
  (hklt : ↑k < N)
  (khgt : ↑0 < (↑k:ℕ))
  (hNltz : 0 < N) :
  N  < N + ↑k :=
begin
  simp only [lt_add_iff_pos_right], exact khgt,
end

example {N : ℕ}
  {hN : ne_zero N}
  (k : fin N)
  (hk : ¬k = 0)
  (hklt : ↑k < N)
  (khgt : ↑0 < (↑k:ℕ))
  (hNltz : 0 < N) :
  N  < N + ↑k :=
begin
   have az := (nat.sub_lt_of_pos_le ↑k N khgt) (le_of_lt hklt),
end

#print instances add_comm_group

def x : ℕ := 2
#check x