import data.finset.basic
import data.finset.nat_antidiagonal
import tactic

open_locale big_operators

open finset

-- some convenient `nat` lemmas
lemma nat.lt_succ_of_add_right_eq {a b n : ℕ} (h : a + b = n) : a < n.succ :=
  nat.lt_succ_of_le (h ▸ nat.le_add_right a b)

lemma nat.lt_succ_of_add_left_eq {a b n : ℕ} (h : a + b = n) : b < n.succ :=
  nat.lt_succ_of_le (h ▸ nat.le_add_left b a)

def catalan : ℕ → ℕ
| 0 := 1
| (n + 1) := ∑ p in finset.nat.antidiagonal n, 
  if h : p.1 + p.2 = n then
    let h₁ : p.1 < n + 1 := nat.lt_succ_of_add_right_eq h in
    let h₂ : p.2 < n + 1 := nat.lt_succ_of_add_left_eq h in
    catalan p.1 * catalan p.2
  else 0

namespace catalan

@[simp] lemma catalan_zero : catalan 0 = 1 := by rw catalan
@[simp] lemma catalan_succ {n : ℕ} : catalan n.succ = ∑ p in finset.nat.antidiagonal n, 
  catalan p.1 * catalan p.2 := 
begin
  rw [catalan, sum_congr rfl],
  simp_rw nat.mem_antidiagonal,
  rintro ⟨x, y⟩ rfl,
  simp only [dif_pos rfl],
end

-- TODO: catalan n = C(2n, n) - C(2n, n - 1) = C(2n, n) / (n + 1)

end catalan
