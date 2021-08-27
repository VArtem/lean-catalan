import data.finset
import data.finset.nat_antidiagonal
import algebra.big_operators.nat_antidiagonal
import tactic

open_locale big_operators

open finset

@[derive decidable_eq]
inductive Tree
| Leaf : Tree
| Branch : Tree → Tree → Tree

namespace Tree

def internal : Tree → ℕ
| Leaf := 0
| (Branch l r) := (internal l) + (internal r) + 1

@[simp] def internal_Leaf : Leaf.internal = 0 := rfl
@[simp] def internal_Branch (l r : Tree) : (Branch l r).internal = l.internal + r.internal + 1 := rfl

lemma eq_Leaf_of_internal_zero {t : Tree} (h : t.internal = 0) : t = Leaf := 
begin
  cases t with l r,
  { refl },
  { rw [internal_Branch] at h, simpa only using h },
end

lemma eq_Branch_of_internal_succ {n : ℕ} {t : Tree} (h : t.internal = n.succ) : 
  ∃ l r, t = Branch l r := 
begin
  cases t with l r,
  { rw [internal_Leaf] at h, simpa only using h},
  { use [l, r] },
end

-- def TreeN (n : ℕ) := {t : Tree // internal t = n}

-- def combineTrees {n m : ℕ} (l : TreeN n) (r : TreeN m) : 
--   TreeN (n + m).succ := ⟨Branch l.1 r.1, by rw [internal_Branch, l.2, r.2]⟩

lemma nat.lt_succ_of_add_right_eq {a b n : ℕ} (h : a + b = n) : a < n.succ :=
  nat.lt_succ_of_le (h ▸ nat.le_add_right a b)

lemma nat.lt_succ_of_add_left_eq {a b n : ℕ} (h : a + b = n) : b < n.succ :=
  nat.lt_succ_of_le (h ▸ nat.le_add_left b a)

def all_trees : Π (n : ℕ), finset Tree
| 0 := ({ Leaf } : finset Tree)
| (n + 1) := 
  finset.bUnion (finset.nat.antidiagonal n) $
  λ p, if h : p.1 + p.2 = n then
    let h₁ : p.1 < n + 1 := nat.lt_succ_of_add_right_eq h in
    let h₂ : p.2 < n + 1 := nat.lt_succ_of_add_left_eq h in
      finset.image 
      (λ i : Tree × Tree, Branch i.1 i.2)
      (finset.product (all_trees p.1) (all_trees p.2))
    else ∅


@[simp] lemma all_trees_zero : all_trees 0 = ({ Leaf } : finset Tree) := by rw all_trees

lemma lt_add_right_succ (a b : ℕ) : a < (a + b).succ :=
  lt_of_lt_of_le (nat.lt_succ_self _) (nat.succ_le_succ $ nat.le_add_right _ _)

lemma lt_add_left_succ (a b : ℕ) : b < (a + b).succ :=
  lt_of_lt_of_le (nat.lt_succ_self _) (nat.succ_le_succ $ nat.le_add_left _ _)

def mem_all {t : Tree} : t ∈ all_trees t.internal :=
begin
  induction t with a b iha ihb, {
    simp only [all_trees_zero, internal_Leaf, mem_singleton],
  }, {
    rw [internal_Branch, all_trees, mem_bUnion],
    simp only [exists_prop, nat.mem_antidiagonal, prod.exists],
    use [a.internal, b.internal, rfl],
    rw dif_pos rfl,
    simp only [iha, ihb, mem_image, exists_prop, and_true, exists_eq_right_right, exists_eq_right, prod.exists, mem_product],
  }
end

def internal_eq_of_mem_all_trees {t : Tree} {n : ℕ} (h : t ∈ all_trees n) : n = t.internal :=
begin
  induction t with a b iha ihb generalizing n, {
    cases n, {
      exact internal_Leaf,
    }, {
      simp [all_trees] at h,
      rcases h with ⟨a, b, rfl, h⟩, 
      simpa only [if_pos rfl, mem_image, if_true, exists_false] using h,
    }
  }, {
    cases n, {
      simpa using h,
    }, {
      simp [all_trees] at h,
      rcases h with ⟨x, y, rfl, h⟩,
      simp only [if_pos rfl, mem_image, exists_prop, if_true, exists_eq_right_right, exists_eq_right, prod.exists, mem_product] at h,
      rw [iha h.1, ihb h.2],
      exact internal_Branch _ _,
    }
  }
end

end Tree

open Tree

def catalan : ℕ → ℕ
| 0 := 1
| (n + 1) := ∑ p in finset.nat.antidiagonal n, 
  if h : p.1 + p.2 = n then
    let h₁ : p.1 < n + 1 := nat.lt_succ_of_add_right_eq h in
    let h₂ : p.2 < n + 1 := nat.lt_succ_of_add_left_eq h in
    catalan p.1 * catalan p.2
  else 0

lemma catalan_eq_all_trees_card {n} : catalan n = (all_trees n).card :=
begin
  apply nat.strong_induction_on n,
  clear n,
  rintro n ih,
  cases n, {
    rw [catalan, all_trees_zero, card_singleton],
  }, {
    simp only [all_trees, catalan],
    rw [card_bUnion], { 
      congr,  
      ext,
      split_ifs, {
        rw [card_image_of_injective, card_product],
        rw [ih _ $ nat.lt_succ_of_add_right_eq h],
        rw [ih _ $ nat.lt_succ_of_add_left_eq h],
        rintro a b hab,
        simp only at hab,
        exact prod.ext hab.1 hab.2, 
      }, {
        simp only [card_empty],
      }
    }, {
      rintro x hx y hy hneq k hk,
      simp only [dite_eq_ite, inf_eq_inter, mem_inter] at hk,
      rw [nat.mem_antidiagonal] at hx hy,
      
      split_ifs at hk, 
      
      simp only [mem_image, exists_prop, prod.exists, mem_product] at hk,
      rcases hk with ⟨⟨a1, b1, ha1, hc1⟩, ⟨a2, b2, ha2, rfl⟩⟩,
      rcases Branch.inj hc1 with ⟨rfl, rfl⟩,
      apply hneq,
      ext, {
        rw [internal_eq_of_mem_all_trees ha1.1, internal_eq_of_mem_all_trees ha2.1],        
      }, {
        rw [internal_eq_of_mem_all_trees ha1.2, internal_eq_of_mem_all_trees ha2.2],        
      },        
    }
  }
end