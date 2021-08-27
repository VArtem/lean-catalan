import catalan

open finset catalan

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
@[simp] lemma all_trees_succ {n : ℕ} : all_trees n.succ = 
  (nat.antidiagonal n).bUnion
    (λ p, finset.image (λ i : Tree × Tree, Branch i.1 i.2) $ finset.product (all_trees p.1) (all_trees p.2)) := 
begin
  -- TODO: extract as bUnion_congr or something
  rw [all_trees],
  ext t, 
  simp only [mem_bUnion, mem_image, dite_eq_ite, exists_prop, nat.mem_antidiagonal, prod.exists, mem_product],
  split,
  {
    rintro ⟨a, b, rfl, h⟩,
    use [a, b, rfl],
    simpa only [mem_image, exists_prop, if_pos rfl, prod.exists, mem_product] using h,
  }, {
    rintro ⟨a, b, rfl, h⟩,
    use [a, b, rfl],
    rw if_pos rfl,
    simpa only [mem_image, exists_prop, prod.exists, mem_product] using h,
  }
end

def mem_all_trees {t : Tree} : t ∈ all_trees t.internal :=
begin
  induction t with a b iha ihb, {
    simp only [internal_Leaf, mem_singleton, all_trees_zero],    
  }, {
    simp only [mem_bUnion, mem_image, exists_prop, internal_Branch, exists_eq_right_right, exists_eq_right, all_trees_succ,
  nat.mem_antidiagonal, prod.exists, mem_product],
    use [a.internal, b.internal, rfl],
    exact ⟨iha, ihb⟩,
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

lemma catalan_eq_all_trees_card {n} : catalan n = (all_trees n).card :=
begin
  apply nat.strong_induction_on n,
  clear n,
  rintro n ih,
  cases n, {
    rw [catalan_zero, all_trees_zero, card_singleton],
  }, {
    simp only [catalan_succ, all_trees_succ],
    rw [card_bUnion], {
      apply sum_congr rfl,
      rintro ⟨a, b⟩ h,
      rw nat.mem_antidiagonal at h,
      rw [card_image_of_injective, card_product],
      {
        rw [ih _ $ nat.lt_succ_of_add_right_eq h],
        rw [ih _ $ nat.lt_succ_of_add_left_eq h],
      }, {
        rintro a b,
        simp only [and_imp],
        exact prod.ext, 
      },
    }, {
      rintro x - y - hneq k hk,
      simp only [mem_image, exists_prop, inf_eq_inter, mem_inter, prod.exists, mem_product] at hk,
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

def TreeN (n : ℕ) := {t : Tree // internal t = n}

instance {n : ℕ} : fintype (TreeN n) :=
  ⟨(all_trees n).subtype (λ t, t.internal = n), 
  begin
    rintro ⟨t, rfl⟩,
    rw mem_subtype,
    exact mem_all_trees,
  end⟩