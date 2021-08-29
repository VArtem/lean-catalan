import catalan

open finset catalan

@[derive decidable_eq]
inductive binary_tree
| empty : binary_tree
| branch : binary_tree → binary_tree → binary_tree

namespace binary_tree

def vertices : binary_tree → ℕ
| empty := 0
| (branch l r) := (vertices l) + (vertices r) + 1

@[simp] def vertices_Empty : empty.vertices = 0 := rfl
@[simp] def vertices_Branch (l r : binary_tree) : (branch l r).vertices = l.vertices + r.vertices + 1 := rfl

lemma eq_Empty_of_vertices_zero {t : binary_tree} (h : t.vertices = 0) : t = empty := 
begin
  cases t with l r,
  { refl },
  { rw [vertices_Branch] at h, simpa only using h },
end

lemma eq_Branch_of_vertices_succ {n : ℕ} {t : binary_tree} (h : t.vertices = n.succ) : 
  ∃ l r, t = branch l r := 
begin
  cases t with l r,
  { rw [vertices_Empty] at h, simpa only using h},
  { use [l, r] },
end

def all_trees : Π (n : ℕ), finset binary_tree
| 0 := ({ empty } : finset binary_tree)
| (n + 1) := 
  finset.bUnion (finset.nat.antidiagonal n) $
  λ p, if h : p.1 + p.2 = n then
    let h₁ : p.1 < n + 1 := nat.lt_succ_of_add_right_eq h in
    let h₂ : p.2 < n + 1 := nat.lt_succ_of_add_left_eq h in
      finset.image 
      (λ i : binary_tree × binary_tree, branch i.1 i.2)
      (finset.product (all_trees p.1) (all_trees p.2))
    else ∅


@[simp] lemma all_trees_zero : all_trees 0 = ({ empty } : finset binary_tree) := by rw all_trees
@[simp] lemma all_trees_succ {n : ℕ} : all_trees n.succ = 
  (nat.antidiagonal n).bUnion
    (λ p, finset.image (λ i : binary_tree × binary_tree, branch i.1 i.2) $ finset.product (all_trees p.1) (all_trees p.2)) := 
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

def mem_all_trees {t : binary_tree} : t ∈ all_trees t.vertices :=
begin
  induction t with a b iha ihb, {
    simp only [vertices_Empty, mem_singleton, all_trees_zero],    
  }, {
    simp only [mem_bUnion, mem_image, exists_prop, vertices_Branch, exists_eq_right_right, exists_eq_right, all_trees_succ,
  nat.mem_antidiagonal, prod.exists, mem_product],
    use [a.vertices, b.vertices, rfl],
    exact ⟨iha, ihb⟩,
  }
end

def vertices_eq_of_mem_all_trees {t : binary_tree} {n : ℕ} (h : t ∈ all_trees n) : t.vertices = n :=
begin
  induction t with a b iha ihb generalizing n, {
    cases n, {
      exact vertices_Empty,
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
      simp only [mem_image, exists_prop, if_true, exists_eq_right_right, eq_self_iff_true, exists_eq_right, prod.exists, mem_product] at h,
      rw [←iha h.1, ←ihb h.2],
      exact vertices_Branch _ _,
    }
  }
end
end binary_tree

open binary_tree

lemma all_trees_card_eq_catalan {n} : (all_trees n).card = catalan n :=
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
      rcases branch.inj hc1 with ⟨rfl, rfl⟩,
      apply hneq,
      ext, {
        rw [←vertices_eq_of_mem_all_trees ha1.1, ←vertices_eq_of_mem_all_trees ha2.1],
      }, {
        rw [←vertices_eq_of_mem_all_trees ha1.2, ←vertices_eq_of_mem_all_trees ha2.2],
      },        
    }
  }
end

def sized_binary_tree (n : ℕ) := {t : binary_tree // vertices t = n}
@[simp] lemma sized_binary_tree_def {n : ℕ} : (sized_binary_tree n) = {t : binary_tree // vertices t = n} := rfl

instance {n : ℕ} : fintype (sized_binary_tree n) :=
  ⟨(all_trees n).subtype (λ t, t.vertices = n), 
  begin
    rintro ⟨t, rfl⟩,
    rw mem_subtype,
    exact mem_all_trees,
  end⟩

lemma catalan_eq_TreeN_card {n : ℕ} : fintype.card (sized_binary_tree n) = catalan n :=
begin
  rw [←all_trees_card_eq_catalan],
  apply fintype.card_of_subtype,
  intro x,
  split, {
    exact vertices_eq_of_mem_all_trees,
  }, {
    rintro rfl,
    exact mem_all_trees,
  }
end