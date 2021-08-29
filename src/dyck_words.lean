import catalan

def balance (l : list (fin 2)) : ℤ := (l.count 1 : ℤ) - (l.count 0)
@[simp] lemma balance_def {l} : balance l = (l.count 1 : ℤ) - (l.count 0) := rfl

@[simp] lemma balance_nil : balance [] = 0 := 
  by rw [balance, list.count_nil, list.count_nil, sub_self]

structure dyck_word :=
  (chars : list (fin 2))
  (total_balance : balance chars = 0)
  (suffix_balance : ∀ t, t <:+ chars → balance t ≥ 0)

lemma list.length_eq_count0_add_count1 (l : list (fin 2)) : l.length = l.count 0 + l.count 1 :=
begin
  induction l with head tail ih, {
    simp only [list.count_nil, list.length],
  }, {
    fin_cases head,
    all_goals {simp [ih, nat.succ_eq_add_one], abel, },
  }
end

namespace dyck_word

lemma even_length (d : dyck_word) : even d.chars.length :=
begin
  use [d.chars.count 0],
  have h₁ := d.total_balance,
  rw [balance] at h₁,
  rw [list.length_eq_count0_add_count1],
  linarith,
end

lemma list.is_suffix_of_append {α} {l a b : list α} (h : l <:+ (a ++ b)) : (∃ k, k <:+ a ∧ k ++ b = l) ∨ (l <:+ b) :=
begin
  simp [←list.mem_tails] at h,
  simp_rw [list.mem_tails] at h,
  cases h, {left, exact h},
  right,
  replace h := list.tail_subset _ h,
  rwa list.mem_tails at h,
end

def append (a b : dyck_word) : dyck_word := {
  chars := a.chars ++ b.chars,
  total_balance := by {
    have h₁ := a.total_balance,
    have h₂ := b.total_balance,
    simp [balance, list.count_append] at *,
    linarith, 
  },
  suffix_balance := by {
    rintro t ht,
    rcases list.is_suffix_of_append ht with ⟨ta, hta, rfl⟩ | ht₂, {
      have h₁ := a.suffix_balance _ hta,
      have h₂ := b.total_balance,
      simp only [int.coe_nat_add, list.count_append, balance_def] at *,
      linarith,
    }, {
      linarith [b.suffix_balance _ ht₂],
    }
  },
}

lemma list.suffix_singleton {α} {a : α} {l} (h : l <:+ [a]) : l = [] ∨ l = [a] :=
begin
  cases l, {left, refl},
  right,
  have h₁ := list.length_le_of_sublist (list.sublist_of_suffix h),
  simp [list.length_eq_zero] at h₁,
  subst h₁,
  apply list.eq_of_sublist_of_length_eq (list.sublist_of_suffix h),
  simp,
end 

def wrap (a : dyck_word) : dyck_word := {
  chars := [0] ++ a.chars ++ [1],
  total_balance := by {
    simpa using a.total_balance,
  }, 
  suffix_balance := by {
    rintro t ht,
    simp at ht,
    rw list.suffix_cons_iff at ht,
    rcases ht with rfl | _, {
      apply ge_of_eq,
      simpa using a.total_balance,
    }, {
      rcases list.is_suffix_of_append ht with ⟨ta, hta, rfl⟩ | ht₂, {
        have h₁ := a.suffix_balance _ hta,
        simp at *,
        linarith,
      }, {
        rcases list.suffix_singleton ht₂ with ⟨rfl, rfl⟩,
        { simp },
        { simp [h] },
      }
    }
  },
}

-- TODO: unique construction through nil, append, wrap -> induction principle on dyck_word

def sized_dyck_word (n : ℕ) := {d : dyck_word // d.chars.length = n}

instance {n} : fintype (sized_dyck_word n) := sorry

theorem catalan_eq_dyck_words_card {n : ℕ} : catalan n = fintype.card (sized_dyck_word (2 * n)) := sorry

end dyck_word