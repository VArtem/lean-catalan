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
  refl,
  rw [internal_Branch] at h,
  simpa only using h,
end

lemma eq_Branch_of_internal_succ {n : ℕ} {t : Tree} (h : t.internal = n.succ) : 
  ∃ l r, t = Branch l r := 
begin
  cases t with l r,
  { rw [internal_Leaf] at h, simpa only using h},
  { use [l, r] },
end


def TreeN (n : ℕ) := {t : Tree // internal t = n}

def combineTrees {n m : ℕ} (l : TreeN n) (r : TreeN m) : 
  TreeN (n + m).succ := ⟨Branch l.1 r.1, by rw [internal_Branch, l.2, r.2]⟩

def all : Π (n : ℕ), finset (TreeN n)
| 0 := { ⟨Leaf, internal_Leaf⟩ }
| (n + 1) := 
  finset.bUnion (finset.nat.antidiagonal n) $
  λ i, if h : i.1 < n.succ ∧ i.2 < n.succ ∧ i.1 + i.2 = n then
    let h₁ := and.left h in
    let h₂ := and.left (and.right h) in
    let h₃ := and.right (and.right h) in
      finset.image 
      (λ p : TreeN i.1 × TreeN i.2, 
        ⟨Branch p.1.val p.2.val, 
        by {rw [internal_Branch, p.fst.property, p.snd.property, h₃]}⟩)
      (finset.product (all i.1) (all i.2))
    else ∅

instance {n : ℕ} : fintype (TreeN n) :=
  ⟨all n, 
  begin
    apply nat.strong_induction_on n,
    clear n,
    rintro n ih ⟨t, h⟩,
    cases n, {
      rw [all, mem_singleton, subtype.mk_eq_mk],
      exact eq_Leaf_of_internal_zero h,
    }, {
      rcases eq_Branch_of_internal_succ h with ⟨a, b, rfl⟩,
      rw [internal, nat.add_one, nat.succ_inj'] at h,
      subst h,
      
      have a_lt : a.internal < (a.internal + b.internal).succ := 
        lt_of_lt_of_le (nat.lt_succ_self _) (nat.succ_le_succ $ nat.le_add_right _ _),

      have b_lt : b.internal < (a.internal + b.internal).succ := 
        lt_of_lt_of_le (nat.lt_succ_self _) (nat.succ_le_succ $ nat.le_add_left _ _),

      simp only [all, mem_bUnion, exists_prop, nat.mem_antidiagonal, subtype.val_eq_coe, prod.exists],
      use [a.internal, b.internal, rfl],
      rw dif_pos,
      {
        simp only [mem_image, exists_prop, prod.exists, mem_product],
        use [a, b],
        refine ⟨⟨ih _ a_lt ⟨a, _⟩, ih _ b_lt ⟨b, _⟩⟩, rfl⟩,
        use [a_lt, b_lt],
      },
    }
  end⟩

end Tree

open Tree

def catalan : ℕ → ℕ
| 0 := 1
| (n + 1) := ∑ p in finset.nat.antidiagonal n, 
  if h : p.1 < n.succ ∧ p.2 < n.succ ∧ p.1 + p.2 = n then
    let h₁ := and.left h in 
    let h₂ := and.left (and.right h) in
    let h₃ := and.right (and.right h) in
    catalan p.1 * catalan p.2
  else 0

lemma catalan_eq_TreeN_card {n} : catalan n = (all n).card :=
begin
  apply nat.strong_induction_on n,
  rintro n ih,
  cases n, {
    simp only [catalan, univ, fintype.elems, all, card_singleton],
  }, {
    simp only [all, catalan, eq_mpr_eq_cast],
    rw [card_bUnion], { 
      congr',
      ext,
      split_ifs, {
        rw [card_image_of_injective, card_product, ih _ h.1, ih _ h.2.1],
        rintro a b h2,
        simp only [subtype.mk_eq_mk, subtype.val_eq_coe] at h2,
        rw [prod.ext_iff, subtype.ext_iff, subtype.ext_iff],
        exact ⟨h2.1, h2.2⟩,
      }, {
        simp only [card_empty],
      }
    }, {
      rintro x hx y hy hneq k hk,
      simp at hk,
      rw [nat.mem_antidiagonal] at hx hy,
      split_ifs at hk, {
        simp only [mem_image, exists_prop, prod.exists, mem_product] at hk,
        rcases hk with ⟨⟨a1, b1, ha1, hc1⟩, ⟨a2, b2, ha2, hc2⟩⟩,
        rcases k with ⟨(_ | ⟨kleft, kright⟩), kint⟩,
        { simpa only using kint, },
        simp only [subtype.mk_eq_mk] at hc1 hc2,
        rcases hc2 with ⟨rfl, rfl⟩,
        apply hneq,
        repeat {rw ←subtype.val_eq_coe at hc1},
        rw prod.eq_iff_fst_eq_snd_eq,
        rw [←a1.property, ←a2.property, ←b1.property, ←b2.property],
        rw [hc1.1, hc1.2],
        exact ⟨rfl, rfl⟩,
      }, 
      all_goals { simpa using hk },
    }
  }
end